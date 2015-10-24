use std::io::Write;
use std::mem::{size_of, uninitialized};
use std::ptr::null_mut;

use libc::{c_void, size_t};
use libc::funcs::c95::stdlib::{free, malloc};

use deflate::calculate_block_size;
use hash::{update_hash, warmup_hash, Hash};
use lz77::{clean_lz77_store, copy_lz77_store, find_longest_match, lz77_greedy, store_litlen_dist, verify_len_dist, BlockState, LZ77Store};
use tree::calculate_entropy;
use util::{get_dist_extra_bits, get_dist_symbol, get_length_extra_bits, get_length_symbol, LARGE_FLOAT, MAX_MATCH, MIN_MATCH, WINDOW_SIZE};

struct SymbolStats {
    /// The literal and length symbols.
    litlens: [usize; 288],
    /// The 32 unique dist symbols, not the 32768 possible dists.
    dists: [usize; 32],

    /// Length of each lit/len symbol in bits.
    ll_symbols: [f64; 288],
    /// Length of each dist symbol in bits.
    d_symbols: [f64; 32],
}

impl SymbolStats {
    fn new() -> SymbolStats {
        SymbolStats {
            litlens: [0usize; 288],
            dists: [0usize; 32],
            ll_symbols: [0f64; 288],
            d_symbols: [0f64; 32],
        }
    }
}

unsafe fn copy_stats(source: *const SymbolStats, dest: *mut SymbolStats) {
    (*dest).litlens = (*source).litlens;
    (*dest).dists = (*source).dists;
    (*dest).ll_symbols = (*source).ll_symbols;
    (*dest).d_symbols = (*source).d_symbols;
}

/// Adds the bit lengths.
unsafe fn add_weighed_stat_freqs(stats1: *const SymbolStats, w1: f64, stats2: *const SymbolStats, w2: f64, result: *mut SymbolStats) {
    for i in 0..288 {
        (*result).litlens[i] = ((*stats1).litlens[i] as f64 * w1 + (*stats2).litlens[i] as f64 * w2) as usize;
    }
    for i in 0..32 {
        (*result).dists[i] = ((*stats1).dists[i] as f64 * w1 + (*stats2).dists[i] as f64 * w2) as usize;
    }
    (*result).litlens[256] = 1; // End symbol.
}

struct RanState {
    m_w: u32,
    m_z: u32,
}

impl RanState {
    fn new() -> RanState {
        RanState {
            m_w: 1,
            m_z: 2,
        }
    }
}

/// Get random number: "Multiply-With-Carry" generator of G. Marsaglia
unsafe fn ran(state: *mut RanState) -> u32 {
    (*state).m_z = 36969 * ((*state).m_z & 65535) + ((*state).m_z >> 16);
    (*state).m_w = 18000 * ((*state).m_w & 65535) + ((*state).m_w >> 16);
    return ((*state).m_z << 16).wrapping_add((*state).m_w);  // 32-bit result.
}

unsafe fn randomize_freqs(state: *mut RanState, freqs: *mut usize, n: i32) {
    for i in 0..n {
        if (ran(state) >> 4) % 3 == 0 {
            *freqs.offset(i as isize) = *freqs.offset((ran(state) % n as u32) as isize);
        }
    }
}

unsafe fn randomize_stat_freqs(state: *mut RanState, stats: *mut SymbolStats) {
    randomize_freqs(state, (*stats).litlens.as_mut_ptr(), 288);
    randomize_freqs(state, (*stats).dists.as_mut_ptr(), 32);
    (*stats).litlens[256] = 1; // End symbol.
}

unsafe fn clear_stat_freqs(stats: *mut SymbolStats) {
    for i in 0..288 {
        (*stats).litlens[i] = 0;
    }
    for i in 0..32 {
        (*stats).dists[i] = 0;
    }
}

/// Function that calculates a cost based on a model for the given LZ77 symbol.
/// litlen: means literal symbol if dist is 0, length otherwise.
type CostModelFun = unsafe fn (litlen: u32, dist: u32, context: *const c_void) -> f64;

/// Cost model which should exactly match fixed tree.
/// type: CostModelFun
unsafe fn get_cost_fixed(litlen: u32, dist: u32, _unused: *const c_void) -> f64 {
    if dist == 0 {
        if litlen <= 143 {
            8f64
        } else {
            9f64
        }
    } else {
        let dbits: i32 = get_dist_extra_bits(dist as i32);
        let lbits: i32 = get_length_extra_bits(litlen as i32);
        let lsym: i32 = get_length_symbol(litlen as i32);
        let mut cost: f64 = 0f64;
        if lsym <= 279 {
            cost += 7f64;
        } else {
            cost += 8f64;
        }
        cost += 5f64; // Every dist symbol has length 5.
        cost + dbits as f64 + lbits as f64
    }
}

/// Cost model based on symbol statistics.
/// type: CostModelFun
unsafe fn get_cost_stat(litlen: u32, dist: u32, context: *const c_void) -> f64 {
    let stats: *const SymbolStats = context as *const SymbolStats;
    if dist == 0 {
        (*stats).ll_symbols[litlen as usize]
    } else {
        let lsym: i32 = get_length_symbol(litlen as i32);
        let lbits: i32 = get_length_extra_bits(litlen as i32);
        let dsym: i32 = get_dist_symbol(dist as i32);
        let dbits: i32 = get_dist_extra_bits(dist as i32);
        (*stats).ll_symbols[lsym as usize] + lbits as f64 + (*stats).d_symbols[dsym as usize] + dbits as f64
    }
}

/// Finds the minimum possible cost this cost model can return for valid length and
/// distance symbols.
unsafe fn get_cost_model_min_cost(costmodel: CostModelFun, costcontext: *const c_void) -> f64 {
    let mut bestlength: i32 = 0; // length that has lowest cost in the cost model
    let mut bestdist: i32 = 0; // distance that has lowest cost in the cost model

    // Table of distances that have a different distance symbol in the deflate
    // specification. Each value is the first distance that has a new symbol. Only
    // different symbols affect the cost model so only these need to be checked.
    // See RFC 1951 section 3.2.5. Compressed blocks (length and distance codes).
    const DSYMBOLS: [i32; 30] = [
        1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513,
        769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577];

    let mut mincost: f64 = LARGE_FLOAT;
    for i in 3..259 {
        let c: f64 = costmodel(i, 1, costcontext);
        if c < mincost {
            bestlength = i as i32;
            mincost = c;
        }
    }

    let mut mincost: f64 = LARGE_FLOAT;
    for i in 0..30 {
        let c: f64 = costmodel(3, DSYMBOLS[i] as u32, costcontext);
        if c < mincost {
            bestdist = DSYMBOLS[i];
            mincost = c;
        }
    }

    costmodel(bestlength as u32, bestdist as u32, costcontext)
}

/**
 * Performs the forward pass for "squeeze". Gets the most optimal length to reach
 * every byte from a previous byte, using cost calculations.
 * s: the ZopfliBlockState
 * in: the input data array
 * instart: where to start
 * inend: where to stop (not inclusive)
 * costmodel: function to calculate the cost of some lit/len/dist pair.
 * costcontext: abstract context for the costmodel function
 * length_array: output array of size (inend - instart) which will receive the best
 *     length to reach this byte from a previous byte.
 * returns the cost that was, according to the costmodel, needed to get to the end.
 */
unsafe fn get_best_lengths(s: *const BlockState, in_: *const u8, instart: usize, inend: usize, costmodel: CostModelFun, costcontext: *const c_void, length_array: *mut u16) -> f64 {
    // Best cost to get here so far.
    let blocksize: usize = inend - instart;
    let mut leng: u16 = uninitialized();
    let mut dist: u16 = uninitialized();
    let mut sublen: [u16; 259] = uninitialized();
    let windowstart: usize = if instart > WINDOW_SIZE { instart - WINDOW_SIZE } else { 0 };
    let result: f64;
    let mincost: f64 = get_cost_model_min_cost(costmodel, costcontext);

    if instart == inend {
        return 0f64;
    }

    let costs: *mut f32 = malloc(size_of::<f32>() as size_t * (blocksize as size_t + 1)) as *mut f32;
    if costs.is_null() {
        panic!("Allocation failed");
    }

    let mut hash = Hash::new(WINDOW_SIZE);
    let h: *mut Hash = &mut hash;
    warmup_hash(in_, windowstart, inend, h);
    for i in windowstart..instart {
        update_hash(in_, i, inend, h);
    }

    for i in 1..blocksize+1 {
        *costs.offset(i as isize) = LARGE_FLOAT as f32;
    }
    *costs.offset(0) = 0f32; // Because it's the start.
    *length_array.offset(0) = 0;

    let mut i: usize = instart;
    while i < inend {
        let mut j: usize = i - instart; // Index in the costs array and length_array.
        update_hash(in_, i, inend, h);

        #[cfg(feature = "shortcut-long-repetitions")]
        unsafe fn shortcut_long_repetitions(in_: *const u8, instart: usize, inend: usize, costmodel: CostModelFun, costcontext: *const c_void, length_array: *mut u16, h: *mut Hash, i: *mut usize, j: *mut usize, costs: *mut f32) {
            use util::WINDOW_MASK;
            // If we're in a long repetition of the same character and have more than
            // ZOPFLI_MAX_MATCH characters before and after our position.
            if *(*h).hash_same.same.offset((*i & WINDOW_MASK) as isize) as usize > MAX_MATCH * 2
                && *i > instart + MAX_MATCH + 1
                && *i + MAX_MATCH * 2 + 1 < inend
                && *(*h).hash_same.same.offset(((*i - MAX_MATCH) & WINDOW_MASK) as isize) as usize > MAX_MATCH {
                    let symbolcost: f64 = costmodel(MAX_MATCH as u32, 1, costcontext);
                    // Set the length to reach each one to ZOPFLI_MAX_MATCH, and the cost to
                    // the cost corresponding to that length. Doing this, we skip
                    // ZOPFLI_MAX_MATCH values to avoid calling ZopfliFindLongestMatch.
                    for _ in 0..MAX_MATCH {
                        *costs.offset((*j + MAX_MATCH) as isize) = (*costs.offset(*j as isize) as f64 + symbolcost) as f32;
                        *length_array.offset((*j + MAX_MATCH) as isize) = MAX_MATCH as u16;
                        *i += 1;
                        *j += 1;
                        update_hash(in_, *i, inend, h);
                    }
                }
        }
        #[cfg(not(feature = "shortcut-long-repetitions"))]
        fn shortcut_long_repetitions(_in: *const u8, _instart: usize, _inend: usize, _costmodel: CostModelFun, _costcontext: *const c_void, _length_array: *const u16, _h: *const Hash, _i: *const usize, _j: *const usize, _costs: *const f32) { }
        shortcut_long_repetitions(in_, instart, inend, costmodel, costcontext, length_array, h, &mut i, &mut j, costs);

        find_longest_match(s, h, in_, i, inend, MAX_MATCH, sublen.as_mut_ptr(), &mut dist, &mut leng);

        // Literal.
        if i + 1 <= inend {
            let new_cost: f64 = *costs.offset(j as isize) as f64 + costmodel(*in_.offset(i as isize) as u32, 0, costcontext);
            assert!(new_cost >= 0f64);
            if new_cost < *costs.offset(j as isize + 1) as f64 {
                *costs.offset(j as isize + 1) = new_cost as f32;
                *length_array.offset(j as isize + 1) = 1;
            }
        }
        // Lengths.
        let mut k: usize = 3;
        while k <= leng as usize && i + k <= inend {
            // Calling the cost model is expensive, avoid this if we are already at
            // the minimum possible cost that it can return.
            if *costs.offset((j + k) as isize) as f64 - *costs.offset(j as isize) as f64 <= mincost {
                continue;
            }

            let new_cost: f64 = *costs.offset(j as isize) as f64 + costmodel(k as u32, sublen[k] as u32, costcontext);
            assert!(new_cost >= 0f64);
            if new_cost < *costs.offset((j + k) as isize) as f64 {
                assert!(k <= MAX_MATCH);
                *costs.offset((j + k) as isize) = new_cost as f32;
                *length_array.offset((j + k) as isize) = k as u16;
            }

            k += 1;
        }
        i += 1;
    }

    assert!(*costs.offset(blocksize as isize) >= 0f32);
    result = *costs.offset(blocksize as isize) as f64;

    Hash::clean(h);
    free(costs as *mut c_void);

    result
}

/// Calculates the optimal path of lz77 lengths to use, from the calculated
/// length_array. The length_array must contain the optimal length to reach that
/// byte. The path will be filled with the lengths to use, so its data size will be
/// the amount of lz77 symbols.
unsafe fn trace_backwards(size: usize, length_array: *const u16, path: *mut *mut u16, pathsize: *mut usize) {
    let mut index: usize = size;
    if size == 0 {
        return;
    }
    loop {
        append_data!(*length_array.offset(index as isize), *path, *pathsize);
        assert!(*length_array.offset(index as isize) as usize <= index);
        assert!(*length_array.offset(index as isize) as usize <= MAX_MATCH);
        assert!(*length_array.offset(index as isize) != 0);
        index -= *length_array.offset(index as isize) as usize;
        if index == 0 {
            break;
        }
    }

    // Mirror result.
    index = 0;
    while index < *pathsize / 2 {
        let temp: u16 = *(*path).offset(index as isize);
        *(*path).offset(index as isize) = *(*path).offset((*pathsize - index - 1) as isize);
        *(*path).offset((*pathsize - index - 1) as isize) = temp;
        index += 1;
    }
}

unsafe fn follow_path(s: *const BlockState, in_: *const u8, instart: usize, inend: usize, path: *const u16, pathsize: usize, store: *mut LZ77Store) {
    let windowstart: usize = if instart > WINDOW_SIZE { instart - WINDOW_SIZE } else { 0 };

    let mut _total_length_test: usize = 0;

    if instart == inend {
        return;
    }

    let mut hash = Hash::new(WINDOW_SIZE);
    let h: *mut Hash = &mut hash;
    warmup_hash(in_, windowstart, inend, h);
    for i in windowstart..instart {
        update_hash(in_, i, inend, h);
    }

    let mut pos: usize = instart;
    for i in 0..pathsize {
        let mut length: u16 = *path.offset(i as isize);
        let mut dummy_length: u16 = uninitialized();
        let mut dist: u16 = uninitialized();
        assert!(pos < inend);

        update_hash(in_, pos, inend, h);

        // Add to output.
        if length as usize >= MIN_MATCH {
            // Get the distance by recalculating longest match. The found length
            // should match the length from the path.
            find_longest_match(s, h, in_, pos, inend, length as usize, null_mut(), &mut dist, &mut dummy_length);
            assert!(!(dummy_length != length && length > 2 && dummy_length > 2));
            verify_len_dist(in_, inend, pos, dist, length);
            store_litlen_dist(length, dist, store);
            _total_length_test += length as usize;
        } else {
            length = 1;
            store_litlen_dist(*in_.offset(pos as isize) as u16, 0, store);
            _total_length_test += 1;
        }

        assert!(pos + length as usize <= inend);
        for j in 1..length {
            update_hash(in_, pos + j as usize, inend, h);
        }

        pos += length as usize;
    }

    Hash::clean(h);
}

/// Calculates the entropy of the statistics
unsafe fn calculate_statistics(stats: *mut SymbolStats) {
    calculate_entropy((*stats).litlens.as_ptr(), 288, (*stats).ll_symbols.as_mut_ptr());
    calculate_entropy((*stats).dists.as_ptr(), 32, (*stats).d_symbols.as_mut_ptr());
}

/// Appends the symbol statistics from the store.
unsafe fn get_statistics(store: *const LZ77Store, stats: *mut SymbolStats) {
    for i in 0..(*store).size {
        if *(*store).dists.offset(i as isize) == 0 {
            (*stats).litlens[*(*store).litlens.offset(i as isize) as usize] += 1;
        } else {
            (*stats).litlens[get_length_symbol(*(*store).litlens.offset(i as isize) as i32) as usize] += 1;
            (*stats).dists[get_dist_symbol(*(*store).dists.offset(i as isize) as i32) as usize] += 1;
        }
    }
    (*stats).litlens[256] = 1; // End Symbol.

    calculate_statistics(stats);
}

/**
 * Does a single run for ZopfliLZ77Optimal. For good compression, repeated runs
 * with updated statistics should be performed.
 * 
 * s: the block state
 * in: the input data array
 * instart: where to start
 * inend: where to stop (not inclusive)
 * path: pointer to dynamically allocated memory to store the path
 * pathsize: pointer to the size of the dynamic path array
 * length_array: array if size (inend - instart) used to store lengths
 * costmodel: function to use as the cost model for this squeeze run
 * costcontext: abstract context for the costmodel function
 * store: place to output the LZ77 data
 * returns the cost that was, according to the costmodel, needed to get to the end.
 *     This is not the actual cost.
 */
unsafe fn lz77_optimal_run(s: *const BlockState, in_: *const u8, instart: usize, inend: usize, path: *mut *mut u16, pathsize: *mut usize,
                           length_array: *mut u16, costmodel: CostModelFun, costcontext: *const c_void, store: *mut LZ77Store) -> f64 {
    let cost: f64 = get_best_lengths(s, in_, instart, inend, costmodel, costcontext, length_array);
    free(*path as *mut c_void);
    *path = null_mut();
    *pathsize = 0;
    trace_backwards(inend - instart, length_array, path, pathsize);
    follow_path(s, in_, instart, inend, *path, *pathsize, store);
    assert!(cost < LARGE_FLOAT);
    cost
}



/// Calculates lit/len and dist pairs for given data.
/// If instart is larger than 0, it uses values before instart as starting
/// dictionary.
pub unsafe fn lz77_optimal(s: *const BlockState, in_: *const u8, instart: usize, inend: usize, store: *mut LZ77Store) {
    // Dist to get to here with smallest cost.
    let blocksize: usize = inend - instart;
    let length_array: *mut u16 = malloc(size_of::<u16>() as size_t * (blocksize as size_t + 1)) as *mut u16;
    let mut path: *mut u16 = null_mut();
    let mut pathsize: usize = 0;
    let mut currentstore = LZ77Store::new();
    let mut stats = SymbolStats::new();
    let mut beststats: SymbolStats = uninitialized();
    let mut laststats: SymbolStats = uninitialized();
    let mut cost: f64;
    let mut bestcost: f64 = LARGE_FLOAT;
    let mut lastcost: f64 = 0f64;
    // Try randomizing the costs a bit once the size stabilizes.
    let mut ran_state = RanState::new();
    let mut lastrandomstep: i32 = -1;

    if length_array.is_null() {
        panic!("Allocation failed");
    }

    // Do regular deflate, then loop multiple shortest path runs, each time using
    // the statistics of the previous run.

    // Initial run.
    lz77_greedy(s, in_, instart, inend, &mut currentstore);
    get_statistics(&currentstore, &mut stats);

    // Repeat statistics with each time the cost model from the previous stat
    // run.
    for i in 0..(*(*s).options).numiterations {
        LZ77Store::clean(&mut currentstore);
        LZ77Store::init(&mut currentstore);
        lz77_optimal_run(s, in_, instart, inend, &mut path, &mut pathsize, length_array, get_cost_stat, &stats as *const _ as *const c_void, &mut currentstore);
        cost = calculate_block_size(currentstore.litlens, currentstore.dists, 0, currentstore.size, 2);
        if (*(*s).options).verbose_more || ((*(*s).options).verbose && cost < bestcost) {
            println_err!("Iteration {}: {} bit", i, cost as i32);
        }
        if cost < bestcost {
            // Copy to the output store.
            copy_lz77_store(&currentstore, store);
            copy_stats(&stats, &mut beststats);
            bestcost = cost;
        }
        copy_stats(&stats, &mut laststats);
        clear_stat_freqs(&mut stats);
        get_statistics(&currentstore, &mut stats);
        if lastrandomstep != -1 {
            // This makes it converge slower but better. Do it only once the
            // randomness kicks in so that if the user does few iterations, it gives a
            // better result sooner.
            add_weighed_stat_freqs(&stats, 1.0, &laststats, 0.5, &mut stats);
            calculate_statistics(&mut stats);
        }
        if i > 5 && cost == lastcost {
            copy_stats(&beststats, &mut stats);
            randomize_stat_freqs(&mut ran_state, &mut stats);
            calculate_statistics(&mut stats);
            lastrandomstep = 1;
        }
        lastcost = cost;
    }

    free(length_array as *mut c_void);
    free(path as *mut c_void);
    clean_lz77_store(&mut currentstore);
}

/// Does the same as ZopfliLZ77Optimal, but optimized for the fixed tree of the
/// deflate standard.
/// The fixed tree never gives the best compression. But this gives the best
/// possible LZ77 encoding possible with the fixed tree.
/// This does not create or output any fixed tree, only LZ77 data optimized for
/// using with a fixed tree.
/// If instart is larger than 0, it uses values before instart as starting
/// dictionary.
pub unsafe fn lz77_optimal_fixed(s: *mut BlockState, in_: *const u8, instart: usize, inend: usize, store: *mut LZ77Store) {
    // Dist to get to here with smallest cost.
    let blocksize: usize = inend - instart;
    let length_array: *mut u16 = malloc(size_of::<u16>() as size_t * (blocksize as size_t + 1)) as *mut u16;
    let mut path: *mut u16 = null_mut();
    let mut pathsize: usize = 0;

    if length_array.is_null() {
        panic!("Allocation failed");
    }

    (*s).blockstart = instart;
    (*s).blockend = inend;

    // Shortest path for fixed tree This one should give the shortest possible
    // result for fixed tree, no repeated runs are needed since the tree is known.
    lz77_optimal_run(s, in_, instart, inend, &mut path, &mut pathsize, length_array, get_cost_fixed, null_mut(), store);

    free(length_array as *mut c_void);
    free(path as *mut c_void);
}
