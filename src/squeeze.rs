use std::io::Write;
use std::iter;

use deflate::calculate_block_size;
use hash::{Hash, update_hash, warmup_hash};
use lz77::{BlockState, LZ77Store, find_longest_match, lz77_greedy, store_litlen_dist,
           verify_len_dist};
use tree::calculate_entropy;
use util::{LARGE_FLOAT, MAX_MATCH, MIN_MATCH, NUM_D, NUM_LL, WINDOW_SIZE, get_dist_extra_bits,
           get_dist_symbol, get_length_extra_bits, get_length_symbol};

struct SymbolStats {
    /// The literal and length symbols.
    litlens: [usize; NUM_LL],
    /// The 32 unique dist symbols, not the 32768 possible dists.
    dists: [usize; NUM_D],

    /// Length of each lit/len symbol in bits.
    ll_symbols: [f64; NUM_LL],
    /// Length of each dist symbol in bits.
    d_symbols: [f64; NUM_D],
}

impl SymbolStats {
    fn new() -> SymbolStats {
        SymbolStats {
            litlens: [0usize; NUM_LL],
            dists: [0usize; NUM_D],
            ll_symbols: [0f64; NUM_LL],
            d_symbols: [0f64; NUM_D],
        }
    }
}

fn copy_stats(source: &SymbolStats, dest: &mut SymbolStats) {
    dest.litlens = source.litlens;
    dest.dists = source.dists;
    dest.ll_symbols = source.ll_symbols;
    dest.d_symbols = source.d_symbols;
}

/// Adds the bit lengths.
fn add_weighed_stat_freqs(stats1: &mut SymbolStats, w1: f64, stats2: &SymbolStats, w2: f64) {
    for i in 0..NUM_LL {
        stats1.litlens[i] =
            (stats1.litlens[i] as f64 * w1 + stats2.litlens[i] as f64 * w2) as usize;
    }
    for i in 0..NUM_D {
        stats1.dists[i] = (stats1.dists[i] as f64 * w1 + stats2.dists[i] as f64 * w2) as usize;
    }
    stats1.litlens[256] = 1; // End symbol.
}

struct RanState {
    m_w: u32,
    m_z: u32,
}

impl RanState {
    fn new() -> RanState {
        RanState { m_w: 1, m_z: 2 }
    }
}

/// Get random number: "Multiply-With-Carry" generator of G. Marsaglia
fn ran(state: &mut RanState) -> u32 {
    state.m_z = 36969 * (state.m_z & 65535) + (state.m_z >> 16);
    state.m_w = 18000 * (state.m_w & 65535) + (state.m_w >> 16);
    return (state.m_z << 16).wrapping_add(state.m_w);  // 32-bit result.
}

fn randomize_freqs(state: &mut RanState, freqs: &mut [usize]) {
    let n = freqs.len();
    for i in 0..n {
        if (ran(state) >> 4) % 3 == 0 {
            freqs[i] = freqs[(ran(state) % n as u32) as usize];
        }
    }
}

fn randomize_stat_freqs(state: &mut RanState, stats: &mut SymbolStats) {
    randomize_freqs(state, &mut stats.litlens);
    randomize_freqs(state, &mut stats.dists);
    stats.litlens[256] = 1; // End symbol.
}

fn clear_stat_freqs(stats: &mut SymbolStats) {
    stats.litlens = [0; NUM_LL];
    stats.dists = [0; NUM_D];
}

trait CostModel {
    /// Function that calculates a cost based on a model for the given LZ77 symbol.
    /// litlen: means literal symbol if dist is 0, length otherwise.
    fn get_cost(&self, litlen: u32, dist: u32) -> f64;
}

struct FixedCostModel;
impl CostModel for FixedCostModel {
    /// Cost model which should exactly match fixed tree.
    fn get_cost(&self, litlen: u32, dist: u32) -> f64 {
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
}

impl CostModel for SymbolStats {
    /// Cost model based on symbol statistics.
    fn get_cost(&self, litlen: u32, dist: u32) -> f64 {
        if dist == 0 {
            self.ll_symbols[litlen as usize]
        } else {
            let lsym: i32 = get_length_symbol(litlen as i32);
            let lbits: i32 = get_length_extra_bits(litlen as i32);
            let dsym: i32 = get_dist_symbol(dist as i32);
            let dbits: i32 = get_dist_extra_bits(dist as i32);
            self.ll_symbols[lsym as usize] + lbits as f64 + self.d_symbols[dsym as usize] + dbits as f64
        }
    }
}

/// Finds the minimum possible cost this cost model can return for valid length and
/// distance symbols.
fn get_cost_model_min_cost(costmodel: &CostModel) -> f64 {
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
        let c: f64 = costmodel.get_cost(i, 1);
        if c < mincost {
            bestlength = i as i32;
            mincost = c;
        }
    }

    let mut mincost: f64 = LARGE_FLOAT;
    for i in 0..30 {
        let c: f64 = costmodel.get_cost(3, DSYMBOLS[i] as u32);
        if c < mincost {
            bestdist = DSYMBOLS[i];
            mincost = c;
        }
    }

    costmodel.get_cost(bestlength as u32, bestdist as u32)
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
fn get_best_lengths(s: &mut BlockState,
                    in_: &[u8],
                    instart: usize,
                    inend: usize,
                    costmodel: &CostModel,
                    length_array: &mut Vec<u16>)
                    -> f64 {
    // Best cost to get here so far.
    let blocksize: usize = inend - instart;
    let mut leng: u16 = 0;
    let mut dist: u16 = 0;
    let mut sublen: Option<[u16; 259]> = Some([0; 259]);
    let windowstart: usize = if instart > WINDOW_SIZE { instart - WINDOW_SIZE } else { 0 };
    let result: f64;
    let mincost: f64 = get_cost_model_min_cost(costmodel);

    if instart == inend {
        return 0f64;
    }

    let mut costs: Vec<f32> = iter::repeat(LARGE_FLOAT as f32).take(blocksize + 1).collect();

    let mut hash = Hash::new(WINDOW_SIZE);
    warmup_hash(in_, windowstart, inend, &mut hash);
    for i in windowstart..instart {
        update_hash(in_, i, inend, &mut hash);
    }

    costs[0] = 0f32; // Because it's the start.
    length_array[0] = 0;

    let mut i: usize = instart;
    while i < inend {
        let mut j: usize = i - instart; // Index in the costs array and length_array.
        update_hash(in_, i, inend, &mut hash);

        #[cfg(feature = "shortcut-long-repetitions")]
        fn shortcut_long_repetitions(in_: &[u8], instart: usize, inend: usize, costmodel: &CostModel, length_array: &mut Vec<u16>, h: &mut Hash, i: &mut usize, j: &mut usize, costs: &mut Vec<f32>) {
            use util::WINDOW_MASK;
            // If we're in a long repetition of the same character and have more than
            // ZOPFLI_MAX_MATCH characters before and after our position.
            if h.hash_same.same[*i & WINDOW_MASK] as usize > MAX_MATCH * 2
                && *i > instart + MAX_MATCH + 1
                && *i + MAX_MATCH * 2 + 1 < inend
                && h.hash_same.same[(*i - MAX_MATCH) & WINDOW_MASK] as usize > MAX_MATCH {
                    let symbolcost: f64 = costmodel.get_cost(MAX_MATCH as u32, 1);
                    // Set the length to reach each one to ZOPFLI_MAX_MATCH, and the cost to
                    // the cost corresponding to that length. Doing this, we skip
                    // ZOPFLI_MAX_MATCH values to avoid calling ZopfliFindLongestMatch.
                    for _ in 0..MAX_MATCH {
                        costs[*j + MAX_MATCH] = (costs[*j] as f64 + symbolcost) as f32;
                        length_array[*j + MAX_MATCH] = MAX_MATCH as u16;
                        *i += 1;
                        *j += 1;
                        update_hash(in_, *i, inend, h);
                    }
                }
        }
        #[cfg(not(feature = "shortcut-long-repetitions"))]
        fn shortcut_long_repetitions(_in: &[u8], _instart: usize, _inend: usize, _costmodel: &CostModel, _length_array: &Vec<u16>, _h: &Hash, _i: &usize, _j: &usize, _costs: &Vec<f32>) { }
        shortcut_long_repetitions(in_, instart, inend, costmodel, length_array, &mut hash, &mut i, &mut j, &mut costs);

        find_longest_match(s, &hash, in_, i, inend, MAX_MATCH, &mut sublen, &mut dist, &mut leng);

        // Literal.
        if i + 1 <= inend {
            let new_cost: f64 = costs[j] as f64 + costmodel.get_cost(in_[i] as u32, 0);
            assert!(new_cost >= 0f64);
            if new_cost < costs[j + 1] as f64 {
                costs[j + 1] = new_cost as f32;
                length_array[j + 1] = 1;
            }
        }
        // Lengths.
        let mut k: usize = 3;
        while k <= leng as usize && i + k <= inend {
            // Calling the cost model is expensive, avoid this if we are already at
            // the minimum possible cost that it can return.
            if costs[j + k] as f64 - costs[j] as f64 <= mincost {
                k += 1;
                continue;
            }

            let new_cost: f64 = costs[j] as f64 +
                                costmodel.get_cost(k as u32, sublen.as_ref().unwrap()[k] as u32);
            assert!(new_cost >= 0f64);
            if new_cost < costs[j + k] as f64 {
                assert!(k <= MAX_MATCH);
                costs[j + k] = new_cost as f32;
                length_array[j + k] = k as u16;
            }

            k += 1;
        }
        i += 1;
    }

    assert!(costs[blocksize] >= 0f32);
    result = costs[blocksize] as f64;

    result
}

/// Calculates the optimal path of lz77 lengths to use, from the calculated
/// length_array. The length_array must contain the optimal length to reach that
/// byte. The path will be filled with the lengths to use, so its data size will be
/// the amount of lz77 symbols.
fn trace_backwards(size: usize, length_array: &Vec<u16>, path: &mut Vec<u16>) {
    let mut index: usize = size;
    if size == 0 {
        return;
    }
    loop {
        path.push(length_array[index]);
        assert!(length_array[index] as usize <= index);
        assert!(length_array[index] as usize <= MAX_MATCH);
        assert!(length_array[index] != 0);
        index -= length_array[index] as usize;
        if index == 0 {
            break;
        }
    }

    path.reverse();
}

fn follow_path(s: &mut BlockState, in_: &[u8], instart: usize, inend: usize, path: &Vec<u16>, store: &mut LZ77Store) {
    let windowstart: usize = if instart > WINDOW_SIZE { instart - WINDOW_SIZE } else { 0 };

    let mut _total_length_test: usize = 0;

    if instart == inend {
        return;
    }

    let mut hash = Hash::new(WINDOW_SIZE);
    warmup_hash(in_, windowstart, inend, &mut hash);
    for i in windowstart..instart {
        update_hash(in_, i, inend, &mut hash);
    }

    let mut pos: usize = instart;
    for i in 0..path.len() {
        let mut length: u16 = path[i];
        assert!(pos < inend);

        update_hash(in_, pos, inend, &mut hash);

        // Add to output.
        if length as usize >= MIN_MATCH {
            let mut dummy_length: u16 = 0;
            let mut dist: u16 = 0;
            // Get the distance by recalculating longest match. The found length
            // should match the length from the path.
            find_longest_match(s, &hash, in_, pos, inend, length as usize, &mut None, &mut dist, &mut dummy_length);
            assert!(!(dummy_length != length && length > 2 && dummy_length > 2));
            verify_len_dist(in_, inend, pos, dist, length);
            store_litlen_dist(length, dist, pos, store);
            _total_length_test += length as usize;
        } else {
            length = 1;
            store_litlen_dist(in_[pos] as u16, 0, pos, store);
            _total_length_test += 1;
        }

        assert!(pos + length as usize <= inend);
        for j in 1..length {
            update_hash(in_, pos + j as usize, inend, &mut hash);
        }

        pos += length as usize;
    }
}

/// Calculates the entropy of the statistics
fn calculate_statistics(stats: &mut SymbolStats) {
    calculate_entropy(&stats.litlens, &mut stats.ll_symbols);
    calculate_entropy(&stats.dists, &mut stats.d_symbols);
}

/// Appends the symbol statistics from the store.
fn get_statistics(store: &LZ77Store, stats: &mut SymbolStats) {
    for i in 0..store.litlens.len() {
        if store.dists[i] == 0 {
            stats.litlens[store.litlens[i] as usize] += 1;
        } else {
            stats.litlens[get_length_symbol(store.litlens[i] as i32) as usize] += 1;
            stats.dists[get_dist_symbol(store.dists[i] as i32) as usize] += 1;
        }
    }
    stats.litlens[256] = 1; // End Symbol.

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
 * length_array: array of size (inend - instart) used to store lengths
 * costmodel: function to use as the cost model for this squeeze run
 * costcontext: abstract context for the costmodel function
 * store: place to output the LZ77 data
 * returns the cost that was, according to the costmodel, needed to get to the end.
 *     This is not the actual cost.
 */
fn lz77_optimal_run(s: &mut BlockState,
                    in_: &[u8],
                    instart: usize,
                    inend: usize,
                    path: &mut Vec<u16>,
                    length_array: &mut Vec<u16>,
                    costmodel: &CostModel,
                    store: &mut LZ77Store)
                    -> f64 {
    let cost: f64 = get_best_lengths(s, in_, instart, inend, costmodel, length_array);
    path.clear();
    trace_backwards(inend - instart, length_array, path);
    follow_path(s, in_, instart, inend, path, store);
    assert!(cost < LARGE_FLOAT);
    cost
}

/// Calculates lit/len and dist pairs for given data.
/// If instart is larger than 0, it uses values before instart as starting
/// dictionary.
pub fn lz77_optimal<'a>(s: &mut BlockState,
                        in_: &'a [u8],
                        instart: usize,
                        inend: usize,
                        numiterations: i32,
                        store: &mut LZ77Store<'a>) {
    // Dist to get to here with smallest cost.
    let blocksize: usize = inend - instart;
    let mut length_array: Vec<u16> = iter::repeat(0).take(blocksize + 1).collect();
    let mut path: Vec<u16> = Vec::new();
    let mut currentstore = LZ77Store::new(in_);
    let mut stats = SymbolStats::new();
    let mut beststats = SymbolStats::new();
    let mut laststats = SymbolStats::new();
    let mut cost: f64;
    let mut bestcost: f64 = LARGE_FLOAT;
    let mut lastcost: f64 = 0f64;
    // Try randomizing the costs a bit once the size stabilizes.
    let mut ran_state = RanState::new();
    let mut lastrandomstep: i32 = -1;

    // Do regular deflate, then loop multiple shortest path runs, each time using
    // the statistics of the previous run.

    // Initial run.
    lz77_greedy(s, in_, instart, inend, &mut currentstore);
    get_statistics(&currentstore, &mut stats);

    // Repeat statistics with each time the cost model from the previous stat
    // run.
    for i in 0..numiterations {
        let mut currentstore = LZ77Store::new(in_);
        lz77_optimal_run(s, in_, instart, inend, &mut path, &mut length_array, &stats, &mut currentstore);
        cost = calculate_block_size(&currentstore, 0, currentstore.size, 2);
        if (*s.options).verbose_more || ((*s.options).verbose && cost < bestcost) {
            println_err!("Iteration {}: {} bit", i, cost as i32);
        }
        if cost < bestcost {
            // Copy to the output store.
            *store = currentstore.clone();
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
            add_weighed_stat_freqs(&mut stats, 1.0, &laststats, 0.5);
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
}

/// Does the same as ZopfliLZ77Optimal, but optimized for the fixed tree of the
/// deflate standard.
/// The fixed tree never gives the best compression. But this gives the best
/// possible LZ77 encoding possible with the fixed tree.
/// This does not create or output any fixed tree, only LZ77 data optimized for
/// using with a fixed tree.
/// If instart is larger than 0, it uses values before instart as starting
/// dictionary.
pub fn lz77_optimal_fixed(s: &mut BlockState,
                          in_: &[u8],
                          instart: usize,
                          inend: usize,
                          store: &mut LZ77Store) {
    // Dist to get to here with smallest cost.
    let blocksize: usize = inend - instart;
    let mut length_array: Vec<u16> = iter::repeat(0).take(blocksize + 1).collect();
    let mut path: Vec<u16> = Vec::new();

    s.blockstart = instart;
    s.blockend = inend;

    // Shortest path for fixed tree This one should give the shortest possible
    // result for fixed tree, no repeated runs are needed since the tree is known.
    lz77_optimal_run(s, in_, instart, inend, &mut path, &mut length_array, &FixedCostModel, store);
}
