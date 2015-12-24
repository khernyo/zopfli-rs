//! Functions for basic LZ77 compression and utilities for the "squeeze" LZ77
//! compression.

use std::cell::RefCell;
use std::rc::Rc;

#[cfg(feature = "longest-match-cache")]
use super::cache;
#[cfg(feature = "longest-match-cache")]
use cache::LongestMatchCache;

use super::hash;
use super::Options;

use hash::Hash;
use util::{get_length_symbol, get_dist_symbol,
    MIN_MATCH, MAX_MATCH, MAX_CHAIN_HITS, NUM_D, NUM_LL, WINDOW_MASK, WINDOW_SIZE};

/// Stores lit/length and dist pairs for LZ77.
/// Parameter litlens: Contains the literal symbols or length values.
/// Parameter dists: Contains the distances. A value is 0 to indicate that there is
/// no dist and the corresponding litlens value is a literal instead of a length.
/// Parameter size: The size of both the litlens and dists arrays.
/// The memory can best be managed by using ZopfliInitLZ77Store to initialize it,
/// ZopfliCleanLZ77Store to destroy it, and ZopfliStoreLitLenDist to append values.
#[derive(Clone)]
pub struct LZ77Store<'a> {
    /// Lit or len.
    pub litlens: Vec<u16>,
    /// If 0: indicates literal in corresponding litlens,
    /// if > 0: length in corresponding litlens, this is the distance.
    pub dists: Vec<u16>,
    pub size: usize,

    /// original data
    pub data: &'a [u8],
    pub pos: Vec<usize>,

    ll_symbol: Vec<u16>,
    d_symbol: Vec<u16>,

    /// Cumulative histograms wrapping around per chunk. Each chunk has the amount
    /// of distinct symbols as length, so using 1 value per LZ77 symbol, we have a
    /// precise histogram at every N symbols, and the rest can be calculated by
    /// looping through the actual symbols of this chunk.
    ll_counts: Vec<usize>,
    d_counts: Vec<usize>,
}

impl<'a> LZ77Store<'a> {
    pub fn new(data: &'a [u8]) -> LZ77Store<'a> {
        LZ77Store {
            litlens: Vec::new(),
            dists: Vec::new(),
            size: 0,
            data: data,
            pos: Vec::new(),
            ll_symbol: Vec::new(),
            d_symbol: Vec::new(),
            ll_counts: Vec::new(),
            d_counts: Vec::new(),
        }
    }
}

/// Some state information for compressing a block.
/// This is currently a bit under-used (with mainly only the longest match cache),
/// but is kept for easy future expansion.
pub struct BlockState<'a> {
    pub options: &'a Options,

    /// Cache for length/distance pairs found so far.
    #[cfg(feature = "longest-match-cache")]
    pub lmc: Option<LongestMatchCache>,

    /// The start (inclusive) and end (not inclusive) of the current block.
    pub blockstart: usize,
    pub blockend: usize,
}

impl<'a> BlockState<'a> {
    #[cfg(feature = "longest-match-cache")]
    pub fn new(options: &'a Options,
               blockstart: usize,
               blockend: usize,
               add_lmc: bool)
               -> BlockState<'a> {
        BlockState {
            options: options,
            blockstart: blockstart,
            blockend: blockend,
            lmc: if add_lmc { Some(LongestMatchCache::new(blockend - blockstart)) } else { None },
        }
    }

    #[cfg(not(feature = "longest-match-cache"))]
    pub fn new(options: &'a Options,
               blockstart: usize,
               blockend: usize,
               _add_lmc: bool)
               -> BlockState<'a> {
        BlockState {
            options: options,
            blockstart: blockstart,
            blockend: blockend,
        }
    }
}

/// Appends the length and distance to the LZ77 arrays of the ZopfliLZ77Store.
/// context must be a ZopfliLZ77Store*.
pub fn store_litlen_dist(length: u16, dist: u16, pos: usize, store: &mut LZ77Store) {
    // Needed for using ZOPFLI_APPEND_DATA twice.
    let origsize: usize = store.size;
    let llstart: usize = NUM_LL * (origsize / NUM_LL);
    let dstart: usize = NUM_D * (origsize / NUM_D);

    // Everytime the index wraps around, a new cumulative histogram is made: we're
    // keeping one histogram value per LZ77 symbol rather than a full histogram for
    // each to save memory.
    if origsize % NUM_LL == 0 {
        for i in 0..NUM_LL {
            let v = if origsize == 0 { 0 } else { store.ll_counts[origsize - NUM_LL + i] };
            store.ll_counts.push(v);
        }
    }
    if origsize % NUM_D == 0 {
        for i in 0..NUM_D {
            let v = if origsize == 0 { 0 } else { store.d_counts[origsize - NUM_D + i] };
            store.d_counts.push(v);
        }
    }

    store.litlens.push(length);
    store.dists.push(dist);
    store.pos.push(pos);
    assert!(length < 259);

    if dist == 0 {
        store.ll_symbol.push(length);
        store.d_symbol.push(0);
        store.ll_counts[llstart + length as usize] += 1;
    } else {
        store.ll_symbol.push(get_length_symbol(length as i32) as u16);
        store.d_symbol.push(get_dist_symbol(dist as i32) as u16);
        store.ll_counts[llstart + get_length_symbol(length as i32) as usize] += 1;
        store.d_counts[dstart + get_dist_symbol(dist as i32) as usize] += 1;
    }
    store.size = store.litlens.len();
    assert_eq!(store.dists.len(), store.size);
    assert_eq!(store.pos.len(), store.size);
    assert_eq!(store.ll_symbol.len(), store.size);
    assert_eq!(store.d_symbol.len(), store.size);
}

pub fn append_lz77_store(store: &LZ77Store, target: &mut LZ77Store) {
    for i in 0..store.size {
        store_litlen_dist(store.litlens[i], store.dists[i], store.pos[i], target);
    }
}

/// Gets the amount of raw bytes that this range of LZ77 symbols spans.
pub fn lz77_get_byte_range(lz77: &LZ77Store, lstart: usize, lend: usize) -> usize {
    if lstart == lend {
        0
    } else {
        let l: usize = lend - 1;
        lz77.pos[l] + (if lz77.dists[l] == 0 { 1 } else { lz77.litlens[l] }) as usize - lz77.pos[lstart]
    }
}

fn lz77_get_histogram_at(lz77: &LZ77Store,
                         lpos: usize,
                         ll_counts: &mut [usize; NUM_LL],
                         d_counts: &mut [usize; NUM_D]) {
    // The real histogram is created by using the histogram for this chunk, but
    // all superfluous values of this chunk subtracted.
    let llpos: usize = NUM_LL * (lpos / NUM_LL);
    let dpos: usize = NUM_D * (lpos / NUM_D);
    for i in 0..NUM_LL {
        ll_counts[i] = lz77.ll_counts[llpos + i];
    }
    let mut i: usize = lpos + 1;
    while i < llpos + NUM_LL && i < lz77.size {
        ll_counts[lz77.ll_symbol[i] as usize] -= 1;
        i += 1;
    }
    for i in 0..NUM_D {
        d_counts[i] = lz77.d_counts[dpos + i];
    }
    let mut i: usize = lpos + 1;
    while i < dpos + NUM_D && i < lz77.size {
        if lz77.dists[i] != 0 {
            d_counts[lz77.d_symbol[i] as usize] -= 1;
        }
        i += 1;
    }
}

/// Gets the histogram of lit/len and dist symbols in the given range, using the
/// cumulative histograms, so faster than adding one by one for large range. Does
/// not add the one end symbol of value 256.
pub fn lz77_get_histogram(lz77: &LZ77Store, lstart: usize, lend: usize)
                          -> ([usize; NUM_LL], [usize; NUM_D]) {
    let mut ll_counts: [usize; NUM_LL] = [0; NUM_LL];
    let mut d_counts: [usize; NUM_D] = [0; NUM_D];
    if lstart + NUM_LL * 3 > lend {
        for i in 0..NUM_LL {
            ll_counts[i] = 0;
        }
        for i in 0..NUM_D {
            d_counts[i] = 0;
        }
        for i in lstart..lend {
            ll_counts[lz77.ll_symbol[i] as usize] += 1;
            if lz77.dists[i] != 0 {
                d_counts[lz77.d_symbol[i] as usize] += 1;
            }
        }
    } else {
        // Subtract the cumulative histograms at the end and the start to get the
        // histogram for this range.
        lz77_get_histogram_at(lz77, lend - 1, &mut ll_counts, &mut d_counts);
        if lstart > 0 {
            let mut ll_counts2: [usize; NUM_LL] = [0; NUM_LL];
            let mut d_counts2: [usize; NUM_D] = [0; NUM_D];
            lz77_get_histogram_at(lz77, lstart - 1, &mut ll_counts2, &mut d_counts2);

            for i in 0..NUM_LL {
                ll_counts[i] -= ll_counts2[i];
            }
            for i in 0..NUM_D {
                d_counts[i] -= d_counts2[i];
            }
        }
    }
    (ll_counts, d_counts)
}

/**
 * Gets a score of the length given the distance. Typically, the score of the
 * length is the length itself, but if the distance is very long, decrease the
 * score of the length a bit to make up for the fact that long distances use large
 * amounts of extra bits.
 *
 * This is not an accurate score, it is a heuristic only for the greedy LZ77
 * implementation. More accurate cost models are employed later. Making this
 * heuristic more accurate may hurt rather than improve compression.
 *
 * The two direct uses of this heuristic are:
 * -avoid using a length of 3 in combination with a long distance. This only has
 *  an effect if length == 3.
 * -make a slightly better choice between the two options of the lazy matching.
 *
 * Indirectly, this affects:
 * -the block split points if the default of block splitting first is used, in a
 *  rather unpredictable way
 * -the first zopfli run, so it affects the chance of the first run being closer
 *  to the optimal output
 */
fn get_length_score(length: i32, distance: i32) -> i32 {
    // At 1024, the distance uses 9+ extra bits and this seems to be the sweet spot
    // on tested files.
    if distance > 1024 {
        length - 1
    } else {
        length
    }
}

/// Verifies if length and dist are indeed valid, only used for assertion.
pub fn verify_len_dist(data: &[u8], datasize: usize, pos: usize, dist: u16, length: u16) {
    // TODO(lode): make this only run in a debug compile, it's for assert only.

    assert!(pos + length as usize <= datasize);
    for i in 0..length {
        if data[pos - dist as usize + i as usize] != data[pos + i as usize] {
            assert_eq!(data[pos - dist as usize + i as usize],
                       data[pos + i as usize]);
            break;
        }
    }
}

/**
 * Finds how long the match of scan and match is. Can be used to find how many
 * bytes starting from scan, and from match, are equal. Returns the last byte
 * after scan, which is still equal to the correspondinb byte after match.
 * scan is the position to compare
 * match is the earlier position to compare.
 * end is the last possible byte, beyond which to stop looking.
 * safe_end is a few (8) bytes before end, for comparing multiple bytes at once.
 */
fn get_match(scan: &[u8], match_: &[u8]) -> usize {
    for i in 0..scan.len() {
        if scan[i] != match_[i] {
            return i;
        }
    }
    return scan.len();
}

#[cfg(not(feature = "longest-match-cache"))]
fn try_get_from_longest_match_cache(_s: &mut BlockState,
                                    _pos: usize,
                                    _limit: &mut usize,
                                    _sublen: &mut Option<[u16; 259]>,
                                    _distance: &mut u16,
                                    _length: &mut u16)
                                    -> bool {
    false
}

/// Gets distance, length and sublen values from the cache if possible.
/// Returns 1 if it got the values from the cache, 0 if not.
/// Updates the limit value to a smaller one if possible with more limited
/// information from the cache.
#[cfg(feature = "longest-match-cache")]
fn try_get_from_longest_match_cache(s: &mut BlockState,
                                    pos: usize,
                                    limit: &mut usize,
                                    sublen: &mut Option<[u16; 259]>,
                                    distance: &mut u16,
                                    length: &mut u16)
                                    -> bool {
    // The LMC cache starts at the beginning of the block rather than the
    // beginning of the whole array.
    let lmcpos: usize = pos - s.blockstart;

    // Length > 0 and dist 0 is invalid combination, which indicates on purpose
    // that this cache value is not filled in yet.
    let cache_available = s.lmc.as_ref().map_or(
        false,
        |lmc| lmc.length[lmcpos] == 0 || lmc.dist[lmcpos] != 0);
    let limit_of_for_cache: bool = cache_available && s.lmc.as_ref()
        .map(|lmc| *limit == MAX_MATCH || lmc.length[lmcpos] <= *limit as u16 || (sublen.is_some() && cache::max_cached_sublen(lmc, lmcpos as usize, lmc.length[lmcpos] as usize) >= *limit as u32)).unwrap();

    if s.lmc.is_some() && limit_of_for_cache && cache_available {
        let lmc = s.lmc.as_mut().unwrap();
        if sublen.is_none() || lmc.length[lmcpos] <= cache::max_cached_sublen(lmc, lmcpos as usize, lmc.length[lmcpos] as usize) as u16 {
            *length = lmc.length[lmcpos];
            if *length > *limit as u16 {
                *length = *limit as u16;
            }
            match sublen {
                &mut Some(ref mut sublen) => {
                    cache::cache_to_sublen(lmc, lmcpos as usize, *length as usize, sublen);
                    *distance = sublen[*length as usize];
                    if *limit == MAX_MATCH && *length >= MIN_MATCH as u16 {
                        assert_eq!(sublen[*length as usize], lmc.dist[lmcpos]);
                    }
                }
                &mut None => *distance = lmc.dist[lmcpos],
            }
            return true;
        }
        // Can't use much of the cache, since the "sublens" need to be calculated,
        // but at  least we already know when to stop.
        *limit = lmc.length[lmcpos] as usize;
    }
    false
}

#[cfg(not(feature = "longest-match-cache"))]
fn store_in_longest_match_cache(_s: &BlockState,
                                _pos: usize,
                                _limit: usize,
                                _sublen: &Option<[u16; 259]>,
                                _distance: u16,
                                _length: u16) {
}

/// Stores the found sublen, distance and length in the longest match cache, if
/// possible.
#[cfg(feature = "longest-match-cache")]
fn store_in_longest_match_cache(s: &mut BlockState,
                                pos: usize,
                                limit: usize,
                                sublen: &Option<[u16; 259]>,
                                distance: u16,
                                length: u16) {
    // The LMC cache starts at the beginning of the block rather than the
    // beginning of the whole array.
    let lmcpos: usize = pos - s.blockstart;

    // Length > 0 and dist 0 is invalid combination, which indicates on purpose
    // that this cache value is not filled in yet.
    let cache_available = s.lmc.as_ref().map_or(
        false,
        |lmc| lmc.length[lmcpos] == 0 || lmc.dist[lmcpos] != 0);

    if s.lmc.is_some() && limit == MAX_MATCH && sublen.is_some() && !cache_available {
        let lmc = s.lmc.as_mut().unwrap();
        assert_eq!(lmc.length[lmcpos], 1);
        assert_eq!(lmc.dist[lmcpos], 0);
        lmc.dist[lmcpos] = if length < MIN_MATCH as u16 { 0 } else { distance };
        lmc.length[lmcpos] = if length < MIN_MATCH as u16 { 0 } else { length };
        assert!(!(lmc.length[lmcpos] == 1 && lmc.dist[lmcpos] == 0));
        cache::sublen_to_cache(sublen.as_ref().unwrap(), lmcpos as usize, length as usize, lmc);
    }
}

/**
 * Finds the longest match (length and corresponding distance) for LZ77
 * compression.
 * Even when not using "sublen", it can be more efficient to provide an array,
 * because only then the caching is used.
 * array: the data
 * pos: position in the data to find the match for
 * size: size of the data
 * limit: limit length to maximum this value (default should be 258). This allows
 *     finding a shorter dist for that length (= less extra bits). Must be
 *     in the range [ZOPFLI_MIN_MATCH, ZOPFLI_MAX_MATCH].
 * sublen: output array of 259 elements, or null. Has, for each length, the
 *     smallest distance required to reach this length. Only 256 of its 259 values
 *     are used, the first 3 are ignored (the shortest length is 3. It is purely
 *     for convenience that the array is made 3 longer).
 */
pub fn find_longest_match(s: &mut BlockState,
                          h: &Hash,
                          array: &[u8],
                          pos: usize,
                          size: usize,
                          limit: usize,
                          sublen: &mut Option<[u16; 259]>,
                          distance: &mut u16,
                          length: &mut u16) {
    let mut limit = limit;

    let hpos: u16 = (pos & WINDOW_MASK) as u16;
    let mut bestdist: u16 = 0;
    let mut bestlength: u16 = 1;

    // For quitting early.
    let mut chain_counter = MAX_CHAIN_HITS;

    let mut hhead = h.head.clone();
    let mut hprev = h.prev.clone();
    let mut hhashval = h.hashval.clone();
    let mut hval: i32 = h.val;
    let mut switched_hash: bool = false;

    if cfg!(feature = "longest-match-cache") {
        if try_get_from_longest_match_cache(s, pos, &mut limit, sublen, distance, length) {
            assert!(pos + *length as usize <= size);
            return;
        }
    }

    assert!(limit <= MAX_MATCH);
    assert!(limit >= MIN_MATCH);
    assert!(pos < size);

    if size - pos < MIN_MATCH {
        // The rest of the code assumes there are at least ZOPFLI_MIN_MATCH bytes to
        // try.
        *length = 0;
        *distance = 0;
        return;
    }

    if pos + limit > size {
        limit = size - pos;
    }
    let arrayend = pos + limit;

    assert!(hval < 65536);

    // During the whole loop, p == hprev[pp].
    let mut pp: u16 = hhead.borrow()[hval as usize] as u16;
    let mut p: u16 = hprev.borrow()[pp as usize];

    assert_eq!(pp, hpos);

    // Not unsigned short on purpose.
    let mut dist: u32 = if p < pp { pp as u32 - p as u32 } else { (WINDOW_SIZE - p as usize + pp as usize) as u32 };

    // Go through all distances.
    while (dist as usize) < WINDOW_SIZE {
        let mut currentlength: u16 = 0;

        assert!((p as usize) < WINDOW_SIZE);
        assert_eq!(p, hprev.borrow()[pp as usize]);
        assert_eq!(hhashval.borrow()[p as usize], hval);

        if dist > 0 {
            assert!(pos < size);
            assert!(dist as usize <= pos);
            let mut scan = pos;
            let mut match_ = pos - dist as usize;

            // Testing the byte at position bestlength first, goes slightly faster.
            if pos + bestlength as usize >= size || array[scan + bestlength as usize] == array[match_ + bestlength as usize] {
                #[cfg(not(feature = "hash-same"))]
                fn do_hash_same(_h: &Hash,
                                _pos: usize,
                                _limit: usize,
                                _array: &[u8],
                                _scan: &mut usize,
                                _match_: &mut usize,
                                _dist: u32) {
                }

                #[cfg(feature = "hash-same")]
                fn do_hash_same(h: &Hash,
                                pos: usize,
                                limit: usize,
                                array: &[u8],
                                scan: &mut usize,
                                match_: &mut usize,
                                dist: u32) {
                    let same0: u16 = h.hash_same.same[pos & WINDOW_MASK];
                    if same0 > 2 && array[*scan] == array[*match_] {
                        let same1: u16 = h.hash_same.same[(pos - dist as usize) & WINDOW_MASK];
                        let mut same: u16 = if same0 < same1 { same0 } else { same1 };
                        if same as usize > limit {
                            same = limit as u16;
                        }
                        *scan += same as usize;
                        *match_ += same as usize;
                    }
                }
                do_hash_same(h, pos, limit, array, &mut scan, &mut match_, dist);

                scan += get_match(&array[scan..arrayend], &array[match_..arrayend]);
                // The found length.
                currentlength = (scan - pos) as u16;
            }

            if currentlength > bestlength {
                if let &mut Some(ref mut sublen) = sublen {
                    for j in bestlength + 1..currentlength + 1 {
                        sublen[j as usize] = dist as u16;
                    }
                }
                bestdist = dist as u16;
                bestlength = currentlength;
                if currentlength as usize >= limit {
                    break;
                }
            }
        }

        #[cfg(not(feature = "hash-same-hash"))]
        fn do_hash_same_hash(_h: &Hash,
                             _hhead: &mut Rc<RefCell<[i32; 65536]>>,
                             _hprev: &mut Rc<RefCell<Vec<u16>>>,
                             _hhashval: &mut Rc<RefCell<Vec<i32>>>,
                             _hval: &mut i32,
                             _switched_hash: &mut bool,
                             _bestlength: u16,
                             _hpos: u16,
                             _p: u16) {
        }

        #[cfg(feature = "hash-same-hash")]
        fn do_hash_same_hash(h: &Hash,
                             hhead: &mut Rc<RefCell<[i32; 65536]>>,
                             hprev: &mut Rc<RefCell<Vec<u16>>>,
                             hhashval: &mut Rc<RefCell<Vec<i32>>>,
                             hval: &mut i32,
                             switched_hash: &mut bool,
                             bestlength: u16,
                             hpos: u16,
                             p: u16) {
            // Switch to the other hash once this will be more efficient.
            if !*switched_hash && bestlength >= h.hash_same.same[hpos as usize] && h.hash_same_hash.val2 == h.hash_same_hash.hashval2.borrow()[p as usize] {
                // Now use the hash that encodes the length and first byte.
                *hhead = h.hash_same_hash.head2.clone();
                *hprev = h.hash_same_hash.prev2.clone();
                *hhashval = h.hash_same_hash.hashval2.clone();
                *hval = h.hash_same_hash.val2;
                *switched_hash = true;
            }
        }
        do_hash_same_hash(h, &mut hhead, &mut hprev, &mut hhashval, &mut hval, &mut switched_hash, bestlength, hpos, p);

        pp = p;
        p = hprev.borrow_mut()[p as usize];
        if p == pp {
            // Uninited prev value.
            break;
        }

        dist += if p < pp { (pp - p) as u32 } else { (WINDOW_SIZE - p as usize + pp as usize) as u32 };

        if MAX_CHAIN_HITS < WINDOW_SIZE {
            chain_counter -= 1;
            if chain_counter <= 0 {
                break;
            }
        }
    }

    if cfg!(feature = "longest-match-cache") {
        store_in_longest_match_cache(s, pos, limit, sublen, bestdist, bestlength);
    }

    assert!(bestlength as usize <= limit);

    *distance = bestdist;
    *length = bestlength;
    assert!(pos + *length as usize <= size);
}

/// Does LZ77 using an algorithm similar to gzip, with lazy matching, rather than
/// with the slow but better "squeeze" implementation.
/// The result is placed in the ZopfliLZ77Store.
/// If instart is larger than 0, it uses values before instart as starting
/// dictionary.
pub fn lz77_greedy(s: &mut BlockState, in_: &[u8], instart: usize, inend: usize, store: &mut LZ77Store) {
    let windowstart: usize = if instart > WINDOW_SIZE { instart - WINDOW_SIZE } else { 0 };

    if instart == inend {
        return;
    }

    let mut hash = Hash::new(WINDOW_SIZE);
    hash::warmup_hash(in_, windowstart, inend, &mut hash);
    for i in windowstart..instart {
        hash::update_hash(in_, i, inend, &mut hash);
    }

    // Lazy matching.
    let mut prev_length: u32 = 0;
    let mut prev_match: u32 = 0;
    let mut match_available: bool = false;
    // End of lazy matching.

    let mut dummysublen: Option<[u16; 259]> = Some([0u16; 259]);
    let mut i: usize = instart;
    while i < inend {
        hash::update_hash(in_, i, inend, &mut hash);

        let mut dist: u16 = 0;
        let mut leng: u16 = 0;
        find_longest_match(s, &hash, in_, i, inend, MAX_MATCH, &mut dummysublen, &mut dist, &mut leng);
        let lengthscore: i32 = get_length_score(leng as i32, dist as i32);

        if cfg!(feature = "lazy-matching") {
            // Lazy matching.
            let prevlengthscore: i32 = get_length_score(prev_length as i32, prev_match as i32);
            if match_available {
                match_available = false;
                if lengthscore > prevlengthscore + 1 {
                    store_litlen_dist(in_[i - 1] as u16, 0, i - 1, store);
                    if lengthscore as usize >= MIN_MATCH && (leng as usize) < MAX_MATCH {
                        match_available = true;
                        prev_length = leng as u32;
                        prev_match = dist as u32;
                        i += 1;
                        continue;
                    }
                } else {
                    // Add previous to output.
                    leng = prev_length as u16;
                    dist = prev_match as u16;
                    // Add to output.
                    verify_len_dist(in_, inend, i - 1, dist, leng);
                    store_litlen_dist(leng, dist, i - 1, store);
                    for _ in 2..leng {
                        assert!(i < inend);
                        i += 1;
                        hash::update_hash(in_, i, inend, &mut hash);
                    }
                    i += 1;
                    continue;
                }
            } else if lengthscore as usize >= MIN_MATCH && (leng as usize) < MAX_MATCH {
                match_available = true;
                prev_length = leng as u32;
                prev_match = dist as u32;
                i += 1;
                continue;
            }
            // End of lazy matching.
        }

        // Add to output.
        if lengthscore as usize >= MIN_MATCH {
            verify_len_dist(in_, inend, i, dist, leng);
            store_litlen_dist(leng, dist, i, store);
        } else {
            leng = 1;
            store_litlen_dist(in_[i] as u16, 0, i, store);
        }
        for _ in 1..leng {
            assert!(i < inend);
            i += 1;
            hash::update_hash(in_, i, inend, &mut hash);
        }
        i += 1;
    }
}

#[cfg(all(feature = "nightly", test))]
mod benches {
    use test::{Bencher, black_box};

    use super::get_match;
    use util::MAX_MATCH;

    #[bench]
    fn bench_get_match(b: &mut Bencher) {
        let x = black_box(0u8);
        let y = black_box(0u8);
        let s = vec![x; MAX_MATCH];
        let m = vec![y; MAX_MATCH];
        b.iter(|| {
            get_match(&s[..], &m[..])
        });
    }
}
