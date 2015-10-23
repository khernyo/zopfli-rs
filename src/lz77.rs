//! Functions for basic LZ77 compression and utilities for the "squeeze" LZ77
//! compression.

use std;
use std::mem::{size_of, size_of_val, uninitialized};
use std::ptr::{null, null_mut};

use libc::funcs::c95::stdlib::{free, malloc};
use libc::{c_void, size_t};

#[cfg(feature = "longest-match-cache")]
use super::cache;
#[cfg(feature = "longest-match-cache")]
use cache::LongestMatchCache;

use super::hash;
use super::util;
use super::Options;

use hash::Hash;
use util::{MIN_MATCH, MAX_MATCH, MAX_CHAIN_HITS, WINDOW_MASK, WINDOW_SIZE};

/// Stores lit/length and dist pairs for LZ77.
/// Parameter litlens: Contains the literal symbols or length values.
/// Parameter dists: Contains the distances. A value is 0 to indicate that there is
/// no dist and the corresponding litlens value is a literal instead of a length.
/// Parameter size: The size of both the litlens and dists arrays.
/// The memory can best be managed by using ZopfliInitLZ77Store to initialize it,
/// ZopfliCleanLZ77Store to destroy it, and ZopfliStoreLitLenDist to append values.
pub struct LZ77Store {
    /// Lit or len.
    pub litlens: *mut u16,
    /// If 0: indicates literal in corresponding litlens,
    /// if > 0: length in corresponding litlens, this is the distance.
    pub dists: *mut u16,
    pub size: usize,
}

impl LZ77Store {
    pub fn new() -> LZ77Store {
        LZ77Store {
            litlens: null_mut(),
            dists: null_mut(),
            size: 0,
        }
    }

    pub unsafe fn init(store: *mut LZ77Store) {
        (*store).litlens = null_mut();
        (*store).dists = null_mut();
        (*store).size = 0;
    }

    pub unsafe fn clean(store: *mut LZ77Store) {
        free((*store).litlens as *mut c_void);
        free((*store).dists as *mut c_void);
    }
}

/// Some state information for compressing a block.
/// This is currently a bit under-used (with mainly only the longest match cache),
/// but is kept for easy future expansion.
pub struct BlockState {
    pub options: *const Options,

    /// Cache for length/distance pairs found so far.
    #[cfg(feature = "longest-match-cache")]
    pub lmc: *mut LongestMatchCache,

    /// The start (inclusive) and end (not inclusive) of the current block.
    pub blockstart: usize,
    pub blockend: usize,
}

impl BlockState {
    #[cfg(feature = "longest-match-cache")]
    pub fn new(options: *const Options, blockstart: usize, blockend: usize, lmc: *mut LongestMatchCache) -> BlockState {
        BlockState {
            options: options,
            blockstart: blockstart,
            blockend: blockend,
            lmc: lmc,
        }
    }

    #[cfg(not(feature = "longest-match-cache"))]
    pub fn new(options: *const Options, blockstart: usize, blockend: usize, lmc: *mut ()) -> BlockState {
        BlockState {
            options: options,
            blockstart: blockstart,
            blockend: blockend,
        }
    }
}

pub unsafe fn clean_lz77_store(store: *mut LZ77Store) {
    free((*store).litlens as *mut c_void);
    free((*store).dists as *mut c_void);
}

pub unsafe fn copy_lz77_store(source: *const LZ77Store, dest: *mut LZ77Store) {
    clean_lz77_store(dest);
    (*dest).litlens = malloc((size_of_val(&*(*dest).litlens) * (*source).size) as size_t) as *mut u16;
    (*dest).dists = malloc((size_of_val(&*(*dest).dists) * (*source).size) as size_t) as *mut u16;

    if (*dest).litlens == null_mut() || (*dest).dists == null_mut() {
        // Allocation failed.
        std::process::exit(-1);
    }

    (*dest).size = (*source).size;
    for i in 0..(*source).size {
        *(*dest).litlens.offset(i as isize) = *(*source).litlens.offset(i as isize);
        *(*dest).dists.offset(i as isize) = *(*source).dists.offset(i as isize);
    }
}

/// Appends the length and distance to the LZ77 arrays of the ZopfliLZ77Store.
/// context must be a ZopfliLZ77Store*.
pub unsafe fn store_litlen_dist(length: u16, dist: u16, store: *mut LZ77Store) {
    // Needed for using ZOPFLI_APPEND_DATA twice.
    let mut size2: usize = (*store).size;
    append_data!(length, (*store).litlens, (*store).size);
    append_data!(dist, (*store).dists, size2);
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
pub unsafe fn verify_len_dist(data: *const u8, datasize: usize, pos: usize, dist: u16, length: u16) {
    /* TODO(lode): make this only run in a debug compile, it's for assert only. */

    assert!(pos + length as usize <= datasize);
    for i in 0..length {
        if *data.offset(pos as isize - dist as isize + i as isize) != *data.offset(pos as isize + i as isize) {
            assert_eq!(*data.offset(pos as isize - dist as isize + i as isize), *data.offset(pos as isize + i as isize));
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
unsafe fn get_match(scan: *const u8, match_: *const u8, end: *const u8, safe_end: *const u8) -> *const u8 {
    let mut scan = scan;
    let mut match_ = match_;
    if size_of::<size_t>() == 8 {
        // 8 checks at once per array bounds check (size_t is 64-bit).
        while scan < safe_end && *(scan as *const size_t) == *(match_ as *const size_t) {
            scan = scan.offset(8);
            match_ = match_.offset(8);
        }
    } else if size_of::<u32>() == 4 {
        // 4 checks at once per array bounds check (unsigned int is 32-bit).
        while scan < safe_end && *(scan as *const u32) == *(match_ as *const u32) {
            scan = scan.offset(4);
            match_ = match_.offset(4);
        }
    } else {
        // do 8 checks at once per array bounds check.
        while scan < safe_end && *scan == *match_ && *(scan.offset(1)) == *(match_.offset(1))
            && *(scan.offset(2)) == *(match_.offset(2)) && *(scan.offset(3)) == *(match_.offset(3))
            && *(scan.offset(4)) == *(match_.offset(4)) && *(scan.offset(5)) == *(match_.offset(5))
            && *(scan.offset(6)) == *(match_.offset(6)) && *(scan.offset(7)) == *(match_.offset(7)) {
                scan = scan.offset(8);
                match_ = scan.offset(8);
            }
    }

    // The remaining few bytes.
    while scan != end && *scan == *match_ {
        scan = scan.offset(1);
        match_ = scan.offset(1);
    }

    scan
}

#[cfg(not(feature = "longest-match-cache"))]
fn try_get_from_longest_match_cache(s: *const BlockState, pos: usize, limit: *mut usize, sublen: *mut u16, distance: *mut u16, length: *mut u16) -> bool {
    false
}

/// Gets distance, length and sublen values from the cache if possible.
/// Returns 1 if it got the values from the cache, 0 if not.
/// Updates the limit value to a smaller one if possible with more limited
/// information from the cache.
#[cfg(feature = "longest-match-cache")]
unsafe fn try_get_from_longest_match_cache(s: *const BlockState, pos: usize, limit: *mut usize, sublen: *mut u16, distance: *mut u16, length: *mut u16) -> bool {
    // The LMC cache starts at the beginning of the block rather than the
    // beginning of the whole array.
    let lmcpos: isize = pos as isize - (*s).blockstart as isize;

    // Length > 0 and dist 0 is invalid combination, which indicates on purpose
    // that this cache value is not filled in yet.
    let cache_available: bool = (*s).lmc != null_mut() && (*(*(*s).lmc).length.offset(lmcpos) == 0 || *(*(*s).lmc).dist.offset(lmcpos) != 0);
    let limit_of_for_cache: bool = cache_available && (*limit == MAX_MATCH || *(*(*s).lmc).length.offset(lmcpos) <= *limit as u16 || (sublen != null_mut() && cache::max_cached_sublen((*s).lmc, lmcpos as usize, *(*(*s).lmc).length.offset(lmcpos) as usize) >= *limit as u32));

    if (*s).lmc != null_mut() && limit_of_for_cache && cache_available {
        if sublen == null_mut() || *(*(*s).lmc).length.offset(lmcpos) <= cache::max_cached_sublen((*s).lmc, lmcpos as usize, *(*(*s).lmc).length.offset(lmcpos) as usize) as u16 {
            *length = *(*(*s).lmc).length.offset(lmcpos);
            if *length > *limit as u16 {
                *length = *limit as u16;
            }
            if sublen != null_mut() {
                cache::cache_to_sublen((*s).lmc, lmcpos as usize, *length as usize, sublen);
                *distance = *sublen.offset(*length as isize);
                if *limit == MAX_MATCH && *length >= MIN_MATCH as u16 {
                    assert_eq!(*sublen.offset(*length as isize), *(*(*s).lmc).dist.offset(lmcpos));
                }
            } else {
                *distance = *(*(*s).lmc).dist.offset(lmcpos);
            }
            return true;
        }
        // Can't use much of the cache, since the "sublens" need to be calculated,
        // but at  least we already know when to stop.
        *limit = *(*(*s).lmc).length.offset(lmcpos) as usize;
    }
    false
}

#[cfg(not(feature = "longest-match-cache"))]
fn store_in_longest_match_cache(s: *const BlockState, pos: usize, limit: usize, sublen: *const u16, distance: u16, length: u16) { }

/// Stores the found sublen, distance and length in the longest match cache, if
/// possible.
#[cfg(feature = "longest-match-cache")]
unsafe fn store_in_longest_match_cache(s: *const BlockState, pos: usize, limit: usize, sublen: *const u16, distance: u16, length: u16) {
    // The LMC cache starts at the beginning of the block rather than the
    // beginning of the whole array.
    let lmcpos: isize = pos as isize - (*s).blockstart as isize;

    // Length > 0 and dist 0 is invalid combination, which indicates on purpose
    // that this cache value is not filled in yet.
    let cache_available: bool = (*s).lmc != null_mut() && (*(*(*s).lmc).length.offset(lmcpos) == 0 || *(*(*s).lmc).dist.offset(lmcpos) != 0);

    if (*s).lmc != null_mut() && limit == MAX_MATCH && sublen != null() && !cache_available {
        assert_eq!(*(*(*s).lmc).length.offset(lmcpos), 1);
        assert_eq!(*(*(*s).lmc).dist.offset(lmcpos), 0);
        *(*(*s).lmc).dist.offset(lmcpos) = if length < MIN_MATCH as u16 { 0 } else { distance };
        *(*(*s).lmc).length.offset(lmcpos) = if length < MIN_MATCH as u16 { 0 } else { length };
        assert!(!(*(*(*s).lmc).length.offset(lmcpos) == 1 && *(*(*s).lmc).dist.offset(lmcpos) == 0));
        cache::sublen_to_cache(sublen, lmcpos as usize, length as usize, (*s).lmc);
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
pub unsafe fn find_longest_match(s: *const BlockState, h: *const Hash, array: *const u8, pos: usize, size: usize, limit: usize, sublen: *mut u16, distance: *mut u16, length: *mut u16) {
    let mut limit = limit;

    let hpos: u16 = (pos & WINDOW_MASK) as u16;
    let mut bestdist: u16 = 0;
    let mut bestlength: u16 = 1;

    // For quitting early.
    let mut chain_counter = MAX_CHAIN_HITS;

    let mut hhead: *const i32 = (*h).head;
    let mut hprev: *const u16 = (*h).prev;
    let mut hhashval: *const i32 = (*h).hashval;
    let mut hval: i32 = (*h).val;

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
    let arrayend: *const u8 = array.offset(pos as isize).offset(limit as isize);
    let arrayend_safe: *const u8 = arrayend.offset(-8);

    assert!(hval < 65536);

    // During the whole loop, p == hprev[pp].
    let mut pp: u16 = *hhead.offset(hval as isize) as u16;
    let mut p: u16 = *hprev.offset(pp as isize);

    assert_eq!(pp, hpos);

    // Not unsigned short on purpose.
    let mut dist: u32 = if p < pp { pp as u32 - p as u32 } else { (WINDOW_SIZE - p as usize + pp as usize) as u32 };

    // Go through all distances.
    while (dist as usize) < WINDOW_SIZE {
        let mut currentlength: u16 = 0;

        assert!((p as usize) < WINDOW_SIZE);
        assert_eq!(p, *hprev.offset(pp as isize));
        assert_eq!(*hhashval.offset(p as isize), hval);

        if dist > 0 {
            assert!(pos < size);
            assert!(dist as usize <= pos);
            let mut scan: *const u8 = array.offset(pos as isize);
            let mut match_: *const u8 = array.offset((pos - dist as usize) as isize);

            // Testing the byte at position bestlength first, goes slightly faster.
            if pos + bestlength as usize >= size || *scan.offset(bestlength as isize) == *match_.offset(bestlength as isize) {
                #[cfg(not(feature = "hash-same"))]
                fn do_hash_same(h: *const Hash, pos: usize, limit: usize, scan: *mut *const u8, match_: *mut *const u8, dist: u32) {}

                #[cfg(feature = "hash-same")]
                unsafe fn do_hash_same(h: *const Hash, pos: usize, limit: usize, scan: *mut *const u8, match_: *mut *const u8, dist: u32) {
                    let same0: u16 = *(*h).hash_same.same.offset((pos & WINDOW_MASK) as isize);
                    if same0 > 2 && **scan == **match_ {
                        let same1: u16 = *(*h).hash_same.same.offset(((pos - dist as usize) & WINDOW_MASK) as isize);
                        let mut same: u16 = if same0 < same1 { same0 } else { same1 };
                        if same as usize > limit {
                            same = limit as u16;
                        }
                        *scan = (*scan).offset(same as isize);
                        *match_ = (*match_).offset(same as isize);
                    }
                }
                do_hash_same(h, pos, limit, &mut scan, &mut match_, dist);

                scan = get_match(scan, match_, arrayend, arrayend_safe);
                // The found length.
                currentlength = (scan as usize - array.offset(pos as isize) as usize) as u16;
            }

            if currentlength > bestlength {
                if !sublen.is_null() {
                    for j in bestlength+1..currentlength+1 {
                        *sublen.offset(j as isize) = dist as u16;
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
        fn do_hash_same_hash(h: *const Hash, hhead: *mut *const i32, hprev: *mut *const u16, hhashval: *mut *const i32, hval: *mut i32, bestlength: u16, hpos: u16, p: u16) { }

        #[cfg(feature = "hash-same-hash")]
        unsafe fn do_hash_same_hash(h: *const Hash, hhead: *mut *const i32, hprev: *mut *const u16, hhashval: *mut *const i32, hval: *mut i32, bestlength: u16, hpos: u16, p: u16) {
            // Switch to the other hash once this will be more efficient.
            if *hhead != (*h).hash_same_hash.head2 && bestlength >= *(*h).hash_same.same.offset(hpos as isize) && (*h).hash_same_hash.val2 == *(*h).hash_same_hash.hashval2.offset(p as isize) {
                // Now use the hash that encodes the length and first byte.
                *hhead = (*h).hash_same_hash.head2;
                *hprev = (*h).hash_same_hash.prev2;
                *hhashval = (*h).hash_same_hash.hashval2;
                *hval = (*h).hash_same_hash.val2;
            }
        }
        do_hash_same_hash(h, &mut hhead, &mut hprev, &mut hhashval, &mut hval, bestlength, hpos, p);

        pp = p;
        p = *hprev.offset(p as isize);
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
pub unsafe fn lz77_greedy(s: *const BlockState, in_: *const u8, instart: usize, inend: usize, store: *mut LZ77Store) {
    let windowstart: usize = if instart > WINDOW_SIZE { instart - WINDOW_SIZE } else { 0 };
    let mut dummysublen_array: [u16; 259] = uninitialized();
    let dummysublen = dummysublen_array.as_mut_ptr();

    if instart == inend {
        return;
    }

    let mut hash = Hash::new(WINDOW_SIZE);
    let h: *mut Hash = &mut hash;
    hash::warmup_hash(in_, windowstart, inend, h);
    for i in windowstart..instart {
        hash::update_hash(in_, i, inend, h);
    }

    // Lazy matching.
    let mut prev_length: u32 = 0;
    let mut prev_match: u32 = 0;
    let mut match_available: bool = false;
    // End of lazy matching.

    let mut i: usize = instart;
    while i < inend {
        hash::update_hash(in_, i, inend, h);

        let mut dist: u16 = 0;
        let mut leng: u16 = 0;
        find_longest_match(s, h, in_, i, inend, MAX_MATCH, dummysublen, &mut dist, &mut leng);
        let lengthscore: i32 = get_length_score(leng as i32, dist as i32);

        if cfg!(feature = "lazy-matching") {
            // Lazy matching.
            let prevlengthscore: i32 = get_length_score(prev_length as i32, prev_match as i32);
            if match_available {
                match_available = false;
                if lengthscore > prevlengthscore + 1 {
                    store_litlen_dist(*in_.offset(i as isize - 1) as u16, 0, store);
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
                    store_litlen_dist(leng, dist, store);
                    for _ in 2..leng {
                        assert!(i < inend);
                        i += 1;
                        hash::update_hash(in_, i, inend, h);
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
            store_litlen_dist(leng, dist, store);
        } else {
            leng = 1;
            store_litlen_dist(*in_.offset(i as isize) as u16, 0, store);
        }
        for _ in 1..leng {
            assert!(i < inend);
            i += 1;
            hash::update_hash(in_, i, inend, h);
        }
        i += 1;
    }

    hash::Hash::clean(h);
}

/**
 * Counts the number of literal, length and distance symbols in the given lz77
 * arrays.
 * litlens: lz77 lit/lengths
 * dists: ll77 distances
 * start: where to begin counting in litlens and dists
 * end: where to stop counting in litlens and dists (not inclusive)
 * ll_count: count of each lit/len symbol, must have size 288 (see deflate
 *     standard)
 * d_count: count of each dist symbol, must have size 32 (see deflate standard)
 */
pub unsafe fn lz77_counts(litlens: *const u16, dists: *const u16, start: usize, end: usize, ll_count: *mut usize, d_count: *mut usize) {
    for i in 0..288 {
        *ll_count.offset(i) = 0;
    }
    for i in 0..32 {
        *d_count.offset(i) = 0;
    }

    for i in start..end {
        if *dists.offset(i as isize) == 0 {
            *ll_count.offset(*litlens.offset(i as isize) as isize) += 1;
        } else {
            *ll_count.offset(util::get_length_symbol(*litlens.offset(i as isize) as i32) as isize) += 1;
            *d_count.offset(util::get_dist_symbol(*dists.offset(i as isize) as i32) as isize) += 1;
        }
    }

    // End symbol.
    *ll_count.offset(256) = 1;
}
