#![cfg(feature = "longest-match-cache")]

//! The cache that speeds up ZopfliFindLongestMatch of lz77.c.

use std::iter;

use util::CACHE_LENGTH;

/// Cache used by ZopfliFindLongestMatch to remember previously found length/dist values.
/// This is needed because the squeeze runs will ask these values multiple times for the
/// same position. Uses large amounts of memory, since it has to remember the distance
/// belonging to every possible shorter-than-the-best length (the so called "sublen" array).
pub struct LongestMatchCache {
    pub length: Vec<u16>,
    pub dist: Vec<u16>,
    sublen: Vec<[u8; CACHE_LENGTH * 3]>,
}

impl LongestMatchCache {
    /// Initializes the ZopfliLongestMatchCache.
    pub fn new(blocksize: usize) -> LongestMatchCache {
        // length > 0 and dist 0 is invalid combination, which indicates on purpose
        // that this cache value is not filled in yet.
        LongestMatchCache {
            length: iter::repeat(1).take(blocksize).collect(),
            dist: iter::repeat(0).take(blocksize).collect(),
            // Rather large amount of memory.
            sublen: iter::repeat([0; CACHE_LENGTH * 3]).take(blocksize).collect(),
        }
    }
}

/// Stores sublen array in the cache.
pub fn sublen_to_cache(sublen: &[u16; 259],
                       pos: usize,
                       length: usize,
                       lmc: &mut LongestMatchCache) {
    if CACHE_LENGTH == 0 {
        return;
    }

    let mut bestlength: u32 = 0;
    {
        let cache: &mut [u8; CACHE_LENGTH * 3] = &mut lmc.sublen[pos];
        if length < 3 {
            return;
        }

        let mut j: usize = 0;
        for i in 3..length + 1 {
            if i == length || sublen[i] != sublen[i + 1] {
                cache[j * 3] = (i - 3) as u8;
                cache[j * 3 + 1] = (sublen[i] % 256) as u8;
                cache[j * 3 + 2] = ((sublen[i] >> 8) % 256) as u8;
                bestlength = i as u32;
                j += 1;
                if j >= CACHE_LENGTH {
                    break;
                }
            }
        }

        if j < CACHE_LENGTH {
            assert_eq!(bestlength as usize, length);
            cache[(CACHE_LENGTH - 1) * 3] = (bestlength - 3) as u8;
        } else {
            assert!(bestlength as usize <= length,
                    "{} <= {}",
                    bestlength,
                    length);
        }
    }
    assert_eq!(bestlength, max_cached_sublen(lmc, pos, length));
}

/// Extracts sublen array from the cache.
pub fn cache_to_sublen(lmc: &mut LongestMatchCache,
                       pos: usize,
                       length: usize,
                       sublen: &mut [u16; 259]) {
    if CACHE_LENGTH == 0 {
        return;
    }

    if length < 3 {
        return;
    }
    let maxlength: u32 = max_cached_sublen(lmc, pos, length);
    let cache: &mut [u8; CACHE_LENGTH * 3] = &mut (*lmc).sublen[pos];
    let mut prevlength: u32 = 0;
    for j in 0..CACHE_LENGTH {
        let length: u32 = cache[j * 3] as u32 + 3;
        let dist: u32 = cache[j * 3 + 1] as u32 + 256 * cache[j * 3 + 2] as u32;
        for i in prevlength..length + 1 {
            sublen[i as usize] = dist as u16;
        }
        if length == maxlength {
            break;
        }
        prevlength = length + 1;
    }
}

/// Returns the length up to which could be stored in the cache.
pub fn max_cached_sublen(lmc: &LongestMatchCache, pos: usize, _length: usize) -> u32 {
    if CACHE_LENGTH == 0 {
        return 0;
    }
    let cache: &[u8; CACHE_LENGTH * 3] = &lmc.sublen[pos];
    if cache[1] == 0 && cache[2] == 0 {
        // No sublen cached.
        return 0;
    }
    cache[(CACHE_LENGTH - 1) * 3] as u32 + 3
}
