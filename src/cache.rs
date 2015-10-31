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
    sublen: Vec<u8>,
}

impl LongestMatchCache {
    /// Initializes the ZopfliLongestMatchCache.
    pub fn new(blocksize: usize) -> LongestMatchCache {
        // Rather large amount of memory.
        let sublen_size = CACHE_LENGTH * 3 * blocksize;

        // length > 0 and dist 0 is invalid combination, which indicates on purpose
        // that this cache value is not filled in yet.
        LongestMatchCache {
            length: iter::repeat(1).take(blocksize).collect(),
            dist: iter::repeat(0).take(blocksize).collect(),
            sublen: iter::repeat(0).take(sublen_size).collect(),
        }
    }
}

/// Stores sublen array in the cache.
pub unsafe fn sublen_to_cache(sublen: &[u16; 259],
                              pos: usize,
                              length: usize,
                              lmc: &mut LongestMatchCache) {
    if CACHE_LENGTH == 0 {
        return;
    }

    let cache: *mut u8 = &mut lmc.sublen[CACHE_LENGTH * pos * 3];
    if length < 3 {
        return;
    }

    let mut j: usize = 0;
    let mut bestlength: u32 = 0;
    for i in 3..length + 1 {
        if i == length || sublen[i] != sublen[i + 1] {
            *cache.offset(j as isize * 3) = (i - 3) as u8;
            *cache.offset(j as isize * 3 + 1) = (sublen[i] % 256) as u8;
            *cache.offset(j as isize * 3 + 2) = ((sublen[i] >> 8) % 256) as u8;
            bestlength = i as u32;
            j += 1;
            if j >= CACHE_LENGTH {
                break;
            }
        }
    }

    if j < CACHE_LENGTH {
        assert_eq!(bestlength as usize, length);
        *cache.offset((CACHE_LENGTH as isize - 1) * 3) = (bestlength - 3) as u8;
    } else {
        assert!(bestlength as usize <= length,
                "{} <= {}",
                bestlength,
                length);
    }
    assert_eq!(bestlength, max_cached_sublen(lmc, pos, length));
}

/// Extracts sublen array from the cache.
pub unsafe fn cache_to_sublen(lmc: *mut LongestMatchCache,
                              pos: usize,
                              length: usize,
                              sublen: &mut [u16; 259]) {
    if CACHE_LENGTH == 0 {
        return;
    }

    if length < 3 {
        return;
    }
    let cache: *mut u8 = &mut (*lmc).sublen[CACHE_LENGTH * pos * 3];
    let maxlength: u32 = max_cached_sublen(lmc, pos, length);
    let mut prevlength: u32 = 0;
    for j in 0..CACHE_LENGTH {
        let length: u32 = *cache.offset(j as isize * 3) as u32 + 3;
        let dist: u32 = *cache.offset(j as isize * 3 + 1) as u32 +
                        256 * *cache.offset(j as isize * 3 + 2) as u32;
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
pub unsafe fn max_cached_sublen(lmc: *const LongestMatchCache, pos: usize, _length: usize) -> u32 {
    if CACHE_LENGTH == 0 {
        return 0;
    }
    let cache: *const u8 = &(*lmc).sublen[CACHE_LENGTH * pos * 3];
    if *cache.offset(1) == 0 && *cache.offset(2) == 0 {
        // No sublen cached.
        return 0;
    }
    *cache.offset(((CACHE_LENGTH - 1) * 3) as isize) as u32 + 3
}
