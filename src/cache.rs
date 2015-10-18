#![cfg(feature = "longest-match-cache")]

//! The cache that speeds up ZopfliFindLongestMatch of lz77.c.

use std::mem::size_of;
use std::ptr::null_mut;

use libc::funcs::c95::stdlib::{free, malloc};
use libc::{c_void, size_t};

use util::CACHE_LENGTH;

/// Cache used by ZopfliFindLongestMatch to remember previously found length/dist values.
/// This is needed because the squeeze runs will ask these values multiple times for the same position.
/// Uses large amounts of memory, since it has to remember the distance belonging
/// to every possible shorter-than-the-best length (the so called "sublen" array).
pub struct LongestMatchCache {
    pub length: *mut u16,
    pub dist: *mut u16,
    sublen: *mut u8,
}

impl LongestMatchCache {
    /// Initializes the ZopfliLongestMatchCache.
    pub unsafe fn new(blocksize: usize) -> *mut LongestMatchCache {
        let length: *mut u16 = malloc((size_of::<u16>() * blocksize) as size_t) as *mut u16;
        let dist: *mut u16 = malloc((size_of::<u16>() * blocksize) as size_t) as *mut u16;

        // Rather large amount of memory.
        let sublen_size = (CACHE_LENGTH * 3 * blocksize) as size_t;
        let sublen: *mut u8 = malloc(sublen_size) as *mut u8;
        if sublen == null_mut() {
            panic!("Error: Out of memory. Tried allocating {} bytes of memory.", sublen_size);
        }

        // length > 0 and dist 0 is invalid combination, which indicates on purpose
        // that this cache value is not filled in yet.
        for i in 0..blocksize {
            *length.offset(i as isize) = 1;
        }
        for i in 0..blocksize {
            *dist.offset(i as isize) = 0;
        }
        for i in 0..sublen_size {
            *sublen.offset(i as isize) = 0;
        }
        let lmc: *mut LongestMatchCache = malloc(size_of::<LongestMatchCache>() as size_t) as *mut LongestMatchCache;
        (*lmc).length = length;
        (*lmc).dist = dist;
        (*lmc).sublen = sublen;
        lmc
    }
}

/// Frees up the memory of the ZopfliLongestMatchCache.
pub unsafe fn clean_cache(lmc: *mut LongestMatchCache) {
    free((*lmc).length as *mut c_void);
    free((*lmc).dist as *mut c_void);
    free((*lmc).sublen as *mut c_void);
}

/// Stores sublen array in the cache.
pub unsafe fn sublen_to_cache(sublen: *const u16, pos: usize, length: usize, lmc: *mut LongestMatchCache) {
    if CACHE_LENGTH == 0 {
        return;
    }

    let cache: *mut u8 = (*lmc).sublen.offset((CACHE_LENGTH * pos * 3) as isize);
    if length < 3 {
        return;
    }

    let mut j: usize = 0;
    let mut bestlength: u32 = 0;
    for i in 3..length+1 {
        if i == length || *sublen.offset(i as isize) != *sublen.offset(i as isize + 1) {
            *cache.offset(j as isize * 3) = (i - 3) as u8;
            *cache.offset(j as isize * 3 + 1) = (*sublen.offset(i as isize) % 256) as u8;
            *cache.offset(j as isize * 3 + 2) = ((*sublen.offset(i as isize) >> 8) % 256) as u8;
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
        assert!(bestlength as usize <= length, "{} <= {}", bestlength, length);
    }
    assert_eq!(bestlength, max_cached_sublen(lmc, pos, length));
}

/// Extracts sublen array from the cache.
pub unsafe fn cache_to_sublen(lmc: *const LongestMatchCache, pos: usize, length: usize, sublen: *mut u16) {
    if CACHE_LENGTH == 0 {
        return;
    }

    if length < 3 {
        return;
    }
    let cache: *mut u8 = (*lmc).sublen.offset((CACHE_LENGTH * pos * 3) as isize);
    let maxlength: u32 = max_cached_sublen(lmc, pos, length);
    let mut prevlength: u32 = 0;
    for j in 0..CACHE_LENGTH {
        let length: u32 = *cache.offset(j as isize * 3) as u32 + 3;
        let dist: u32 = *cache.offset(j as isize * 3 + 1) as u32 + 256 * *cache.offset(j as isize * 3 + 2) as u32;
        for i in prevlength..length+1 {
            *sublen.offset(i as isize) = dist as u16;
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
    let cache: *const u8 = (*lmc).sublen.offset((CACHE_LENGTH * pos * 3) as isize);
    if *cache.offset(1) == 0 && *cache.offset(2) == 0 {
        // No sublen cached.
        return 0;
    }
    *cache.offset(((CACHE_LENGTH - 1) * 3) as isize) as u32 + 3
}
