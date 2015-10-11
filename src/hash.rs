use std::mem::{size_of_val, transmute};
use std::ptr::null_mut;

use libc::funcs::c95::stdlib::{free, malloc};
use libc::{c_void, size_t};

use util::{MIN_MATCH, WINDOW_MASK};

struct Hash {
    /// Hash value to index of its most recent occurrence.
    head: *mut i32,
    /// Index to index of prev. occurrence of same hash.
    prev: *mut u16,
    /// Index to hash value at this index.
    hashval: *mut i32,
    /// Current hash value.
    val: i32,

    hash_same_hash: HashSameHash,
    hash_same: HashSame,
}

#[cfg(not(feature = "hash-same-hash"))]
struct HashSameHash;

#[cfg(feature = "hash-same-hash")]
/// Fields with similar purpose as the above hash, but for the second hash with
/// a value that is calculated differently.
struct HashSameHash {
    /// Hash value to index of its most recent occurrence.
    head2: *mut i32,
    /// Index to index of prev. occurrence of same hash.
    prev2: *mut u16,
    /// Index to hash value at this index.
    hashval2: *mut i32,
    /// Current hash value.
    val2: i32,
}

impl HashSameHash {
    #[cfg(not(feature = "hash-same-hash"))]
    fn new(window_size: usize) -> HashSameHash {
        HashSameHash
    }

    #[cfg(feature = "hash-same-hash")]
    unsafe fn new(window_size: usize) -> HashSameHash {
        let mut head2: *mut i32 = null_mut();
        head2 = transmute(malloc(size_of_val(&*head2) as size_t * 65536));
        let mut prev2: *mut u16 = null_mut();
        prev2 = transmute(malloc((size_of_val(&*prev2) * window_size) as size_t));
        let mut hashval2: *mut i32 = null_mut();
        hashval2 = transmute(malloc((size_of_val(&*hashval2) * window_size) as size_t));
        for i in 0..65536 {
            *head2.offset(i) = -1;
        }
        for i in 0..window_size {
            *prev2.offset(i as isize) = i as u16;
            *hashval2.offset(i as isize) = -1;
        }

        HashSameHash {
            head2: head2,
            prev2: prev2,
            hashval2: hashval2,
            val2: 0,
        }
    }

    #[cfg(not(feature = "hash-same-hash"))]
    fn clean(h: *const HashSameHash) { }

    #[cfg(feature = "hash-same-hash")]
    unsafe fn clean(h: *const HashSameHash) {
        free((*h).head2 as *mut c_void);
        free((*h).prev2 as *mut c_void);
        free((*h).hashval2 as *mut c_void);
    }
}

#[cfg(not(feature = "hash-same"))]
struct HashSame;

#[cfg(feature = "hash-same")]
struct HashSame {
    /// Amount of repetitions of same byte after this.
    same: *mut u16,
}

impl HashSame {
    #[cfg(not(feature = "hash-same"))]
    fn new(window_size: usize) -> HashSame {
        HashSame
    }

    #[cfg(feature = "hash-same")]
    unsafe fn new(window_size: usize) -> HashSame {
        let mut same: *mut u16 = null_mut();
        same = transmute(malloc((size_of_val(&*same) * window_size) as size_t));
        for i in 0..window_size {
            *same.offset(i as isize) = 0;
        }
        HashSame {
            same: same
        }
    }

    #[cfg(not(feature = "hash-same"))]
    fn clean(h: *const HashSame) { }

    #[cfg(feature = "hash-same")]
    unsafe fn clean(h: *const HashSame) {
        free((*h).same as *mut c_void);
    }
}

const HASH_SHIFT: u32 = 5;
const HASH_MASK: i32 = 32767;

impl Hash {
    unsafe fn new(window_size: usize) -> Hash {
        let mut head: *mut i32 = null_mut();
        head = transmute(malloc(size_of_val(&*head) as size_t * 65536));
        let mut prev: *mut u16 = null_mut();
        prev = transmute(malloc((size_of_val(&*prev) * window_size) as size_t));
        let mut hashval: *mut i32 = null_mut();
        hashval = transmute(malloc((size_of_val(&*hashval) * window_size) as size_t));

        for i in 0..65536 {
            // -1 indicates no head so far.
            *head.offset(i) = -1;
        }
        for i in 0..window_size {
            // If prev[j] == j, then prev[j] is uninitialized.
            *prev.offset(i as isize) = i as u16;
            *hashval.offset(i as isize) = -1;
        }

        Hash {
            head: head,
            prev: prev,
            hashval: hashval,
            val: 0,
            hash_same: HashSame::new(window_size),
            hash_same_hash: HashSameHash::new(window_size),
        }
    }

    unsafe fn clean(h: *mut Hash) {
        free((*h).head as *mut c_void);
        free((*h).prev as *mut c_void);
        free((*h).hashval as *mut c_void);

        HashSameHash::clean(&(*h).hash_same_hash as *const _);
        HashSame::clean(&(*h).hash_same as *const _);
    }
}

/// Update the sliding hash value with the given byte. All calls to this function
/// must be made on consecutive input characters. Since the hash value exists out
/// of multiple input bytes, a few warmups with this function are needed initially.
unsafe fn update_hash_value(h: *mut Hash, c: u8) {
    (*h).val = (((*h).val << HASH_SHIFT) ^ c as i32) & HASH_MASK;
}

#[cfg(not(feature = "hash-same"))]
fn update_hash_same(array: *const u8, pos: usize, end: usize, hpos: u16, h: *mut Hash) { }

#[cfg(feature = "hash-same")]
unsafe fn update_hash_same(array: *const u8, pos: usize, end: usize, hpos: u16, h: *mut Hash) {
    let mut amount: usize = 0;
    if *(*h).hash_same.same.offset(((pos - 1) & WINDOW_MASK) as isize) > 1 {
        amount = (*(*h).hash_same.same.offset(((pos - 1) & WINDOW_MASK) as isize) - 1) as usize;
    }
    while pos + amount + 1 < end && *array.offset(pos as isize) == *array.offset((pos + amount + 1) as isize) && amount < (-1 as u16) as usize {
        amount += 1;
    }
    *(*h).hash_same.same.offset(hpos as isize) = amount as u16;
}

#[cfg(not(feature = "hash-same-hash"))]
fn update_hash_same_hash(array: *const u8, pos: usize, end: usize, hpos: u16, h: *mut Hash) { }

#[cfg(feature = "hash-same-hash")]
unsafe fn update_hash_same_hash(array: *const u8, pos: usize, end: usize, hpos: u16, h: *mut Hash) {
    (*h).hash_same_hash.val2 = (((*(*h).hash_same.same.offset(hpos as isize) - MIN_MATCH as u16) & 255) ^ (*h).val as u16) as i32;
    *(*h).hash_same_hash.hashval2.offset(hpos as isize) = (*h).hash_same_hash.val2;
    if *(*h).hash_same_hash.head2.offset((*h).hash_same_hash.val2 as isize) != -1 && *(*h).hash_same_hash.hashval2.offset(*(*h).hash_same_hash.head2.offset((*h).hash_same_hash.val2 as isize) as isize) == (*h).hash_same_hash.val2 {
        *(*h).hash_same_hash.prev2.offset(hpos as isize) = *(*h).hash_same_hash.head2.offset((*h).hash_same_hash.val2 as isize) as u16;
    } else {
        *(*h).hash_same_hash.prev2.offset(hpos as isize) = hpos;
    }
    *(*h).hash_same_hash.head2.offset((*h).hash_same_hash.val2 as isize) = hpos as i32;
}

unsafe fn update_hash(array: *const u8, pos: usize, end: usize, h: *mut Hash) {
    let hpos: u16 = pos as u16 & WINDOW_MASK as u16;
    update_hash_value(h, if pos + MIN_MATCH <= end { *array.offset(pos as isize + MIN_MATCH as isize - 1) } else { 0 });
    *(*h).hashval.offset(hpos as isize) = (*h).val;
    if *(*h).head.offset((*h).val as isize) != -1 && *(*h).hashval.offset(*(*h).head.offset((*h).val as isize) as isize) == (*h).val {
        *(*h).prev.offset(hpos as isize) = *(*h).head.offset((*h).val as isize) as u16;
    } else {
        *(*h).prev.offset(hpos as isize) = hpos;
    }
    *(*h).head.offset((*h).val as isize) = hpos as i32;

    update_hash_same(array, pos, end, hpos, h);
    update_hash_same_hash(array, pos, end, hpos, h);
}

unsafe fn warmup_hash(array: *const u8, pos: usize, end: usize, h: *mut Hash) {
    update_hash_value(h, *array.offset(pos as isize + 0));
    update_hash_value(h, *array.offset(pos as isize + 1));
}