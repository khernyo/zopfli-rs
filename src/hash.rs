use std::cell::RefCell;
use std::iter;
use std::rc::Rc;

use util::{MIN_MATCH, WINDOW_MASK};

pub struct Hash {
    /// Hash value to index of its most recent occurrence.
    pub head: Rc<RefCell<[i32; 65536]>>,
    /// Index to index of prev. occurrence of same hash.
    /// If prev[j] == j, then prev[j] is uninitialized.
    pub prev: Rc<RefCell<Vec<u16>>>,
    /// Index to hash value at this index.
    pub hashval: Rc<RefCell<Vec<i32>>>,
    /// Current hash value.
    pub val: i32,

    pub hash_same_hash: HashSameHash,
    pub hash_same: HashSame,
}

#[cfg(not(feature = "hash-same-hash"))]
pub struct HashSameHash;

#[cfg(feature = "hash-same-hash")]
/// Fields with similar purpose as the above hash, but for the second hash with
/// a value that is calculated differently.
pub struct HashSameHash {
    /// Hash value to index of its most recent occurrence.
    pub head2: Rc<RefCell<[i32; 65536]>>,
    /// Index to index of prev. occurrence of same hash.
    pub prev2: Rc<RefCell<Vec<u16>>>,
    /// Index to hash value at this index.
    pub hashval2: Rc<RefCell<Vec<i32>>>,
    /// Current hash value.
    pub val2: i32,
}

impl HashSameHash {
    #[cfg(not(feature = "hash-same-hash"))]
    fn new(_window_size: usize) -> HashSameHash {
        HashSameHash
    }

    #[cfg(feature = "hash-same-hash")]
    fn new(window_size: usize) -> HashSameHash {
        HashSameHash {
            head2: Rc::new(RefCell::new([-1i32; 65536])),
            prev2: Rc::new(RefCell::new((0..window_size).map(|n| n as u16).collect())),
            hashval2: Rc::new(RefCell::new(iter::repeat(-1i32).take(window_size).collect())),
            val2: 0,
        }
    }
}

#[cfg(not(feature = "hash-same"))]
pub struct HashSame;

#[cfg(feature = "hash-same")]
pub struct HashSame {
    /// Amount of repetitions of same byte after this.
    pub same: Vec<u16>,
}

impl HashSame {
    #[cfg(not(feature = "hash-same"))]
    fn new(_window_size: usize) -> HashSame {
        HashSame
    }

    #[cfg(feature = "hash-same")]
    fn new(window_size: usize) -> HashSame {
        HashSame { same: iter::repeat(0).take(window_size).collect() }
    }
}

const HASH_SHIFT: u32 = 5;
const HASH_MASK: i32 = 32767;

impl Hash {
    pub fn new(window_size: usize) -> Hash {
        Hash {
            head: Rc::new(RefCell::new([-1i32; 65536])),
            prev: Rc::new(RefCell::new((0..window_size).map(|n| n as u16).collect())),
            hashval: Rc::new(RefCell::new(iter::repeat(-1i32).take(window_size).collect())),
            val: 0,
            hash_same: HashSame::new(window_size),
            hash_same_hash: HashSameHash::new(window_size),
        }
    }
}

/// Update the sliding hash value with the given byte. All calls to this function
/// must be made on consecutive input characters. Since the hash value exists out
/// of multiple input bytes, a few warmups with this function are needed initially.
fn update_hash_value(h: &mut Hash, c: u8) {
    h.val = ((h.val << HASH_SHIFT) ^ c as i32) & HASH_MASK;
}

#[cfg(not(feature = "hash-same"))]
fn update_hash_same(_array: &[u8], _pos: usize, _end: usize, _hpos: u16, _h: &mut Hash) { }

#[cfg(feature = "hash-same")]
fn update_hash_same(array: &[u8], pos: usize, end: usize, hpos: u16, h: &mut Hash) {
    let mut amount: usize = 0;
    if h.hash_same.same[pos.wrapping_sub(1) & WINDOW_MASK] > 1 {
        amount = (h.hash_same.same[pos.wrapping_sub(1) & WINDOW_MASK] - 1) as usize;
    }
    while pos + amount + 1 < end && array[pos] == array[(pos + amount + 1)] && amount < !0u16 as usize {
        amount += 1;
    }
    h.hash_same.same[hpos as usize] = amount as u16;
}

#[cfg(not(feature = "hash-same-hash"))]
fn update_hash_same_hash(_hpos: u16, _h: &mut Hash) { }

#[cfg(feature = "hash-same-hash")]
fn update_hash_same_hash(hpos: u16, h: &mut Hash) {
    let mut head2 = h.hash_same_hash.head2.borrow_mut();
    let mut prev2 = h.hash_same_hash.prev2.borrow_mut();
    let mut hashval2 = h.hash_same_hash.hashval2.borrow_mut();
    h.hash_same_hash.val2 = ((h.hash_same.same[hpos as usize] as i32 - MIN_MATCH as i32) & 255) ^ h.val;
    hashval2[hpos as usize] = h.hash_same_hash.val2;
    if head2[h.hash_same_hash.val2 as usize] != -1 && hashval2[head2[h.hash_same_hash.val2 as usize] as usize] == h.hash_same_hash.val2 {
        prev2[hpos as usize] = head2[h.hash_same_hash.val2 as usize] as u16;
    } else {
        prev2[hpos as usize] = hpos;
    }
    head2[h.hash_same_hash.val2 as usize] = hpos as i32;
}

pub fn update_hash(array: &[u8], pos: usize, end: usize, h: &mut Hash) {
    let hpos: u16 = pos as u16 & WINDOW_MASK as u16;
    update_hash_value(h, if pos + MIN_MATCH <= end { array[pos + MIN_MATCH - 1] } else { 0 });

    {
        let mut head = h.head.borrow_mut();
        let mut prev = h.prev.borrow_mut();
        let mut hashval = h.hashval.borrow_mut();
        hashval[hpos as usize] = h.val;
        if head[h.val as usize] != -1 && hashval[head[h.val as usize] as usize] == h.val {
            prev[hpos as usize] = head[h.val as usize] as u16;
        } else {
            prev[hpos as usize] = hpos;
        }
        head[h.val as usize] = hpos as i32;
    }

    update_hash_same(array, pos, end, hpos, h);
    update_hash_same_hash(hpos, h);
}

pub fn warmup_hash(array: &[u8], pos: usize, end: usize, h: &mut Hash) {
    update_hash_value(h, array[pos + 0]);
    if pos + 1 < end {
        update_hash_value(h, array[pos + 1]);
    }
}
