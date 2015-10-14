
use std::mem;

use libc::{c_void, size_t};
use libc::funcs::c95::stdlib::{free, malloc};

unsafe fn lengths_to_symbols(lengths: *const u32, n: usize, maxbits: u32, symbols: *mut u32) {
    let bl_count: *mut size_t = malloc((mem::size_of::<size_t>() * (maxbits as usize + 1)) as size_t) as *mut size_t;
    let next_code: *mut size_t = malloc((mem::size_of::<size_t>() * (maxbits as usize + 1)) as size_t) as *mut size_t;

    for i in 0..n {
        *symbols.offset(i as isize) = 0;
    }

    // 1) Count the number of codes for each code length. Let bl_count[N] be the
    // number of codes of length N, N >= 1.
    for bits in 0..maxbits+1 {
        *bl_count.offset(bits as isize) = 0;
    }
    for i in 0..n {
        assert!(*lengths.offset(i as isize) <= maxbits, "{} <= {}", *lengths.offset(i as isize), maxbits);
        *bl_count.offset(*lengths.offset(i as isize) as isize) += 1;
    }

    // 2) Find the numerical value of the smallest code for each code length.
    let mut code = 0;
    *bl_count.offset(0) = 0;
    for bits in 1..maxbits+1 {
        code = (code + *bl_count.offset(bits as isize - 1)) << 1;
        *next_code.offset(bits as isize) = code;
    }

    // 3) Assign numerical values to all codes, using consecutive values for all
    // codes of the same length with the base values determined at step 2.
    for i in 0..n {
        let len = *lengths.offset(i as isize);
        if len != 0 {
            *symbols.offset(i as isize) = *next_code.offset(len as isize) as u32;
            *next_code.offset(len as isize) += 1;
        }
    }

    free(bl_count as *mut c_void);
    free(next_code as *mut c_void);
}

unsafe fn calculate_entropy(count: *const usize, n: usize, bitlengths: *mut f64) {
    const K_INV_LOG2: f64 = 1.4426950408889;  // 1.0 / log(2.0)
    let mut sum = 0;
    for i in 0..n {
        sum += *count.offset(i as isize);
    }
    let log2sum = (if sum == 0 { (n as f64).ln() } else { (sum as f64).ln() }) * K_INV_LOG2;
    for i in 0..n {
        // When the count of the symbol is 0, but its cost is requested anyway, it
        // means the symbol will appear at least once anyway, so give it the cost as if
        // its count is 1.
        if *count.offset(i as isize) == 0 {
            *bitlengths.offset(i as isize) = log2sum;
        } else {
            *bitlengths.offset(i as isize) = log2sum - (*count.offset(i as isize) as f64).ln() * K_INV_LOG2;
        }
        // Depending on compiler and architecture, the above subtraction of two
        // floating point numbers may give a negative result very close to zero
        // instead of zero (e.g. -5.973954e-17 with gcc 4.1.2 on Ubuntu 11.4). Clamp
        // it to zero. These floating point imprecisions do not affect the cost model
        // significantly so this is ok.
        if *bitlengths.offset(i as isize) < 0f64 && *bitlengths.offset(i as isize) > -1e-5 {
            *bitlengths.offset(i as isize) = 0f64;
        }
        assert!(*bitlengths.offset(i as isize) >= 0f64, "{} >= {}", *bitlengths.offset(i as isize), 0);
    }
}

unsafe fn calculate_bit_lengths(count: *const usize, n: usize, maxbits: i32, bitlengths: *mut u32) {
    let error = super::katajainen::length_limited_code_lengths(count, n as i32, maxbits, bitlengths);
    assert!(!error);
}
