use std::iter;

use libc::size_t;

pub fn lengths_to_symbols(lengths: &[u32], n: usize, maxbits: u32, symbols: &mut [u32]) {
    let mut bl_count: Vec<size_t> = iter::repeat(0).take(maxbits as usize + 1).collect();
    let mut next_code: Vec<size_t> = iter::repeat(0).take(maxbits as usize + 1).collect();

    for i in 0..n {
        symbols[i] = 0;
    }

    // 1) Count the number of codes for each code length. Let bl_count[N] be the
    // number of codes of length N, N >= 1.
    for i in 0..n {
        assert!(lengths[i] <= maxbits, "{} <= {}", lengths[i], maxbits);
        bl_count[lengths[i] as usize] += 1;
    }

    // 2) Find the numerical value of the smallest code for each code length.
    let mut code = 0;
    bl_count[0] = 0;
    for bits in 1..maxbits + 1 {
        code = (code + bl_count[bits as usize - 1]) << 1;
        next_code[bits as usize] = code;
    }

    // 3) Assign numerical values to all codes, using consecutive values for all
    // codes of the same length with the base values determined at step 2.
    for i in 0..n {
        let len = lengths[i];
        if len != 0 {
            symbols[i] = next_code[len as usize] as u32;
            next_code[len as usize] += 1;
        }
    }
}

pub fn calculate_entropy(count: &[usize], bitlengths: &mut [f64]) {
    const K_INV_LOG2: f64 = 1.4426950408889;  // 1.0 / log(2.0)
    let mut sum = 0;
    for i in 0..count.len() {
        sum += count[i];
    }
    let log2sum = (if sum == 0 { (count.len() as f64).ln() } else { (sum as f64).ln() }) * K_INV_LOG2;
    for i in 0..count.len() {
        // When the count of the symbol is 0, but its cost is requested anyway, it
        // means the symbol will appear at least once anyway, so give it the cost as if
        // its count is 1.
        if count[i] == 0 {
            bitlengths[i] = log2sum;
        } else {
            bitlengths[i] = log2sum - (count[i] as f64).ln() * K_INV_LOG2;
        }
        // Depending on compiler and architecture, the above subtraction of two
        // floating point numbers may give a negative result very close to zero
        // instead of zero (e.g. -5.973954e-17 with gcc 4.1.2 on Ubuntu 11.4). Clamp
        // it to zero. These floating point imprecisions do not affect the cost model
        // significantly so this is ok.
        if bitlengths[i] < 0f64 && bitlengths[i] > -1e-5 {
            bitlengths[i] = 0f64;
        }
        assert!(bitlengths[i] >= 0f64, "{} >= {}", bitlengths[i], 0);
    }
}

pub fn calculate_bit_lengths(count: &[usize], n: usize, maxbits: i32, bitlengths: &mut [u32]) {
    let error = super::katajainen::length_limited_code_lengths(count, n as i32, maxbits, bitlengths);
    assert!(!error);
}
