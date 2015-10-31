//! Functions to compress according to the Gzip specification.

use std::io::Write;

use super::Options;

use deflate::deflate;

/// Table of CRCs of all 8-bit messages.
static mut crc_table: [u64; 256] = [0u64; 256];

/// Flag: has the table been computed? Initially false.
static mut crc_table_computed: bool = false;

/// Makes the table for a fast CRC.
unsafe fn make_crc_table() {
    for n in 0..256 {
        let mut c: u64 = n as u64;
        for _ in 0..8 {
            if c & 1 == 1 {
                c = 0xedb88320u64 ^ (c >> 1);
            } else {
                c = c >> 1;
            }
        }
        crc_table[n] = c;
    }
    crc_table_computed = true;
}

/// Updates a running crc with the bytes buf[0..len-1] and returns
/// the updated crc. The crc should be initialized to zero.
unsafe fn update_crc(crc: u64, buf: &[u8]) -> u64 {
    let mut c: u64 = crc ^ 0xffffffffu64;

    if !crc_table_computed {
        make_crc_table();
    }
    for v in buf {
        c = crc_table[((c ^ *v as u64) & 0xff) as usize] ^ (c >> 8);
    }
    c ^ 0xffffffffu64
}

/// Returns the CRC of the bytes buf[0..len-1].
unsafe fn crc(buf: &[u8]) -> u64 {
    update_crc(0u64, buf)
}

/**
 * Compresses according to the gzip specification and append the compressed
 * result to the output.
 *
 * options: global program options
 * out: pointer to the dynamic output array to which the result is appended. Must
 *   be freed after use.
 * outsize: pointer to the dynamic output array size.
 */
pub unsafe fn compress(options: &Options, input: &[u8]) -> Vec<u8> {
    let crcvalue: u64 = crc(input);
    let mut bp: u8 = 0;

    let mut out = Vec::new();
    out.push(31); // ID1
    out.push(139); // ID2
    out.push(8); // CM
    out.push(0); // FLG
    // MTIME
    out.push(0);
    out.push(0);
    out.push(0);
    out.push(0);

    out.push(2); // XFL, 2 indicates best compression.
    out.push(3); // OS follows Unix conventions.

    deflate(options,
            2, // Dynamic block
            true,
            input,
            &mut bp,
            &mut out);

    // CRC
    out.push((crcvalue % 256) as u8);
    out.push(((crcvalue >> 8) % 256) as u8);
    out.push(((crcvalue >> 16) % 256) as u8);
    out.push(((crcvalue >> 24) % 256) as u8);

    // ISIZE
    let insize = input.len();
    out.push((insize % 256) as u8);
    out.push(((insize >> 8) % 256) as u8);
    out.push(((insize >> 16) % 256) as u8);
    out.push(((insize >> 24) % 256) as u8);

    if (*options).verbose {
        let outsize = out.len();
        println_err!("Original Size: {}, Gzip: {}, Compression: {}% Removed",
                     insize,
                     outsize,
                     100.0 * (insize as isize - outsize as isize) as f64 / insize as f64);
    }
    out
}
