//! Functions to compress according to the Zlib specification.

use std::io::Write;

use super::Options;

use deflate::deflate;

/// Calculates the adler32 checksum of the data
fn adler32(data: &[u8]) -> u32 {
    const SUMS_OVERFLOW: u32 = 5550;
    let mut s1: u32 = 1;
    let mut s2: u32 = 1 >> 16;

    let mut i = 0;
    let mut size = data.len();
    while size > 0 {
        let mut amount: usize = if size > SUMS_OVERFLOW as usize { SUMS_OVERFLOW as usize } else { size };
        size -= amount;
        while amount > 0 {
            s1 += data[i] as u32;
            i += 1;
            s2 += s1;
            amount -= 1;
        }
        s1 %= 65521;
        s2 %= 65521;
    }

    (s2 << 16) | s1
}

/**
 * Compresses according to the zlib specification and append the compressed
 * result to the output.
 *
 * options: global program options
 * out: pointer to the dynamic output array to which the result is appended. Must
 *   be freed after use.
 * outsize: pointer to the dynamic output array size.
 */
pub unsafe fn compress(options: *const Options, input: &[u8], out: *mut *mut u8, outsize: *mut usize) {
    let mut bitpointer: u8 = 0;
    let checksum: u32 = adler32(input);
    let cmf: u32 = 120; // CM 8, CINFO 7. See zlib spec.
    let flevel: u32 = 0;
    let fdict: u32 = 0;
    let mut cmfflg: u32 = 256 * cmf + fdict * 32 + flevel * 64;
    let fcheck: u32 = 31 - cmfflg % 31;
    cmfflg += fcheck;

    append_data!((cmfflg / 256) as u8, *out, *outsize);
    append_data!((cmfflg % 256) as u8, *out, *outsize);

    deflate(options, 2 /* dynamic block */, true /* final */, input, &mut bitpointer, out, outsize);

    append_data!(((checksum >> 24) % 256) as u8, *out, *outsize);
    append_data!(((checksum >> 16) % 256) as u8, *out, *outsize);
    append_data!(((checksum >> 8) % 256) as u8, *out, *outsize);
    append_data!((checksum % 256) as u8, *out, *outsize);

    if (*options).verbose {
        let insize = input.len();
        println_err!("Original Size: {}, Zlib: {}, Compression: {}% Removed", insize, *outsize, 100.0 * (insize as isize - *outsize as isize) as f64 / insize as f64);
    }
}
