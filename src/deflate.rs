//! Functions to compress according to the DEFLATE specification, using the
//! "squeeze" LZ77 compression backend.

use std::mem::uninitialized;
use std::ptr::{copy_nonoverlapping, null_mut};

use libc::{c_void, size_t};
use libc::funcs::c95::stdlib::{free, malloc};

use super::Options;

use tree::{calculate_bit_lengths, lengths_to_symbols};

/// bp = bitpointer, always in range [0, 7].
/// The outsize is number of necessary bytes to encode the bits.
/// Given the value of bp and the amount of bytes, the amount of bits represented
/// is not simply bytesize * 8 + bp because even representing one bit requires a
/// whole byte. It is: (bp == 0) ? (bytesize * 8) : ((bytesize - 1) * 8 + bp)
unsafe fn add_bit(bit: i32, bp: *mut u8, out: *mut *mut u8, outsize: *mut usize) {
    if *bp == 0 {
        append_data!(0, *out, *outsize);
    }
    *(*out).offset(*outsize as isize - 1) |= (bit << *bp) as u8;
    *bp = (*bp + 1) & 7;
}

unsafe fn add_bits(symbol: u32, length: u32, bp: *mut u8, out: *mut *mut u8, outsize: *mut usize) {
    // TODO(lode): make more efficient (add more bits at once).
    for i in 0..length {
        let bit: u32 = (symbol >> i) & 1;
        if *bp == 0 {
            append_data!(0, *out, *outsize);
        }
        *(*out).offset(*outsize as isize - 1) |= (bit << *bp) as u8;
        *bp = (*bp + 1) & 7;
    }
}

/// Adds bits, like AddBits, but the order is inverted. The deflate specification
/// uses both orders in one standard.
unsafe fn add_huffman_bits(symbol: u32, length: u32, bp: *mut u8, out: *mut *mut u8, outsize: *mut usize) {
    // TODO(lode): make more efficient (add more bits at once).
    for i in 0..length {
        let bit: u32 = (symbol >> (length - i - 1)) & 1;
        if *bp == 0 {
            append_data!(0, *out, *outsize);
        }
        *(*out).offset(*outsize as isize - 1) |= (bit << *bp) as u8;
        *bp = (*bp + 1) & 7;
    }
}

/**
 * Ensures there are at least 2 distance codes to support buggy decoders.
 * Zlib 1.2.1 and below have a bug where it fails if there isn't at least 1
 * distance code (with length > 0), even though it's valid according to the
 * deflate spec to have 0 distance codes. On top of that, some mobile phones
 * require at least two distance codes. To support these decoders too (but
 * potentially at the cost of a few bytes), add dummy code lengths of 1.
 * References to this bug can be found in the changelog of
 * Zlib 1.2.2 and here: http://www.jonof.id.au/forum/index.php?topic=515.0.
 *
 * d_lengths: the 32 lengths of the distance codes.
 */
unsafe fn patch_distance_codes_for_buggy_decoders(d_lengths: *mut u32) {
    // Amount of non-zero distance codes
    let mut num_dist_codes: i32 = 0;

    for i in 0..30 /* Ignore the two unused codes from the spec */ {
        if *d_lengths.offset(i) != 0 {
            num_dist_codes += 1;
        }
        if num_dist_codes >= 2 {
            // Two or more codes is fine.
            return;
        }
    }

    if num_dist_codes == 2 {
        *d_lengths.offset(0) = 1;
        *d_lengths.offset(1) = 1;
    } else if num_dist_codes == 1 {
        *d_lengths.offset(if *d_lengths.offset(0) != 0 { 1 } else { 0 }) = 1;
    }
}

/// Encodes the Huffman tree and returns how many bits its encoding takes. If out
/// is a null pointer, only returns the size and runs faster.
unsafe fn encode_tree(ll_lengths: *const u32, d_lengths: *const u32, use_16: bool, use_17: bool, use_18: bool, bp: *mut u8, out: *mut *mut u8, outsize: *mut usize) -> usize {
    let mut rle: *mut u32 = null_mut(); // Runlength encoded version of lengths of litlen and dist trees.
    let mut rle_bits: *mut u32 = null_mut(); // Extra bits for rle values 16, 17 and 18.
    let mut rle_size: usize = 0; // Size of rle array.
    let mut rle_bits_size: usize = 0; // Should have same value as rle_size.
    let mut hlit: u32 = 29; // 286 - 257
    let mut hdist: u32 = 29; // 32 - 1, but gzip does not like hdist > 29.
    let mut hclen: u32;
    let mut clcounts: [usize; 19] = [0; 19];
    let mut clcl: [u32; 19] = uninitialized(); // Code length code lengths.
    let mut clsymbols: [u32; 19] = uninitialized();

    /// The order in which code length code lengths are encoded as per deflate.
    const ORDER: [u32; 19] = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];

    let size_only = out.is_null();
    let mut result_size: usize = 0;

    // Trim zeros.
    while hlit > 0 && *ll_lengths.offset(257 + hlit as isize - 1) == 0 {
        hlit -= 1;
    }
    while hdist > 0 && *d_lengths.offset(1 + hdist as isize - 1) == 0 {
        hdist -= 1;
    }
    let hlit2: u32 = hlit + 257;

    let lld_total: u32 = hlit2 + hdist + 1; // Total amount of literal, length, distance codes.

    let mut i: usize = 0;
    while i < lld_total as usize {
        // This is an encoding of a huffman tree, so now the length is a symbol
        let symbol: u8 = if i < hlit2 as usize { *ll_lengths.offset(i as isize) as u8 } else { *d_lengths.offset((i - hlit2 as usize) as isize) as u8 };
        let mut count: u32 = 1;
        if use_16 || (symbol == 0 && (use_17 || use_18)) {
            let mut j: usize = i as usize + 1;
            while j < lld_total as usize && symbol == (if j < hlit2 as usize { *ll_lengths.offset(j as isize) as u8 } else { *d_lengths.offset((j - hlit2 as usize) as isize) as u8 }) {
                count += 1;
                j += 1;
            }
        }
        i += count as usize - 1;

        // Repetitions of zeroes
        if symbol == 0 && count >= 3 {
            if use_18 {
                while count >= 11 {
                    let count2: u32 = if count > 138 { 138 } else { count };
                    if !size_only {
                        append_data!(18, rle, rle_size);
                        append_data!(count2 - 11, rle_bits, rle_bits_size);
                    }
                    clcounts[18] += 1;
                    count -= count2;
                }
            }
            if use_17 {
                while count >= 3 {
                    let count2: u32 = if count > 10 { 10 } else { count };
                    if !size_only {
                        append_data!(17, rle, rle_size);
                        append_data!(count2 - 3, rle_bits, rle_bits_size);
                    }
                    clcounts[17] += 1;
                    count -= count2;
                }
            }
        }

        // Repetitions of any symbol
        if use_16 && count >= 4 {
            count -= 1; // Since the first one is hardcoded.
            clcounts[symbol as usize] += 1;
            if !size_only {
                append_data!(symbol as u32, rle, rle_size);
                append_data!(0, rle_bits, rle_bits_size);
            }
            while count >= 3 {
                let count2: u32 = if count > 6 { 6 } else { count };
                if !size_only {
                    append_data!(16, rle, rle_size);
                    append_data!(count2 - 3, rle_bits, rle_bits_size);
                }
                clcounts[16] += 1;
                count -= count2;
            }
        }

        // No or insufficient repetition
        clcounts[symbol as usize] += count as usize;
        while count > 0 {
            if !size_only {
                append_data!(symbol as u32, rle, rle_size);
                append_data!(0, rle_bits, rle_bits_size);
            }
            count -= 1;
        }
        i += 1;
    }

    calculate_bit_lengths(clcounts.as_ptr(), 19, 7, clcl.as_mut_ptr());
    if !size_only {
        lengths_to_symbols(clcl.as_ptr(), 19, 7, clsymbols.as_mut_ptr());
    }

    hclen = 15;
    // Trim zeros.
    while hclen > 0 && clcounts[ORDER[hclen as usize + 4 - 1] as usize] == 0 {
        hclen -= 1;
    }

    if !size_only {
        add_bits(hlit, 5, bp, out, outsize);
        add_bits(hdist, 5, bp, out, outsize);
        add_bits(hclen, 4, bp, out, outsize);

        for i in 0..hclen+4 {
            add_bits(clcl[ORDER[i as usize] as usize], 3, bp, out, outsize);
        }

        for i in 0..rle_size {
            let symbol: u32 = clsymbols[*rle.offset(i as isize) as usize];
            add_huffman_bits(symbol, clcl[*rle.offset(i as isize) as usize], bp, out, outsize);
            // Extra bits.
            if *rle.offset(i as isize) == 16 {
                add_bits(*rle_bits.offset(i as isize), 2, bp, out, outsize);
            } else if *rle.offset(i as isize) == 17 {
                add_bits(*rle_bits.offset(i as isize), 3, bp, out, outsize);
            } else if *rle.offset(i as isize) == 18 {
                add_bits(*rle_bits.offset(i as isize), 7, bp, out, outsize);
            }
        }
    }

    result_size += 14; // hlit, hdist, hclen bits
    result_size += (hclen as usize + 4) * 3; // clcl bits
    for i in 0..19 {
        result_size += clcl[i] as usize * clcounts[i];
    }
    // Extra bits.
    result_size += clcounts[16] * 2;
    result_size += clcounts[17] * 3;
    result_size += clcounts[18] * 7;

    // Note: in case of "size_only" these are null pointers so no effect.
    free(rle as *mut c_void);
    free(rle_bits as *mut c_void);

    result_size
}

fn add_dynamic_tree(ll_lengths: *const u32, d_lengths: *const u32, bp: *const u8, out: *const *const u8, outsize: *const usize) {
    unimplemented!();
}

/// Gives the exact size of the tree, in bits, as it will be encoded in DEFLATE.
fn calculate_tree_size(ll_lengths: *const u32, d_lengths: *const u32) -> usize {
    unimplemented!();
}

/// Adds all lit/len and dist codes from the lists as huffman symbols. Does not add
/// end code 256. expected_data_size is the uncompressed block size, used for
/// assert, but you can set it to 0 to not do the assertion.
fn add_lz77_data(litlens: *const u16, dists: *const u16, lstart: usize, lend: usize, expected_data_size: usize,
                 ll_symbols: *const u32, ll_lengths: *const u32, d_symbols: *const u32, d_lengths: *const u32,
                 bp: *const u8, out: *const *const u8, outsize: *const usize) {
    unimplemented!();
}

fn get_fixed_tree(ll_lengths: *const u32, d_lengths: *const u32) {
    unimplemented!();
}

/// Calculates size of the part after the header and tree of an LZ77 block, in bits.
fn calculate_block_symbol_size(ll_lengths: *const u32, d_lengths: *const u32, litlens: *const u16, dists: *const u16, lstart: usize, lend: usize) -> usize {
    unimplemented!();
}

fn abs_diff(x: usize, y: usize) -> usize {
    unimplemented!();
}

/// Change the population counts in a way that the consequent Hufmann tree
/// compression, especially its rle-part will be more likely to compress this data
/// more efficiently. length containts the size of the histogram.
fn optimize_huffman_for_rle(length: i32, counts: *const usize) {
    unimplemented!();
}

/// Calculates the bit lengths for the symbols for dynamic blocks. Chooses bit
/// lengths that give the smallest size of tree encoding + encoding of all the
/// symbols to have smallest output size. This are not necessarily the ideal Huffman
/// bit lengths.
fn get_dynamic_lengths(litlens: *const u16, dists: *const u16, lstart: usize, lend: usize, ll_lengths: *const u32, d_lengths: *const u32) {
    unimplemented!();
}

/// Calculates block size in bits.
/// litlens: lz77 lit/lengths
/// dists: ll77 distances
/// lstart: start of block
/// lend: end of block (not inclusive)
pub unsafe fn calculate_block_size(litlens: *const u16, dists: *const u16, lstart: usize, lend: usize, btype: i32) -> f64 {
    let ll_lengths: [u32; 288] = uninitialized();
    let d_lengths: [u32; 32] = uninitialized();

    // bfinal and btype bits
    let mut result: f64 = 3.0;

    // This is not for uncompressed blocks.
    assert!(btype == 1 || btype == 2);

    if btype == 1 {
        get_fixed_tree(ll_lengths.as_ptr(), d_lengths.as_ptr());
    } else {
        get_dynamic_lengths(litlens, dists, lstart, lend, ll_lengths.as_ptr(), d_lengths.as_ptr());
        result += calculate_tree_size(ll_lengths.as_ptr(), d_lengths.as_ptr()) as f64;
    }

    result += calculate_block_symbol_size(ll_lengths.as_ptr(), d_lengths.as_ptr(), litlens, dists, lstart, lend) as f64;

    result
}

/**
 * Adds a deflate block with the given LZ77 data to the output.
 * options: global program options
 * btype: the block type, must be 1 or 2
 * final: whether to set the "final" bit on this block, must be the last block
 * litlens: literal/length array of the LZ77 data, in the same format as in
 *     ZopfliLZ77Store.
 * dists: distance array of the LZ77 data, in the same format as in
 *     ZopfliLZ77Store.
 * lstart: where to start in the LZ77 data
 * lend: where to end in the LZ77 data (not inclusive)
 * expected_data_size: the uncompressed block size, used for assert, but you can
 *   set it to 0 to not do the assertion.
 * bp: output bit pointer
 * out: dynamic output array to append to
 * outsize: dynamic output array size
 */
fn add_lz77_block(options: *const Options, btype: i32, is_final: bool, litlens: *const u16, dists: *const u16, lstart: usize, lend: usize,
                  expected_data_size: usize, bp: *const u8, out: *const *const u8, outsize: *const usize) {
    unimplemented!();
}

fn deflate_dynamic_block(options: *const Options, is_final: bool, in_: *const u8, instart: usize, inend: usize, bp: *const u8, out: *const *const u8, outsize: *const usize) {
    unimplemented!();
}

fn deflate_fixed_block(options: *const Options, is_final: bool, in_: *const u8, instart: usize, inend: usize, bp: *const u8, out: *const *const u8, outsize: *const usize) {
    unimplemented!();
}

fn deflate_non_compressed_block(options: *const Options, is_final: bool, in_: *const u8, instart: usize, inend: usize, bp: *const u8, out: *const *const u8, outsize: *const usize) {
    unimplemented!();
}

fn deflate_block(options: *const Options, btype: i32, is_final: bool, in_: *const u8, instart: usize, inend: usize, bp: *const u8, out: *const *const u8, outsize: *const usize) {
    unimplemented!();
}

/// Does squeeze strategy where first block splitting is done, then each block is
/// squeezed.
/// Parameters: see description of the ZopfliDeflate function.
fn deflate_splitting_first(options: *const Options, btype: i32, is_final: bool, in_: *const u8, instart: usize, inend: usize, bp: *const u8, out: *const *const u8, outsize: *const usize) {
    unimplemented!();
}

/// Does squeeze strategy where first the best possible lz77 is done, and then based
/// on that data, block splitting is done.
/// Parameters: see description of the ZopfliDeflate function.
fn deflate_splitting_last(options: *const Options, btype: i32, is_final: bool, in_: *const u8, instart: usize, inend: usize, bp: *const u8, out: *const *const u8, outsize: *const usize) {
    unimplemented!();
}

/**
 * Like ZopfliDeflate, but allows to specify start and end byte with instart and
 * inend. Only that part is compressed, but earlier bytes are still used for the
 * back window.
 *
 * Deflate a part, to allow ZopfliDeflate() to use multiple master blocks if
 * needed.
 * It is possible to call this function multiple times in a row, shifting
 * instart and inend to next bytes of the data. If instart is larger than 0, then
 * previous bytes are used as the initial dictionary for LZ77.
 * This function will usually output multiple deflate blocks. If final is 1, then
 * the final bit will be set on the last block.
*/
fn deflate_part(options: *const Options, btype: i32, is_final: bool, input: *const u8, instart: usize, inend: usize, bp: *mut u8, out: *mut *mut u8, outsize: *mut usize) {
    unimplemented!();
}

/**
 * Compresses according to the deflate specification and append the compressed
 * result to the output.
 * This function will usually output multiple deflate blocks. If final is 1, then
 * the final bit will be set on the last block.
 *
 * options: global program options
 * btype: the deflate block type. Use 2 for best compression.
 *   -0: non compressed blocks (00)
 *   -1: blocks with fixed tree (01)
 *   -2: blocks with dynamic tree (10)
 * final: whether this is the last section of the input, sets the final bit to the
 *   last deflate block.
 * in: the input bytes
 * insize: number of input bytes
 * bp: bit pointer for the output array. This must initially be 0, and for
 *   consecutive calls must be reused (it can have values from 0-7). This is
 *   because deflate appends blocks as bit-based data, rather than on byte
 *   boundaries.
 * out: pointer to the dynamic output array to which the result is appended. Must
 *   be freed after use.
 * outsize: pointer to the dynamic output array size.
 */
pub unsafe fn deflate(options: *const Options, btype: i32, is_final: bool, input: *const u8, insize: usize, bp: *mut u8, out: *mut *mut u8, outsize: *mut usize) {
    *out = malloc(insize as u64) as *mut u8;
    copy_nonoverlapping(input, *out, insize);
    *outsize = insize;
}
