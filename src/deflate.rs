//! Functions to compress according to the DEFLATE specification, using the
//! "squeeze" LZ77 compression backend.

use std::io::Write;
use std::mem::{size_of, uninitialized};
use std::ptr::null_mut;

use libc::{c_void, size_t};
use libc::funcs::c95::stdlib::{free, malloc};

use super::Options;
use util;

use blocksplitter::{block_split, block_split_lz77, block_split_simple};

#[cfg(feature = "longest-match-cache")]
use cache;
#[cfg(feature = "longest-match-cache")]
use cache::LongestMatchCache;

use lz77::{clean_lz77_store, lz77_counts, BlockState, LZ77Store};
use squeeze::{lz77_optimal, lz77_optimal_fixed};
use tree::{calculate_bit_lengths, lengths_to_symbols};
use util::{get_length_symbol, get_dist_symbol, get_length_extra_bits_value, get_length_extra_bits, get_dist_extra_bits_value, get_dist_extra_bits};

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

    if num_dist_codes == 0 {
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

unsafe fn add_dynamic_tree(ll_lengths: *const u32, d_lengths: *const u32, bp: *mut u8, out: *mut *mut u8, outsize: *mut usize) {
    let mut best: i32 = 0;
    let mut bestsize: usize = 0;

    for i in 0..8 {
        let size: usize = encode_tree(ll_lengths, d_lengths, i & 1 != 0, i & 2 != 0, i & 4 != 0, null_mut(), null_mut(), null_mut());
        if bestsize == 0 || size < bestsize {
            bestsize = size;
            best = i;
        }
    }

    encode_tree(ll_lengths, d_lengths, best & 1 != 0, best & 2 != 0, best & 4 != 0, bp, out, outsize);
}

/// Gives the exact size of the tree, in bits, as it will be encoded in DEFLATE.
unsafe fn calculate_tree_size(ll_lengths: *const u32, d_lengths: *const u32) -> usize {
    let mut result: usize = 0;

    for i in 0..8 {
        let size: usize = encode_tree(ll_lengths, d_lengths, i & 1 != 0, i & 2 != 0, i & 4 != 0, null_mut(), null_mut(), null_mut());
        if result == 0 || size < result {
            result = size;
        }
    }

    result
}

/// Adds all lit/len and dist codes from the lists as huffman symbols. Does not add
/// end code 256. expected_data_size is the uncompressed block size, used for
/// assert, but you can set it to 0 to not do the assertion.
unsafe fn add_lz77_data(litlens: *const u16, dists: *const u16, lstart: usize, lend: usize, expected_data_size: usize,
                 ll_symbols: *const u32, ll_lengths: *const u32, d_symbols: *const u32, d_lengths: *const u32,
                 bp: *mut u8, out: *mut *mut u8, outsize: *mut usize) {
    let mut testlength: usize = 0;
    for i in lstart..lend {
        let dist: u32 = *dists.offset(i as isize) as u32;
        let litlen: u32 = *litlens.offset(i as isize) as u32;
        if dist == 0 {
            assert!(litlen < 256);
            assert!(*ll_lengths.offset(litlen as isize) > 0);
            add_huffman_bits(*ll_symbols.offset(litlen as isize), *ll_lengths.offset(litlen as isize), bp, out, outsize);
            testlength += 1;
        } else {
            let lls: u32 = get_length_symbol(litlen as i32) as u32;
            let ds: u32 = get_dist_symbol(dist as i32) as u32;
            assert!(litlen >= 3 && litlen <= 288);
            assert!(*ll_lengths.offset(lls as isize) > 0);
            assert!(*d_lengths.offset(ds as isize) > 0);
            add_huffman_bits(*ll_symbols.offset(lls as isize), *ll_lengths.offset(lls as isize), bp, out, outsize);
            add_bits(get_length_extra_bits_value(litlen as i32) as u32, get_length_extra_bits(litlen as i32) as u32, bp, out, outsize);
            add_huffman_bits(*d_symbols.offset(ds as isize), *d_lengths.offset(ds as isize), bp, out, outsize);
            add_bits(get_dist_extra_bits_value(dist as i32) as u32, get_dist_extra_bits(dist as i32) as u32, bp, out, outsize);
            testlength += litlen as usize;
        }
    }
    assert!(expected_data_size == 0 || testlength == expected_data_size);
}

unsafe fn get_fixed_tree(ll_lengths: *mut u32, d_lengths: *mut u32) {
    for i in 0..144 {
        *ll_lengths.offset(i) = 8;
    }
    for i in 144..256 {
        *ll_lengths.offset(i) = 9;
    }
    for i in 256..280 {
        *ll_lengths.offset(i) = 7;
    }
    for i in 280..288 {
        *ll_lengths.offset(i) = 8;
    }
    for i in 0..32 {
        *d_lengths.offset(i) = 5;
    }
}

/// Calculates size of the part after the header and tree of an LZ77 block, in bits.
unsafe fn calculate_block_symbol_size(ll_lengths: *const u32, d_lengths: *const u32, litlens: *const u16, dists: *const u16, lstart: usize, lend: usize) -> usize {
    let mut result: usize = 0;
    for i in lstart..lend {
        if *dists.offset(i as isize) ==0 {
            result += *ll_lengths.offset(*litlens.offset(i as isize) as isize) as usize;
        } else {
            result += *ll_lengths.offset(get_length_symbol(*litlens.offset(i as isize) as i32) as isize) as usize;
            result += *d_lengths.offset(get_dist_symbol(*dists.offset(i as isize) as i32) as isize) as usize;
            result += get_length_extra_bits(*litlens.offset(i as isize) as i32) as usize;
            result += get_dist_extra_bits(*dists.offset(i as isize) as i32) as usize;
        }
    }
    result += *ll_lengths.offset(256) as usize; // end symbol
    result
}

fn abs_diff(x: usize, y: usize) -> usize {
    if x > y {
        x - y
    } else {
        y - x
    }
}

/// Change the population counts in a way that the consequent Hufmann tree
/// compression, especially its rle-part will be more likely to compress this data
/// more efficiently. length containts the size of the histogram.
unsafe fn optimize_huffman_for_rle(mut length: i32, counts: *mut usize) {
    // 1) We don't want to touch the trailing zeros. We may break the
    // rules of the format by adding more data in the distance codes.
    while length >= 0 {
        if length == 0 {
            return;
        }
        if *counts.offset(length as isize - 1) != 0 {
            // Now counts[0..length - 1] does not have trailing zeros.
            break;
        }
        length -= 1;
    }
    // 2) Let's mark all population counts that already can be encoded
    // with an rle code.
    let good_for_rle: *mut bool = malloc((length as usize * size_of::<bool>()) as size_t) as *mut bool;
    for i in 0..length {
        *good_for_rle.offset(i as isize) = false;
    }

    // Let's not spoil any of the existing good rle codes.
    // Mark any seq of 0's that is longer than 5 as a good_for_rle.
    // Mark any seq of non-0's that is longer than 7 as a good_for_rle.
    let mut symbol: usize = *counts.offset(0);
    let mut stride: i32 = 0;
    for i in 0..length+1 {
        if i == length || *counts.offset(i as isize) != symbol {
            if (symbol == 0 && stride >= 5) || (symbol != 0 && stride >= 7) {
                for k in 0..stride {
                    *good_for_rle.offset(i as isize - k as isize - 1) = true;
                }
            }
            stride = 1;
            if i != length {
                symbol = *counts.offset(i as isize);
            }
        } else {
            stride += 1;
        }
    }

    // 3) Let's replace those population counts that lead to more rle codes.
    stride = 0;
    let mut limit: usize = *counts.offset(0);
    let mut sum: usize = 0;
    for i in 0..length+1 {
        if i == length || *good_for_rle.offset(i as isize)
            // Heuristic for selecting the stride ranges to collapse.
            || abs_diff(*counts.offset(i as isize), limit) >= 4 {
                if stride >= 4 || (stride >= 3 && sum == 0) {
                    // The stride must end, collapse what we have, if we have enough (4).
                    let mut count: i32 = ((sum + stride as usize / 2) / stride as usize) as i32;
                    if count < 1 {
                        count = 1;
                    }
                    if sum == 0 {
                        // Don't make an all zeros stride to be upgraded to ones.
                        count = 0;
                    }
                    for k in 0..stride {
                        // We don't want to change value at counts[i],
                        // that is already belonging to the next stride. Thus - 1.
                        *counts.offset(i as isize - k as isize - 1) = count as usize;
                    }
                }
                stride = 0;
                sum = 0;
                if i < length - 3 {
                    // All interesting strides have a count of at least 4,
                    // at least when non-zeros.
                    limit = (*counts.offset(i as isize) + *counts.offset(i as isize + 1) + *counts.offset(i as isize + 2) + *counts.offset(i as isize + 3) + 2) / 4;
                } else if i < length {
                    limit = *counts.offset(i as isize);
                } else {
                    limit = 0;
                }
            }
        stride += 1;
        if i != length {
            sum += *counts.offset(i as isize);
        }
    }

    free(good_for_rle as *mut c_void);
}

/// Calculates the bit lengths for the symbols for dynamic blocks. Chooses bit
/// lengths that give the smallest size of tree encoding + encoding of all the
/// symbols to have smallest output size. This are not necessarily the ideal Huffman
/// bit lengths.
unsafe fn get_dynamic_lengths(litlens: *const u16, dists: *const u16, lstart: usize, lend: usize, ll_lengths: *mut u32, d_lengths: *mut u32) {
    let mut ll_counts: [usize; 288] = uninitialized();
    let mut d_counts: [usize; 32] = uninitialized();

    lz77_counts(litlens, dists, lstart, lend, ll_counts.as_mut_ptr(), d_counts.as_mut_ptr());
    optimize_huffman_for_rle(288, ll_counts.as_mut_ptr());
    optimize_huffman_for_rle(32, d_counts.as_mut_ptr());
    calculate_bit_lengths(ll_counts.as_ptr(), 288, 15, ll_lengths);
    calculate_bit_lengths(d_counts.as_ptr(), 32, 15, d_lengths);
    patch_distance_codes_for_buggy_decoders(d_lengths);
}

/// Calculates block size in bits.
/// litlens: lz77 lit/lengths
/// dists: ll77 distances
/// lstart: start of block
/// lend: end of block (not inclusive)
pub unsafe fn calculate_block_size(litlens: *const u16, dists: *const u16, lstart: usize, lend: usize, btype: i32) -> f64 {
    let mut ll_lengths: [u32; 288] = uninitialized();
    let mut d_lengths: [u32; 32] = uninitialized();

    // bfinal and btype bits
    let mut result: f64 = 3.0;

    // This is not for uncompressed blocks.
    assert!(btype == 1 || btype == 2);

    if btype == 1 {
        get_fixed_tree(ll_lengths.as_mut_ptr(), d_lengths.as_mut_ptr());
    } else {
        get_dynamic_lengths(litlens, dists, lstart, lend, ll_lengths.as_mut_ptr(), d_lengths.as_mut_ptr());
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
unsafe fn add_lz77_block(options: *const Options, btype: i32, is_final: bool, litlens: *const u16, dists: *const u16, lstart: usize, lend: usize,
                  expected_data_size: usize, bp: *mut u8, out: *mut *mut u8, outsize: *mut usize) {
    let mut ll_lengths: [u32; 288] = uninitialized();
    let mut d_lengths: [u32; 32] = uninitialized();
    let mut ll_symbols: [u32; 288] = uninitialized();
    let mut d_symbols: [u32; 32] = uninitialized();

    add_bit(if is_final { 1 } else { 0 }, bp, out, outsize);
    add_bit(btype & 1, bp, out, outsize);
    add_bit((btype & 2) >> 1, bp, out, outsize);

    if btype == 1 {
        // Fixed block.
        get_fixed_tree(ll_lengths.as_mut_ptr(), d_lengths.as_mut_ptr());
    } else {
        // Dynamic block.
        assert_eq!(btype, 2);

        get_dynamic_lengths(litlens, dists, lstart, lend, ll_lengths.as_mut_ptr(), d_lengths.as_mut_ptr());

        let detect_tree_size: u32 = *outsize as u32;
        add_dynamic_tree(ll_lengths.as_ptr(), d_lengths.as_ptr(), bp, out, outsize);
        if (*options).verbose {
            println_err!("treesize: {}", *outsize - detect_tree_size as usize);
        }
    }

    lengths_to_symbols(ll_lengths.as_ptr(), 288, 15, ll_symbols.as_mut_ptr());
    lengths_to_symbols(d_lengths.as_ptr(), 32, 15, d_symbols.as_mut_ptr());

    let detect_block_size: usize = *outsize;
    add_lz77_data(litlens, dists, lstart, lend, expected_data_size, ll_symbols.as_ptr(), ll_lengths.as_ptr(), d_symbols.as_ptr(), d_lengths.as_ptr(), bp, out, outsize);

    // End symbol.
    add_huffman_bits(ll_symbols[256], ll_lengths[256], bp, out, outsize);

    let mut uncompressed_size: usize = 0;
    for i in lstart..lend {
        uncompressed_size += if *dists.offset(i as isize) == 0 { 1 } else { *litlens.offset(i as isize) } as usize;
    }
    let compressed_size: usize = *outsize - detect_block_size;
    if (*options).verbose {
        println_err!("compressed block size: {} ({}k) (unc: {})", compressed_size, (compressed_size / 1024), uncompressed_size);
    }
}

unsafe fn deflate_dynamic_block(options: *const Options, is_final: bool, in_: *const u8, instart: usize, inend: usize, bp: *mut u8, out: *mut *mut u8, outsize: *mut usize) {
    let blocksize: usize = inend - instart;

    #[cfg(feature = "longest-match-cache")]
    unsafe fn create_block_state(options: *const Options, instart: usize, inend: usize, blocksize: usize) -> BlockState {
        BlockState::new(options, instart, inend, LongestMatchCache::new(blocksize))
    }
    #[cfg(not(feature = "longest-match-cache"))]
    fn create_block_state(options: *const Options, instart: usize, inend: usize, _blocksize: usize) -> BlockState {
        BlockState::new(options, instart, inend, null_mut())
    }
    let mut s = create_block_state(options, instart, inend, blocksize);

    let mut store = LZ77Store::new();
    let mut btype: i32 = 2;

    lz77_optimal(&s, in_, instart, inend, &mut store);

    // For small block, encoding with fixed tree can be smaller. For large block,
    // don't bother doing this expensive test, dynamic tree will be better.
    if store.size < 1000 {
        let mut fixedstore = LZ77Store::new();
        lz77_optimal_fixed(&mut s, in_, instart, inend, &mut fixedstore);
        let dyncost: f64 = calculate_block_size(store.litlens, store.dists, 0, store.size, 2);
        let fixedcost: f64 = calculate_block_size(fixedstore.litlens, fixedstore.dists, 0, fixedstore.size, 1);
        if fixedcost < dyncost {
            btype = 1;
            clean_lz77_store(&mut store);
            store = fixedstore;
        } else {
            clean_lz77_store(&mut fixedstore);
        }
    }

    add_lz77_block(s.options, btype, is_final, store.litlens, store.dists, 0, store.size, blocksize, bp, out, outsize);

    #[cfg(feature = "longest-match-cache")]
    unsafe fn clean_cache(s: *mut BlockState) {
        cache::clean_cache((*s).lmc);
        free((*s).lmc as *mut c_void);
    }
    #[cfg(not(feature = "longest-match-cache"))]
    fn clean_cache(_s: *mut BlockState) { }
    clean_cache(&mut s);

    clean_lz77_store(&mut store);
}

unsafe fn deflate_fixed_block(options: *const Options, is_final: bool, in_: *const u8, instart: usize, inend: usize, bp: *mut u8, out: *mut *mut u8, outsize: *mut usize) {
    let blocksize: usize = inend - instart;

    #[cfg(feature = "longest-match-cache")]
    unsafe fn create_block_state(options: *const Options, instart: usize, inend: usize, blocksize: usize) -> BlockState {
        BlockState::new(options, instart, inend, LongestMatchCache::new(blocksize))
    }
    #[cfg(not(feature = "longest-match-cache"))]
    fn create_block_state(options: *const Options, instart: usize, inend: usize, _blocksize: usize) -> BlockState {
        BlockState::new(options, instart, inend, null_mut())
    }
    let mut s = create_block_state(options, instart, inend, blocksize);

    let mut store = LZ77Store::new();

    lz77_optimal_fixed(&mut s, in_, instart, inend, &mut store);

    add_lz77_block(s.options, 1, is_final, store.litlens, store.dists, 0, store.size, blocksize, bp, out, outsize);

    #[cfg(feature = "longest-match-cache")]
    unsafe fn clean_cache(s: *mut BlockState) {
        cache::clean_cache((*s).lmc);
        free((*s).lmc as *mut c_void);
    }
    #[cfg(not(feature = "longest-match-cache"))]
    fn clean_cache(_s: *mut BlockState) { }
    clean_cache(&mut s);

    clean_lz77_store(&mut store);
}

unsafe fn deflate_non_compressed_block(_options: *const Options, is_final: bool, in_: *const u8, instart: usize, inend: usize, bp: *mut u8, out: *mut *mut u8, outsize: *mut usize) {
    let blocksize: usize = inend - instart;
    let nlen: u16 = !blocksize as u16;

    assert!(blocksize < 65536); // Non compressed blocks are max this size.
    add_bit(if is_final { 1 } else { 0 }, bp, out, outsize);
    // BTYPE 00
    add_bit(0, bp, out, outsize);
    add_bit(0, bp, out, outsize);

    // Any bits of input up to the next byte boundary are ignored.
    *bp = 0;

    append_data!((blocksize % 256) as u8, *out, *outsize);
    append_data!(((blocksize / 256) % 256) as u8, *out, *outsize);
    append_data!((nlen % 256) as u8, *out, *outsize);
    append_data!(((nlen / 256) % 256) as u8, *out, *outsize);

    for i in instart..inend {
        append_data!(*in_.offset(i as isize), *out, *outsize);
    }
}

unsafe fn deflate_block(options: *const Options, btype: i32, is_final: bool, in_: *const u8, instart: usize, inend: usize, bp: *mut u8, out: *mut *mut u8, outsize: *mut usize) {
    if btype == 0 {
        deflate_non_compressed_block(options, is_final, in_, instart, inend, bp, out, outsize);
    } else if btype == 1 {
        deflate_fixed_block(options, is_final, in_, instart, inend, bp, out, outsize);
    } else {
        deflate_dynamic_block(options, is_final, in_, instart, inend, bp, out, outsize);
    }
}

/// Does squeeze strategy where first block splitting is done, then each block is
/// squeezed.
/// Parameters: see description of the ZopfliDeflate function.
unsafe fn deflate_splitting_first(options: *const Options, btype: i32, is_final: bool, in_: *const u8, instart: usize, inend: usize, bp: *mut u8, out: *mut *mut u8, outsize: *mut usize) {
    let mut splitpoints: *mut usize = null_mut();
    let mut npoints: usize = 0;
    if btype == 0 {
        block_split_simple(in_, instart, inend, 65535, &mut splitpoints, &mut npoints);
    } else if btype == 1 {
        // If all blocks are fixed tree, splitting into separate blocks only
        // increases the total size. Leave npoints at 0, this represents 1 block.
    } else {
        block_split(options, in_, instart, inend, (*options).blocksplittingmax as usize, &mut splitpoints, &mut npoints);
    }

    for i in 0..npoints+1 {
        let start: usize = if i == 0 { instart } else { *splitpoints.offset(i as isize - 1) };
        let end: usize = if i == npoints { inend } else { *splitpoints.offset(i as isize) };
        deflate_block(options, btype, i == npoints && is_final, in_, start, end, bp, out, outsize);
    }

    free(splitpoints as *mut c_void);
}

/// Does squeeze strategy where first the best possible lz77 is done, and then based
/// on that data, block splitting is done.
/// Parameters: see description of the ZopfliDeflate function.
unsafe fn deflate_splitting_last(options: *const Options, btype: i32, is_final: bool, in_: *const u8, instart: usize, inend: usize, bp: *mut u8, out: *mut *mut u8, outsize: *mut usize) {
    #[cfg(feature = "longest-match-cache")]
    unsafe fn create_block_state(options: *const Options, instart: usize, inend: usize, blocksize: usize) -> BlockState {
        BlockState::new(options, instart, inend, LongestMatchCache::new(blocksize))
    }
    #[cfg(not(feature = "longest-match-cache"))]
    fn create_block_state(options: *const Options, instart: usize, inend: usize, _blocksize: usize) -> BlockState {
        BlockState::new(options, instart, inend, null_mut())
    }
    let mut s = create_block_state(options, instart, inend, inend - instart);

    let mut store = LZ77Store::new();

    if btype == 0 {
        // This function only supports LZ77 compression. DeflateSplittingFirst
        // supports the special case of noncompressed data. Punt it to that one.
        deflate_splitting_first(options, btype, is_final, in_, instart, inend, bp, out, outsize);
    }
    assert!(btype == 1 || btype == 2);

    if btype == 2 {
        lz77_optimal(&s, in_, instart, inend, &mut store);
    } else {
        assert_eq!(btype, 1);
        lz77_optimal_fixed(&mut s, in_, instart, inend, &mut store);
    }

    let mut splitpoints: *mut usize = null_mut();
    let mut npoints: usize = 0;
    if btype == 1 {
        // If all blocks are fixed tree, splitting into separate blocks only
        // increases the total size. Leave npoints at 0, this represents 1 block.
    } else {
        block_split_lz77(options, store.litlens, store.dists, store.size, (*options).blocksplittingmax as usize, &mut splitpoints, &mut npoints);
    }

    for i in 0..npoints+1 {
        let start: usize = if i == 0 { 0 } else { *splitpoints.offset(i as isize - 1) };
        let end: usize = if i == npoints { store.size } else { *splitpoints.offset(i as isize) };
        add_lz77_block(options, btype, i == npoints && is_final, store.litlens, store.dists, start, end, 0, bp, out, outsize);
    }

    #[cfg(feature = "longest-match-cache")]
    unsafe fn clean_cache(s: *mut BlockState) {
        cache::clean_cache((*s).lmc);
        free((*s).lmc as *mut c_void);
    }
    #[cfg(not(feature = "longest-match-cache"))]
    fn clean_cache(_s: *mut BlockState) { }
    clean_cache(&mut s);

    clean_lz77_store(&mut store);
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
unsafe fn deflate_part(options: *const Options, btype: i32, is_final: bool, input: *const u8, instart: usize, inend: usize, bp: *mut u8, out: *mut *mut u8, outsize: *mut usize) {
    if (*options).blocksplitting {
        if (*options).blocksplittinglast {
            deflate_splitting_last(options, btype, is_final, input, instart, inend, bp, out, outsize);
        } else {
            deflate_splitting_first(options, btype, is_final, input, instart, inend, bp, out, outsize);
        }
    } else {
        deflate_block(options, btype, is_final, input, instart, inend, bp, out, outsize);
    }
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
    let offset: usize = *outsize;

    if util::MASTER_BLOCK_SIZE == 0 {
        deflate_part(options, btype, is_final, input, 0, insize, bp, out, outsize);
    } else {
        let mut i: usize = 0;
        while i < insize {
            let masterfinal: bool = i + util::MASTER_BLOCK_SIZE >= insize;
            let final2: bool = is_final && masterfinal;
            let size: usize = if masterfinal { insize - i } else { util::MASTER_BLOCK_SIZE };
            deflate_part(options, btype, final2, input, i, i + size, bp, out, outsize);
            i += size;
        }
    }

    if (*options).verbose {
        println_err!("Original Size: {}, Deflate: {}, Compression: {}% Removed", insize, *outsize - offset, 100.0 * (insize as isize - (*outsize - offset) as isize) as f64 / insize as f64);
    }
}
