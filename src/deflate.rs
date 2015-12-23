//! Functions to compress according to the DEFLATE specification, using the
//! "squeeze" LZ77 compression backend.

use std::io::Write;
use std::iter;

use super::Options;
use util;

use blocksplitter::{block_split, block_split_lz77};

use lz77::{BlockState, LZ77Store, append_lz77_store, lz77_get_byte_range, lz77_get_histogram};
use squeeze::{lz77_optimal, lz77_optimal_fixed};
use tree::{calculate_bit_lengths, lengths_to_symbols};
use util::{get_length_symbol, get_dist_symbol, get_length_extra_bits_value, get_length_extra_bits,
           get_length_symbol_extra_bits, get_dist_symbol_extra_bits, get_dist_extra_bits_value,
           get_dist_extra_bits, NUM_D, NUM_LL};

/// bp = bitpointer, always in range [0, 7].
/// The outsize is number of necessary bytes to encode the bits.
/// Given the value of bp and the amount of bytes, the amount of bits represented
/// is not simply bytesize * 8 + bp because even representing one bit requires a
/// whole byte. It is: (bp == 0) ? (bytesize * 8) : ((bytesize - 1) * 8 + bp)
fn add_bit(bit: i32, bp: &mut u8, out: &mut Vec<u8>) {
    if *bp == 0 {
        out.push(0);
    }
    *out.last_mut().unwrap() |= (bit << *bp) as u8;
    *bp = (*bp + 1) & 7;
}

fn add_bits(symbol: u32, length: u32, bp: &mut u8, out: &mut Vec<u8>) {
    // TODO(lode): make more efficient (add more bits at once).
    for i in 0..length {
        let bit: u32 = (symbol >> i) & 1;
        if *bp == 0 {
            out.push(0);
        }
        *out.last_mut().unwrap() |= (bit << *bp) as u8;
        *bp = (*bp + 1) & 7;
    }
}

/// Adds bits, like AddBits, but the order is inverted. The deflate specification
/// uses both orders in one standard.
fn add_huffman_bits(symbol: u32, length: u32, bp: &mut u8, out: &mut Vec<u8>) {
    // TODO(lode): make more efficient (add more bits at once).
    for i in 0..length {
        let bit: u32 = (symbol >> (length - i - 1)) & 1;
        if *bp == 0 {
            out.push(0);
        }
        *out.last_mut().unwrap() |= (bit << *bp) as u8;
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
fn patch_distance_codes_for_buggy_decoders(d_lengths: &mut [u32]) {
    // Amount of non-zero distance codes
    let mut num_dist_codes: i32 = 0;

    for i in 0..30 /* Ignore the two unused codes from the spec */ {
        if d_lengths[i] != 0 {
            num_dist_codes += 1;
        }
        if num_dist_codes >= 2 {
            // Two or more codes is fine.
            return;
        }
    }

    if num_dist_codes == 0 {
        d_lengths[0] = 1;
        d_lengths[1] = 1;
    } else if num_dist_codes == 1 {
        d_lengths[if d_lengths[0] != 0 { 1 } else { 0 }] = 1;
    }
}

/// Encodes the Huffman tree and returns how many bits its encoding takes. If out
/// is a null pointer, only returns the size and runs faster.
fn encode_tree(ll_lengths: &[u32; 288],
               d_lengths: &[u32; 32],
               use_16: bool,
               use_17: bool,
               use_18: bool,
               bp: Option<&mut u8>,
               out: Option<&mut Vec<u8>>)
               -> usize {
    let mut rle: Vec<u32> = Vec::new(); // Runlength encoded version of lengths of litlen and dist trees.
    let mut rle_bits: Vec<u32> = Vec::new(); // Extra bits for rle values 16, 17 and 18.
    let mut hlit: u32 = 29; // 286 - 257
    let mut hdist: u32 = 29; // 32 - 1, but gzip does not like hdist > 29.
    let mut hclen: u32;
    let mut clcounts: [usize; 19] = [0; 19];

    /// The order in which code length code lengths are encoded as per deflate.
    const ORDER: [u32; 19] = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];

    let size_only = out.is_none();
    assert_eq!(size_only, bp.is_none());
    let mut result_size: usize = 0;

    // Trim zeros.
    while hlit > 0 && ll_lengths[257 + hlit as usize - 1] == 0 {
        hlit -= 1;
    }
    while hdist > 0 && d_lengths[1 + hdist as usize - 1] == 0 {
        hdist -= 1;
    }
    let hlit2: u32 = hlit + 257;

    let lld_total: u32 = hlit2 + hdist + 1; // Total amount of literal, length, distance codes.

    let mut i: usize = 0;
    while i < lld_total as usize {
        // This is an encoding of a huffman tree, so now the length is a symbol
        let symbol: u8 = if i < hlit2 as usize { ll_lengths[i as usize] as u8 } else { d_lengths[i - hlit2 as usize] as u8 };
        let mut count: u32 = 1;
        if use_16 || (symbol == 0 && (use_17 || use_18)) {
            let mut j: usize = i as usize + 1;
            while j < lld_total as usize && symbol == (if j < hlit2 as usize { ll_lengths[j] as u8 } else { d_lengths[j - hlit2 as usize] as u8 }) {
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
                        rle.push(18);
                        rle_bits.push(count2 - 11);
                    }
                    clcounts[18] += 1;
                    count -= count2;
                }
            }
            if use_17 {
                while count >= 3 {
                    let count2: u32 = if count > 10 { 10 } else { count };
                    if !size_only {
                        rle.push(17);
                        rle_bits.push(count2 - 3);
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
                rle.push(symbol as u32);
                rle_bits.push(0);
            }
            while count >= 3 {
                let count2: u32 = if count > 6 { 6 } else { count };
                if !size_only {
                    rle.push(16);
                    rle_bits.push(count2 - 3);
                }
                clcounts[16] += 1;
                count -= count2;
            }
        }

        // No or insufficient repetition
        clcounts[symbol as usize] += count as usize;
        while count > 0 {
            if !size_only {
                rle.push(symbol as u32);
                rle_bits.push(0);
            }
            count -= 1;
        }
        i += 1;
    }

    let mut clcl = [0u32; 19]; // Code length code lengths.
    let mut clsymbols = [0u32; 19];
    calculate_bit_lengths(&clcounts, 19, 7, &mut clcl);
    if !size_only {
        lengths_to_symbols(&clcl, 19, 7, &mut clsymbols);
    }

    hclen = 15;
    // Trim zeros.
    while hclen > 0 && clcounts[ORDER[hclen as usize + 4 - 1] as usize] == 0 {
        hclen -= 1;
    }

    if !size_only {
        let out = out.unwrap();
        let bp = bp.unwrap();
        add_bits(hlit, 5, bp, out);
        add_bits(hdist, 5, bp, out);
        add_bits(hclen, 4, bp, out);

        for i in 0..hclen + 4 {
            add_bits(clcl[ORDER[i as usize] as usize], 3, bp, out);
        }

        for i in 0..rle.len() {
            let symbol: u32 = clsymbols[rle[i] as usize];
            add_huffman_bits(symbol, clcl[rle[i] as usize], bp, out);
            // Extra bits.
            if rle[i] == 16 {
                add_bits(rle_bits[i], 2, bp, out);
            } else if rle[i] == 17 {
                add_bits(rle_bits[i], 3, bp, out);
            } else if rle[i] == 18 {
                add_bits(rle_bits[i], 7, bp, out);
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

    result_size
}

fn add_dynamic_tree(ll_lengths: &[u32; 288], d_lengths: &[u32; 32], bp: &mut u8, out: &mut Vec<u8>) {
    let mut best: i32 = 0;
    let mut bestsize: usize = 0;

    for i in 0..8 {
        let size: usize = encode_tree(ll_lengths, d_lengths, i & 1 != 0, i & 2 != 0, i & 4 != 0, None, None);
        if bestsize == 0 || size < bestsize {
            bestsize = size;
            best = i;
        }
    }

    encode_tree(ll_lengths, d_lengths, best & 1 != 0, best & 2 != 0, best & 4 != 0, Some(bp), Some(out));
}

/// Gives the exact size of the tree, in bits, as it will be encoded in DEFLATE.
fn calculate_tree_size(ll_lengths: &[u32; 288], d_lengths: &[u32; 32]) -> usize {
    let mut result: usize = 0;

    for i in 0..8 {
        let size: usize = encode_tree(ll_lengths, d_lengths, i & 1 != 0, i & 2 != 0, i & 4 != 0, None, None);
        if result == 0 || size < result {
            result = size;
        }
    }

    result
}

/// Adds all lit/len and dist codes from the lists as huffman symbols. Does not add
/// end code 256. expected_data_size is the uncompressed block size, used for
/// assert, but you can set it to 0 to not do the assertion.
fn add_lz77_data(lz77: &LZ77Store,
                 lstart: usize,
                 lend: usize,
                 expected_data_size: usize,
                 ll_symbols: &[u32; 288],
                 ll_lengths: &[u32; 288],
                 d_symbols: &[u32; 32],
                 d_lengths: &[u32; 32],
                 bp: &mut u8,
                 out: &mut Vec<u8>) {
    let mut testlength: usize = 0;
    for i in lstart..lend {
        let dist: u32 = lz77.dists[i] as u32;
        let litlen: u32 = lz77.litlens[i] as u32;
        if dist == 0 {
            assert!(litlen < 256);
            assert!(ll_lengths[litlen as usize] > 0);
            add_huffman_bits(ll_symbols[litlen as usize], ll_lengths[litlen as usize], bp, out);
            testlength += 1;
        } else {
            let lls: u32 = get_length_symbol(litlen as i32) as u32;
            let ds: u32 = get_dist_symbol(dist as i32) as u32;
            assert!(litlen >= 3 && litlen <= 288);
            assert!(ll_lengths[lls as usize] > 0);
            assert!(d_lengths[ds as usize] > 0);
            add_huffman_bits(ll_symbols[lls as usize], ll_lengths[lls as usize], bp, out);
            add_bits(get_length_extra_bits_value(litlen as i32) as u32,
                     get_length_extra_bits(litlen as i32) as u32,
                     bp,
                     out);
            add_huffman_bits(d_symbols[ds as usize], d_lengths[ds as usize], bp, out);
            add_bits(get_dist_extra_bits_value(dist as i32) as u32,
                     get_dist_extra_bits(dist as i32) as u32,
                     bp,
                     out);
            testlength += litlen as usize;
        }
    }
    assert!(expected_data_size == 0 || testlength == expected_data_size);
}

fn get_fixed_tree() -> ([u32; 288], [u32; 32]) {
    let mut ll_lengths: [u32; 288] = [8u32; 288];

    for i in 144..256 {
        ll_lengths[i] = 9;
    }
    for i in 256..280 {
        ll_lengths[i] = 7;
    }

    let d_lengths = [5u32; 32];
    (ll_lengths, d_lengths)
}

/// Calculates size of the part after the header and tree of an LZ77 block, in bits.
fn calculate_block_symbol_size(ll_lengths: &[u32; 288],
                               d_lengths: &[u32; 32],
                               lz77: &LZ77Store,
                               lstart: usize,
                               lend: usize)
                               -> usize {
    let mut result: usize = 0;
    if lstart + NUM_LL * 3 > lend {
        for i in lstart..lend {
            assert!(i < lz77.size);
            assert!(lz77.litlens[i] < 259);
            if lz77.dists[i] == 0 {
                result += ll_lengths[lz77.litlens[i] as usize] as usize;
            } else {
                let ll_symbol: i32 = get_length_symbol(lz77.litlens[i] as i32);
                let d_symbol: i32 = get_dist_symbol(lz77.dists[i] as i32);
                result += ll_lengths[ll_symbol as usize] as usize;
                result += d_lengths[d_symbol as usize] as usize;
                result += get_length_symbol_extra_bits(ll_symbol) as usize;
                result += get_dist_symbol_extra_bits(d_symbol) as usize;
            }
        }
    } else {

    }
    result += ll_lengths[256] as usize; // end symbol
    result
}

fn abs_diff(x: usize, y: usize) -> usize {
    if x > y {
        x - y
    } else {
        y - x
    }
}

/// Change the population counts in a way that the consequent Huffman tree
/// compression, especially its rle-part will be more likely to compress this data
/// more efficiently. length containts the size of the histogram.
fn optimize_huffman_for_rle(counts: &mut [usize]) {
    let mut length: i32 = counts.len() as i32;
    // 1) We don't want to touch the trailing zeros. We may break the
    // rules of the format by adding more data in the distance codes.
    while length >= 0 {
        if length == 0 {
            return;
        }
        if counts[length as usize - 1] != 0 {
            // Now counts[0..length - 1] does not have trailing zeros.
            break;
        }
        length -= 1;
    }
    // 2) Let's mark all population counts that already can be encoded
    // with an rle code.
    let mut good_for_rle: Vec<bool> = iter::repeat(false).take(length as usize).collect();

    // Let's not spoil any of the existing good rle codes.
    // Mark any seq of 0's that is longer than 5 as a good_for_rle.
    // Mark any seq of non-0's that is longer than 7 as a good_for_rle.
    let mut symbol: usize = counts[0];
    let mut stride: i32 = 0;
    for i in 0..length + 1 {
        if i == length || counts[i as usize] != symbol {
            if (symbol == 0 && stride >= 5) || (symbol != 0 && stride >= 7) {
                for k in 0..stride {
                    good_for_rle[i as usize - k as usize - 1] = true;
                }
            }
            stride = 1;
            if i != length {
                symbol = counts[i as usize];
            }
        } else {
            stride += 1;
        }
    }

    // 3) Let's replace those population counts that lead to more rle codes.
    stride = 0;
    let mut limit: usize = counts[0];
    let mut sum: usize = 0;
    for i in 0..length+1 {
        if i == length || good_for_rle[i as usize]
            // Heuristic for selecting the stride ranges to collapse.
            || abs_diff(counts[i as usize], limit) >= 4 {
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
                        counts[i as usize - k as usize - 1] = count as usize;
                    }
                }
                stride = 0;
                sum = 0;
                if i < length - 3 {
                    // All interesting strides have a count of at least 4,
                    // at least when non-zeros.
                    limit = (counts[i as usize] + counts[i as usize + 1] + counts[i as usize + 2] + counts[i as usize + 3] + 2) / 4;
                } else if i < length {
                    limit = counts[i as usize];
                } else {
                    limit = 0;
                }
            }
        stride += 1;
        if i != length {
            sum += counts[i as usize];
        }
    }
}

/// Calculates the bit lengths for the symbols for dynamic blocks. Chooses bit
/// lengths that give the smallest size of tree encoding + encoding of all the
/// symbols to have smallest output size. This are not necessarily the ideal Huffman
/// bit lengths.
fn get_dynamic_lengths(lz77: &LZ77Store, lstart: usize, lend: usize) -> ([u32; 288], [u32; 32]) {
    let (mut ll_counts, mut d_counts) = lz77_get_histogram(lz77, lstart, lend);
    ll_counts[256] = 1;  // End symbol.
    optimize_huffman_for_rle(&mut ll_counts);
    optimize_huffman_for_rle(&mut d_counts);
    let mut ll_lengths = [0u32; NUM_LL];
    calculate_bit_lengths(&ll_counts, NUM_LL, 15, &mut ll_lengths);
    let mut d_lengths = [0u32; NUM_D];
    calculate_bit_lengths(&d_counts, NUM_D, 15, &mut d_lengths);
    patch_distance_codes_for_buggy_decoders(&mut d_lengths);
    (ll_lengths, d_lengths)
}

/// Calculates block size in bits.
/// litlens: lz77 lit/lengths
/// dists: ll77 distances
/// lstart: start of block
/// lend: end of block (not inclusive)
pub fn calculate_block_size(lz77: &LZ77Store, lstart: usize, lend: usize, btype: i32) -> f64 {
    // bfinal and btype bits
    let mut result: f64 = 3.0;

    if btype == 0 {
        let length: usize = lz77_get_byte_range(lz77, lstart, lend);
        let rem: usize = length % 65535;
        let blocks: usize = length / 65535 + (if rem > 0 { 1 } else { 0 });
        // An uncompressed block must actually be split into multiple blocks if it's
        // larger than 65535 bytes long. Eeach block header is 5 bytes: 3 bits,
        // padding, LEN and NLEN (potential less padding for first one ignored).
        return (blocks * 5 * 8 + length * 8) as f64;
    }
    let (ll_lengths, d_lengths) = {
        if btype == 1 {
            get_fixed_tree()
        } else {
            let (ll_lengths, d_lengths) = get_dynamic_lengths(lz77, lstart, lend);
            result += calculate_tree_size(&ll_lengths, &d_lengths) as f64;
            (ll_lengths, d_lengths)
        }
    };

    result += calculate_block_symbol_size(&ll_lengths, &d_lengths, lz77, lstart, lend) as f64;

    result
}

/// Calculates block size in bits, automatically using the best btype.
pub fn calculate_block_size_auto_type(lz77: &LZ77Store, lstart: usize, lend: usize) -> f64 {
    let uncompressedcost: f64 = calculate_block_size(lz77, lstart, lend, 0);
    // Don't do the expensive fixed cost calculation for larger blocks that are
    // unlikely to use it.
    let fixedcost: f64 = if (*lz77).size > 1000 { uncompressedcost } else { calculate_block_size(lz77, lstart, lend, 1) };
    let dyncost: f64 = calculate_block_size(lz77, lstart, lend, 2);
    if uncompressedcost < fixedcost && uncompressedcost < dyncost {
        uncompressedcost
    } else if fixedcost < dyncost {
        fixedcost
    } else {
        dyncost
    }
}

/// Since an uncompressed block can be max 65535 in size, it actually adds
/// multiple blocks if needed.
fn add_non_compressed_block(_options: *const Options, is_final: bool, in_: &[u8], instart: usize, inend: usize, bp: &mut u8, out: &mut Vec<u8>) {
    let mut pos: usize = instart;
    loop {
        let mut blocksize: u16 = 65535;

        if pos + blocksize as usize > inend {
            blocksize = (inend - pos) as u16;
        }
        let currentfinal = pos + blocksize as usize >= inend;

        let nlen: u16 = !blocksize;

        add_bit(if is_final && currentfinal { 1 } else { 0 }, bp, out);
        // BTYPE 00
        add_bit(0, bp, out);
        add_bit(0, bp, out);

        // Any bits of input up to the next byte boundary are ignored.
        *bp = 0;

        out.push((blocksize % 256) as u8);
        out.push(((blocksize / 256) % 256) as u8);
        out.push((nlen % 256) as u8);
        out.push(((nlen / 256) % 256) as u8);

        for i in 0..blocksize {
            out.push(in_[pos + i as usize]);
        }

        if currentfinal { break }
        pos += blocksize as usize;
    }
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
fn add_lz77_block(options: &Options,
                  btype: i32,
                  is_final: bool,
                  lz77: &LZ77Store,
                  lstart: usize,
                  lend: usize,
                  expected_data_size: usize,
                  bp: &mut u8,
                  out: &mut Vec<u8>) {
    if btype == 0 {
        let length: usize = lz77_get_byte_range(lz77, lstart, lend);
        let pos: usize = if lstart == lend { 0 } else { lz77.pos[lstart] };
        let end: usize = pos + length;
        add_non_compressed_block(options, is_final, lz77.data, pos, end, bp, out);
        return
    }
    add_bit(if is_final { 1 } else { 0 }, bp, out);
    add_bit(btype & 1, bp, out);
    add_bit((btype & 2) >> 1, bp, out);


    let (ll_lengths, d_lengths) = {
        if btype == 1 {
            // Fixed block.
            get_fixed_tree()
        } else {
            // Dynamic block.
            assert_eq!(btype, 2);

            let (ll_lengths, d_lengths) = get_dynamic_lengths(lz77, lstart, lend);

            let detect_tree_size: u32 = out.len() as u32;
            add_dynamic_tree(&ll_lengths, &d_lengths, bp, out);
            if options.verbose {
                println_err!("treesize: {}", out.len() - detect_tree_size as usize);
            }
            (ll_lengths, d_lengths)
        }
    };

    let mut ll_symbols = [0u32; NUM_LL];
    lengths_to_symbols(&ll_lengths, NUM_LL, 15, &mut ll_symbols);
    let mut d_symbols = [0u32; NUM_D];
    lengths_to_symbols(&d_lengths, NUM_D, 15, &mut d_symbols);

    let detect_block_size: usize = out.len();
    add_lz77_data(lz77, lstart, lend, expected_data_size, &ll_symbols, &ll_lengths, &d_symbols, &d_lengths, bp, out);

    // End symbol.
    add_huffman_bits(ll_symbols[256], ll_lengths[256], bp, out);

    let mut uncompressed_size: usize = 0;
    for i in lstart..lend {
        uncompressed_size += if lz77.dists[i] == 0 { 1 } else { lz77.litlens[i] } as usize;
    }
    let compressed_size: usize = out.len() - detect_block_size;
    if options.verbose {
        println_err!("compressed block size: {} ({}k) (unc: {})", compressed_size, (compressed_size / 1024), uncompressed_size);
    }
}

fn add_lz77_block_auto_type(options: &Options, is_final: bool, lz77: &LZ77Store,
                            lstart: usize, lend: usize, expected_data_size: usize,
                            bp: &mut u8, out: &mut Vec<u8>) {
    let uncompressedcost: f64 = calculate_block_size(lz77, lstart, lend, 0);
    let mut fixedcost: f64 = calculate_block_size(lz77, lstart, lend, 1);
    let dyncost: f64 = calculate_block_size(lz77, lstart, lend, 2);

    // Whether to perform the expensive calculation of creating an optimal block
    // with fixed huffman tree to check if smaller. Only do this for small blocks or
    // blocks which already are pretty good with fixed huffman tree.
    let expensivefixed = (lz77.size < 1000) || fixedcost <= dyncost * 1.1;

    if lstart == lend {
        // Smallest empty block is represented by fixed block
        add_bits(if is_final { 1 } else { 0 }, 1, bp, out);
        add_bits(1, 2, bp, out);  // btype 01
        add_bits(0, 7, bp, out);  // end symbol has code 0000000
        return;
    }
    let mut fixedstore = LZ77Store::new(lz77.data);
    if expensivefixed {
        // Recalculate the LZ77 with ZopfliLZ77OptimalFixed
        let instart: usize = lz77.pos[lstart];
        let inend: usize = instart + lz77_get_byte_range(lz77, lstart, lend);

        let mut s = BlockState::new(options, instart, inend, true);
        lz77_optimal_fixed(&mut s, lz77.data, instart, inend, &mut fixedstore);
        fixedcost = calculate_block_size(&fixedstore, 0, fixedstore.size, 1);
    }

    if uncompressedcost < fixedcost && uncompressedcost < dyncost {
        add_lz77_block(options, 0, is_final, lz77, lstart, lend, expected_data_size, bp, out);
    } else if fixedcost < dyncost {
        if expensivefixed {
            add_lz77_block(options, 1, is_final, &fixedstore, 0, fixedstore.size, expected_data_size, bp, out);
        } else {
            add_lz77_block(options, 1, is_final, lz77, lstart, lend, expected_data_size, bp, out);
        }
    } else {
        add_lz77_block(options, 2, is_final, lz77, lstart, lend, expected_data_size, bp, out);
    }
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
fn deflate_part(options: &Options, btype: i32, is_final: bool, input: &[u8], instart: usize, inend: usize, bp: &mut u8, out: &mut Vec<u8>) {
    // byte coordinates rather than lz77 index
    let mut splitpoints_uncompressed: Vec<usize> = Vec::new();
    let mut splitpoints: Vec<usize> = Vec::new();
    let mut totalcost: f64 = 0f64;

    // If btype=2 is specified, it tries all block types. If a lesser btype is
    // given, then however it forces that one. Neither of the lesser types needs
    // block splitting as they have no dynamic huffman trees.
    if btype == 0 {
        add_non_compressed_block(options, is_final, input, instart, inend, bp, out);
        return;
    } else if btype == 1 {
        let mut store = LZ77Store::new(input);
        let mut s = BlockState::new(options, instart, inend, true);

        lz77_optimal_fixed(&mut s, input, instart, inend, &mut store);
        add_lz77_block(options, btype, is_final, &store, 0, store.size, 0, bp, out);
        return;
    }

    if options.blocksplitting {
        block_split(options, input, instart, inend, options.blocksplittingmax as usize, &mut splitpoints_uncompressed);
    }

    let mut lz77 = LZ77Store::new(input);

    for i in 0..splitpoints_uncompressed.len() + 1 {
        let start: usize = if i == 0 { instart } else { splitpoints_uncompressed[i - 1] };
        let end: usize = if i == splitpoints_uncompressed.len() { inend } else { splitpoints_uncompressed[i] };
        let mut store = LZ77Store::new(input);
        let mut s = BlockState::new(options, start, end, true);
        lz77_optimal(&mut s, input, start, end, (*options).numiterations, &mut store);
        totalcost += calculate_block_size_auto_type(&store, 0, store.size);

        append_lz77_store(&store, &mut lz77);
        if i < splitpoints_uncompressed.len() {
            splitpoints.push(lz77.size);
        }
    }

    // Second block splitting attempt
    let splitpoints =
        if options.blocksplitting && splitpoints_uncompressed.len() > 1 {
            let mut splitpoints2: Vec<usize> = Vec::new();
            let mut totalcost2: f64 = 0f64;

            block_split_lz77(options, &lz77, options.blocksplittingmax as usize, &mut splitpoints2);

            for i in 0..splitpoints2.len() + 1 {
                let start: usize = if i == 0 { 0 } else { splitpoints2[i - 1] };
                let end: usize = if i == splitpoints2.len() { lz77.size } else { splitpoints2[i] };
                totalcost2 += calculate_block_size_auto_type(&lz77, start, end);
            }

            if totalcost2 < totalcost {
                splitpoints2
            } else {
                splitpoints
            }
        } else {
            splitpoints
        };

    for i in 0..splitpoints_uncompressed.len() + 1 {
        let start: usize = if i == 0 { 0 } else { splitpoints[i - 1] };
        let end: usize = if i == splitpoints_uncompressed.len() { lz77.size } else { splitpoints[i] };
        add_lz77_block_auto_type(options, i == splitpoints_uncompressed.len() && is_final, &lz77, start, end, 0, bp, out);
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
pub fn deflate(options: &Options,
               btype: i32,
               is_final: bool,
               input: &[u8],
               bp: &mut u8,
               out: &mut Vec<u8>) {
    let offset: usize = out.len();

    let insize = input.len();
    if util::MASTER_BLOCK_SIZE == 0 {
        deflate_part(options, btype, is_final, input, 0, insize, bp, out);
    } else {
        let mut i: usize = 0;
        loop {
            let masterfinal: bool = i + util::MASTER_BLOCK_SIZE >= insize;
            let final2: bool = is_final && masterfinal;
            let size: usize = if masterfinal { insize - i } else { util::MASTER_BLOCK_SIZE };
            deflate_part(options, btype, final2, input, i, i + size, bp, out);
            i += size;
            if i >= insize { break }
        }
    }

    let outsize = out.len();
    if (*options).verbose {
        println_err!("Original Size: {}, Deflate: {}, Compression: {}% Removed",
                     insize,
                     outsize - offset,
                     100.0 * (insize as isize - (outsize - offset) as isize) as f64 /
                     insize as f64);
    }
}
