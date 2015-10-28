//! Functions to choose good boundaries for block splitting. Deflate allows
//! encoding the data in multiple blocks, with a separate Huffman tree for each
//! block. The Huffman tree itself requires some bytes to encode, so by
//! choosing certain blocks, you can either hurt, or enhance compression. These
//! functions choose good ones that enhance it.

use std::io::Write;
use std::iter;
use std::mem::uninitialized;
use std::ptr::null_mut;

use super::Options;

use deflate::calculate_block_size;
use lz77::{BlockState, LZ77Store, lz77_greedy};
use util;

/// Finds minimum of function f(i) where is is of type size_t, f(i) is of type
/// double, i is in range start-end (excluding end).
unsafe fn find_minimum<F>(f: F, start: usize, end: usize) -> usize
    where F: Fn(usize) -> f64
{

    if end - start < 1024 {
        let mut best: f64 = util::LARGE_FLOAT;
        let mut result = start;
        for i in start..end {
            let v = f(i);
            if v < best {
                best = v;
                result = i;
            }
        }
        result
    } else {
        // Try to find minimum faster by recursively checking multiple points.

        // Good value: 9.
        const NUM: usize = 9;

        let mut p: [usize; NUM] = uninitialized();
        let mut vp: [f64; NUM] = uninitialized();
        let mut lastbest: f64 = util::LARGE_FLOAT;
        let mut pos = start;

        let mut start = start;
        let mut end = end;
        loop {
            if end - start <= NUM {
                break;
            }

            for i in 0..NUM {
                p[i] = start + (i + 1) * ((end - start) / (NUM + 1));
                vp[i] = f(p[i]);
            }
            let mut besti: usize = 0;
            let mut best: f64 = vp[0];
            for i in 1..NUM {
                if vp[i] < best {
                    best = vp[i];
                    besti = i;
                }
            }
            if best > lastbest {
                break;
            }

            start = if besti == 0 { start } else { p[besti - 1] };
            end = if besti == NUM - 1 { end } else { p[besti + 1] };

            pos = p[besti];
            lastbest = best;
        }
        pos
    }
}

/**
 * Returns estimated cost of a block in bits.  It includes the size to encode the
 * tree and the size to encode all literal, length and distance symbols and their
 * extra bits.
 *
 * litlens: lz77 lit/lengths
 * dists: ll77 distances
 * lstart: start of block
 * lend: end of block (not inclusive)
 */
unsafe fn estimate_cost(litlens: &Vec<u16>, dists: &Vec<u16>, lstart: usize, lend: usize) -> f64 {
    calculate_block_size(litlens, dists, lstart, lend, 2)
}

struct SplitCostContext<'a> {
    litlens: &'a Vec<u16>,
    dists: &'a Vec<u16>,
    _llsize: usize,
    start: usize,
    end: usize,
}

/// Gets the cost which is the sum of the cost of the left and the right section
/// of the data.
/// type: FindMinimumFun
unsafe fn split_cost(i: usize, c: &SplitCostContext) -> f64 {
    estimate_cost(c.litlens, c.dists, c.start, i) + estimate_cost(c.litlens, c.dists, i, c.end)
}

unsafe fn add_sorted(value: usize, out: &mut Vec<usize>) {
    out.push(value);
    let mut i: usize = 0;
    while i + 1 < out.len() {
        if out[i] > value {
            let mut j: usize = out.len() - 1;
            while j > i {
                out[j] = out[j - 1];
                j -= 1;
            }
            out[i] = value;
            break;
        }
        i += 1;
    }
}

/// Prints the block split points as decimal and hex values in the terminal.
fn print_block_split_points(litlens: &Vec<u16>,
                            dists: &Vec<u16>,
                            llsize: usize,
                            lz77splitpoints: &Vec<usize>) {
    let mut splitpoints: Vec<usize> = Vec::new();

    // The input is given as lz77 indices, but we want to see the uncompressed
    // index values.
    let mut pos: usize = 0;
    if lz77splitpoints.len() > 0 {
        for i in 0..llsize {
            let length: usize = if dists[i] == 0 { 1 } else { litlens[i] as usize };
            if lz77splitpoints[splitpoints.len()] == i {
                splitpoints.push(pos);
                if splitpoints.len() == lz77splitpoints.len() {
                    break;
                }
            }
            pos += length;
        }
    }
    assert_eq!(splitpoints.len(), lz77splitpoints.len());

    print_err!("block split points: ");
    for i in 0..splitpoints.len() {
        print_err!("{} ", splitpoints[i] as i32);
    }
    print_err!("(hex:");
    for i in 0..splitpoints.len() {
        print_err!(" {:x}", splitpoints[i] as i32);
    }
    println_err!(")");
}

/// Finds next block to try to split, the largest of the available ones.
/// The largest is chosen to make sure that if only a limited amount of blocks is
/// requested, their sizes are spread evenly.
/// llsize: the size of the LL77 data, which is the size of the done array here.
/// done: array indicating which blocks starting at that position are no longer
///     splittable (splitting them increases rather than decreases cost).
/// splitpoints: the splitpoints found so far.
/// npoints: the amount of splitpoints found so far.
/// lstart: output variable, giving start of block.
/// lend: output variable, giving end of block.
/// returns 1 if a block was found, 0 if no block found (all are done).
unsafe fn find_largest_splittable_block(llsize: usize,
                                        done: &Vec<u8>,
                                        splitpoints: &Vec<usize>,
                                        lstart: *mut usize,
                                        lend: *mut usize)
                                        -> bool {
    assert_eq!(llsize, done.len());
    let mut longest: usize = 0;
    let mut found = false;
    for i in 0..splitpoints.len()+1 {
        let start: usize = if i == 0 { 0 } else { splitpoints[i - 1] };
        let end: usize = if i == splitpoints.len() { llsize - 1 } else { splitpoints[i] };
        if done[start] == 0 && end - start > longest {
            *lstart = start;
            *lend = end;
            found = true;
            longest = end - start;
        }
    }
    found
}

/// Does blocksplitting on LZ77 data.
/// The output splitpoints are indices in the LZ77 data.
/// litlens: lz77 lit/lengths
/// dists: lz77 distances
/// llsize: size of litlens and dists
/// maxblocks: set a limit to the amount of blocks. Set to 0 to mean no limit.
pub unsafe fn block_split_lz77(options: *const Options,
                               litlens: &mut Vec<u16>,
                               dists: &mut Vec<u16>,
                               llsize: usize,
                               maxblocks: usize,
                               splitpoints: &mut Vec<usize>) {
    if llsize < 10 {
        // This code fails on tiny files.
        return;
    }

    let mut done: Vec<u8> = iter::repeat(0).take(llsize).collect();

    let mut lstart: usize = 0;
    let mut lend: usize = llsize;
    let mut numblocks: usize = 1;
    loop {
        if maxblocks > 0 && numblocks >= maxblocks {
            break;
        }

        let c = SplitCostContext {
            litlens: litlens,
            dists: dists,
            _llsize: llsize,
            start: lstart,
            end: lend,
        };
        assert!(lstart < lend);
        let llpos: usize = find_minimum(|i| split_cost(i, &c), lstart + 1, lend);

        assert!(llpos > lstart);
        assert!(llpos < lend);

        let splitcost: f64 = estimate_cost(litlens, dists, lstart, llpos) +
                             estimate_cost(litlens, dists, llpos, lend);
        let origcost: f64 = estimate_cost(litlens, dists, lstart, lend);

        if splitcost > origcost || llpos == lstart + 1 || llpos == lend {
            done[lstart] = 1;
        } else {
            add_sorted(llpos, splitpoints);
            numblocks += 1;
        }

        if !find_largest_splittable_block(llsize, &done, splitpoints, &mut lstart, &mut lend) {
            // No further split will probably reduce compression.
            break;
        }

        if lend - lstart < 10 {
            break;
        }
    }

    if (*options).verbose {
        print_block_split_points(litlens, dists, llsize, splitpoints);
    }
}

/**
 * Does blocksplitting on uncompressed data.
 * The output splitpoints are indices in the uncompressed bytes.
 *
 * options: general program options.
 * in: uncompressed input data
 * instart: where to start splitting
 * inend: where to end splitting (not inclusive)
 * maxblocks: maximum amount of blocks to split into, or 0 for no limit
 * splitpoints: dynamic array to put the resulting split point coordinates into.
 *   The coordinates are indices in the input array.
 * npoints: pointer to amount of splitpoints, for the dynamic array. The amount of
 *   blocks is the amount of splitpoitns + 1.
 */
pub unsafe fn block_split(options: *const Options,
                          in_: &[u8],
                          instart: usize,
                          inend: usize,
                          maxblocks: usize,
                          splitpoints: &mut Vec<usize>) {
    let s = BlockState::new(options, instart, inend, null_mut());
    let mut lz77splitpoints: Vec<usize> = Vec::new();
    let mut store = LZ77Store::new();

    splitpoints.clear();

    // Unintuitively, Using a simple LZ77 method here instead of ZopfliLZ77Optimal
    // results in better blocks.
    lz77_greedy(&s, in_, instart, inend, &mut store);

    let store_size = store.litlens.len();
    block_split_lz77(options,
                     &mut store.litlens,
                     &mut store.dists,
                     store_size,
                     maxblocks,
                     &mut lz77splitpoints);

    // Convert LZ77 positions to positions in the uncompressed input.
    let mut pos: usize = instart;
    if lz77splitpoints.len() > 0 {
        for i in 0..store.litlens.len() {
            let length: usize = if store.dists[i] == 0 { 1 } else { store.litlens[i] as usize };
            if lz77splitpoints[splitpoints.len()] == i {
                splitpoints.push(pos);
                if splitpoints.len() == lz77splitpoints.len() {
                    break;
                }
            }
            pos += length;
        }
    }
    assert_eq!(splitpoints.len(), lz77splitpoints.len());
}

/// Divides the input into equal blocks, does not even take LZ77 lengths into
/// account.
pub fn block_split_simple(_in: &[u8],
                          instart: usize,
                          inend: usize,
                          blocksize: usize,
                          splitpoints: &mut Vec<usize>) {
    let mut i: usize = instart;
    while i < inend {
        splitpoints.push(i);
        i += blocksize;
    }
}
