//! Functions to choose good boundaries for block splitting. Deflate allows encoding
//! the data in multiple blocks, with a separate Huffman tree for each block. The
//! Huffman tree itself requires some bytes to encode, so by choosing certain
//! blocks, you can either hurt, or enhance compression. These functions choose good
//! ones that enhance it.

use std::io::Write;
use std::mem::{transmute, uninitialized};
use std::ptr::null_mut;

use libc::{c_void, size_t};
use libc::funcs::c95::stdlib::{free, malloc};

use super::Options;

use deflate::calculate_block_size;
use lz77::{BlockState, LZ77Store, lz77_greedy, clean_lz77_store};
use util;

/// The "f" for the FindMinimum function below.
/// i: the current parameter of f(i)
/// context: for your implementation
type FindMinimumFun = unsafe fn(i: usize, context: *const c_void) -> f64;

/// Finds minimum of function f(i) where is is of type size_t, f(i) is of type
/// double, i is in range start-end (excluding end).
unsafe fn find_minimum(f: FindMinimumFun, context: *const c_void, start: usize, end: usize) -> usize {
    if end - start < 1024 {
        let mut best: f64 = util::LARGE_FLOAT;
        let mut result = start;
        for i in start..end {
            let v = f(i, context);
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
                vp[i] = f(p[i], context);
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
unsafe fn estimate_cost(litlens: *const u16, dists: *const u16, lstart: usize, lend: usize) -> f64 {
    calculate_block_size(litlens, dists, lstart, lend, 2)
}

struct SplitCostContext {
    litlens: *const u16,
    dists: *const u16,
    llsize: usize,
    start: usize,
    end: usize,
}

/// Gets the cost which is the sum of the cost of the left and the right section
/// of the data.
/// type: FindMinimumFun
unsafe fn split_cost(i: usize, context: *const c_void) -> f64 {
    let c: *const SplitCostContext = transmute(context);
    estimate_cost((*c).litlens, (*c).dists, (*c).start, i) + estimate_cost((*c).litlens, (*c).dists, i, (*c).end)
}

unsafe fn add_sorted(value: usize, out: *mut *mut usize, outsize: *mut usize) {
    append_data!(value, *out, *outsize);
    let mut i: usize = 0;
    while i + 1 < *outsize {
        if *(*out).offset(i as isize) > value {
            let mut j: usize = *outsize - 1;
            while j > i {
                *(*out).offset(j as isize) = *(*out).offset(j as isize - 1);
                j -= 1;
            }
            *(*out).offset(i as isize) = value;
            break;
        }
        i += 1;
    }
}

/// Prints the block split points as decimal and hex values in the terminal.
unsafe fn print_block_split_points(litlens: *const u16, dists: *const u16, llsize: usize, lz77splitpoints: *const usize, nlz77points: usize) {
    let mut splitpoints: *mut usize = null_mut();
    let mut npoints: usize = 0;

    // The input is given as lz77 indices, but we want to see the uncompressed
    // index values.
    let mut pos: usize = 0;
    if nlz77points > 0 {
        for i in 0..llsize {
            let length: usize = if *dists.offset(i as isize) == 0 { 1 } else { *litlens.offset(i as isize) as usize };
            if *lz77splitpoints.offset(npoints as isize) == i {
                append_data!(pos, splitpoints, npoints);
                if npoints == nlz77points {
                    break;
                }
            }
            pos += length;
        }
    }
    assert_eq!(npoints, nlz77points);

    print_err!("block split points: ");
    for i in 0..npoints {
        print_err!("{} ", *splitpoints.offset(i as isize) as i32);
    }
    print_err!("(hex:");
    for i in 0..npoints {
        print_err!(" {:x}", *splitpoints.offset(i as isize) as i32);
    }
    println_err!("");

    free(splitpoints as *mut c_void);
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
unsafe fn find_largest_splittable_block(llsize: usize, done: *const u8, splitpoints: *const usize, npoints: usize, lstart: *mut usize, lend: *mut usize) -> bool {
    let mut longest: usize = 0;
    let mut found = false;
    for i in 0..npoints+1 {
        let start: usize = if i == 0 { 0 } else { *splitpoints.offset(i as isize - 1) };
        let end: usize = if i == npoints { llsize - 1 } else { *splitpoints.offset(i as isize) };
        if *done.offset(start as isize) == 0 && end - start > longest {
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
unsafe fn block_split_lz77(options: *const Options, litlens: *const u16, dists: *const u16, llsize: usize, maxblocks: usize, splitpoints: *mut *mut usize, npoints: *mut usize) {
    if llsize < 10 {
        // This code fails on tiny files.
        return;
    }

    let done: *mut u8 = transmute(malloc(llsize as size_t));
    if done.is_null() {
        panic!("Allocation failed!");
    }
    for i in 0..llsize {
        *done.offset(i as isize) = 0;
    }

    let mut lstart: usize = 0;
    let mut lend: usize = llsize;
    let mut numblocks: usize = 1;
    loop {
        if maxblocks > 0 && numblocks >= maxblocks {
            break;
        }

        let mut c = SplitCostContext {
            litlens: litlens,
            dists: dists,
            llsize: llsize,
            start: lstart,
            end: lend,
        };
        assert!(lstart < lend);
        let llpos: usize = find_minimum(split_cost, &mut c as *mut _ as *mut c_void, lstart + 1, lend);

        assert!(llpos > lstart);
        assert!(llpos < lend);

        let splitcost: f64 = estimate_cost(litlens, dists, lstart, llpos) + estimate_cost(litlens, dists, llpos, lend);
        let origcost: f64 = estimate_cost(litlens, dists, lstart, lend);

        if splitcost > origcost || llpos == lstart + 1 || llpos == lend {
            *done.offset(lstart as isize) = 1;
        } else {
            add_sorted(llpos, splitpoints, npoints);
            numblocks += 1;
        }

        if !find_largest_splittable_block(llsize, done, *splitpoints, *npoints, &mut lstart, &mut lend) {
            // No further split will probably reduce compression.
            break;
        }

        if lend - lstart < 10 {
            break;
        }
    }

    if (*options).verbose {
        print_block_split_points(litlens, dists, llsize, *splitpoints, *npoints);
    }

    free(transmute(done));
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
unsafe fn block_split(options: *const Options, in_: *const u8, instart: usize, inend: usize, maxblocks: usize, splitpoints: *mut *mut usize, npoints: *mut usize) {
    let s = BlockState::new(options, instart, inend, null_mut());
    let mut lz77splitpoints: *mut usize = null_mut();
    let mut nlz77points: usize = 0;
    let mut store = LZ77Store::new();

    *npoints = 0;
    *splitpoints = null_mut();

    // Unintuitively, Using a simple LZ77 method here instead of ZopfliLZ77Optimal
    // results in better blocks.
    lz77_greedy(&s, in_, instart, inend, &mut store);

    block_split_lz77(options, store.litlens, store.dists, store.size, maxblocks, &mut lz77splitpoints, &mut nlz77points);

    // Convert LZ77 positions to positions in the uncompressed input.
    let mut pos: usize = instart;
    if nlz77points > 0 {
        for i in 0..store.size {
            let length: usize = if *store.dists.offset(i as isize) == 0 { 1 } else { *store.litlens.offset(i as isize) as usize };
            if *lz77splitpoints.offset(*npoints as isize) == i {
                append_data!(pos, *splitpoints, *npoints);
                if *npoints == nlz77points {
                    break;
                }
            }
            pos += length;
        }
    }
    assert_eq!(*npoints, nlz77points);

    free(lz77splitpoints as *mut c_void);
    clean_lz77_store(&mut store);
}

/// Divides the input into equal blocks, does not even take LZ77 lengths into
/// account.
unsafe fn block_split_simple(in_: *const u8, instart: usize, inend: usize, blocksize: usize, splitpoints: *mut *mut usize, npoints: *mut usize) {
    let mut i: usize = instart;
    while i < inend {
        append_data!(i, *splitpoints, *npoints);
        i += blocksize;
    }
}
