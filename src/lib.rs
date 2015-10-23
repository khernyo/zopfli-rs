#![macro_use]
#![allow(unused)]

#[macro_use]
extern crate log;
extern crate libc;

mod util;

mod blocksplitter;
#[cfg(feature = "longest-match-cache")]
mod cache;
mod deflate;
mod gzip_container;
mod hash;
mod katajainen;
mod lz77;
mod squeeze;
mod tree;
mod zlib_container;

/// Options used throughout the program.
pub struct Options {
    /// Whether to print output
    pub verbose: bool,
    /// Whether to print more detailed output
    pub verbose_more: bool,
    /// Maximum amount of times to rerun forward and backward pass to optimize LZ77
    /// compression cost. Good values: 10, 15 for small files, 5 for files over
    /// several MB in size or it will be too slow.
    pub numiterations: i32,
    /// If true, splits the data in multiple deflate blocks with optimal choice
    /// for the block boundaries. Block splitting gives better compression. Default:
    /// true (1).
    pub blocksplitting: bool,
    /// If true, chooses the optimal block split points only after doing the iterative
    /// LZ77 compression. If false, chooses the block split points first, then does
    /// iterative LZ77 on each individual block. Depending on the file, either first
    /// or last gives the best compression. Default: false (0).
    pub blocksplittinglast: bool,
    /// Maximum amount of blocks to split into (0 for unlimited, but this can give
    /// extreme results that hurt compression on some files). Default value: 15.
    pub blocksplittingmax: i32,
}

impl Options {
    pub fn new() -> Options {
        Options {
            verbose: false,
            verbose_more: false,
            numiterations: 15,
            blocksplitting: true,
            blocksplittinglast: false,
            blocksplittingmax: 15,
        }
    }
}

/// Output format
#[derive(Clone, Copy)]
pub enum Format {
    GZIP,
    ZLIB,
    DEFLATE,
}

/**
 * Compresses according to the given output format and appends the result to the
 * output.
 * 
 * options: global program options
 * output_type: the output format to use
 * out: pointer to the dynamic output array to which the result is appended. Must
 *   be freed after use
 * outsize: pointer to the dynamic output array size
 */
pub unsafe fn compress(options: *const Options, output_type: Format, input: *const u8, insize: usize, out: *mut *mut u8, outsize: *mut usize) {
    match output_type {
        Format::GZIP    => gzip_container::compress(options, input, insize, out, outsize),
        Format::ZLIB    => zlib_container::compress(options, input, insize, out, outsize),
        Format::DEFLATE => {
            let mut bp: u8 = 0;
            deflate::deflate(options, 2 /* Dynamic block */, true, input, insize, &mut bp, out, outsize)
        },
    }
}

#[cfg(test)]
mod test {
    extern crate flate2;

    use libc::{c_void, size_t};
    use libc::funcs::c95::string::memcmp;
    use std::io::Read;
    use std::ptr::null_mut;
    use std::slice;

    use self::flate2::read::{DeflateDecoder, GzDecoder, ZlibDecoder};
    
    use super::*;
    
    unsafe fn roundtrip(format: Format, bytes: &[u8]) {
        let options = Options { verbose: false, verbose_more: false, .. Options::new() };
        let mut compressed: *mut u8 = null_mut();
        let mut compressed_size: usize = 0;
        compress(&options, format, bytes.as_ptr(), bytes.len(), &mut compressed, &mut compressed_size);
        let decompressed = match format {
            Format::GZIP => {
                let mut d = GzDecoder::new(slice::from_raw_parts(compressed, compressed_size)).unwrap();
                let mut s = Vec::new();
                d.read_to_end(&mut s).unwrap();
                s
            }
            Format::ZLIB => {
                let mut d = ZlibDecoder::new(slice::from_raw_parts(compressed, compressed_size));
                let mut s = Vec::new();
                d.read_to_end(&mut s).unwrap();
                s
            }
            Format::DEFLATE => {
                let mut d = DeflateDecoder::new(slice::from_raw_parts(compressed, compressed_size));
                let mut s = Vec::new();
                d.read_to_end(&mut s).unwrap();
                s
            }
        };
        assert!(memcmp(bytes.as_ptr() as *const c_void, decompressed.as_ptr() as *const c_void, bytes.len() as size_t) == 0);
    }

    #[test]
    fn roundtrips() {
        unsafe {
            for format in vec![Format::GZIP, Format::ZLIB, Format::DEFLATE] {
                roundtrip(format, b"1");
                roundtrip(format, b"foobar");
            }
        }
    }

    #[test]
    #[ignore]
    fn compress_zero_bytes() {
        unsafe {
            for format in vec![Format::GZIP, Format::ZLIB, Format::DEFLATE] {
                roundtrip(format, b"");
            }
        }
    }
}
