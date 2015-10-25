#![macro_use]

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

    fn expect_compressed(format: Format, data: &[u8], compressed: &[u8]) {
        unsafe {
            let options = Options { verbose: false, verbose_more: false, .. Options::new() };
            let mut result: *mut u8 = null_mut();
            let mut result_size: usize = 0;
            compress(&options, format, data.as_ptr(), data.len(), &mut result, &mut result_size);
            assert_eq!(slice::from_raw_parts(result, result_size), compressed);
        }
    }

    #[test]
    fn test_compression() {
        expect_compressed(Format::DEFLATE, b"44098c409eb5a2f2", &[0x33, 0x31, 0x31, 0xb0, 0xb4, 0x48, 0x06, 0x12, 0xa9, 0x49, 0xa6, 0x89, 0x46, 0x69, 0x46, 0x00]);

        expect_compressed(Format::DEFLATE, b"0ff2837fae317edf2d54e4b31d62db77731ecf48\n",
                          &[0x05, 0xc1, 0x45, 0x01, 0xc0, 0x50, 0x0c, 0x05, 0xb0, 0xfb, 0xcc, 0x7c,
                            0x2a, 0xc9, 0x29, 0x3e, 0xff, 0x12, 0x96, 0x6c, 0xe0, 0xda, 0x53, 0xc4,
                            0xbc, 0xa3, 0xd3, 0xb8, 0xcd, 0x34, 0x94, 0xef, 0xb4, 0xdc, 0x4e, 0x55,
                            0x7d, 0x67, 0x0a, 0x64, 0xdf, 0x0f]);

        expect_compressed(Format::DEFLATE, b"c9649845430e0fa797c0c5a92dfd2441de149915\n",
                          &[0x05, 0xc1, 0x45, 0x01, 0xc0, 0x40, 0x0c, 0x00, 0xb0, 0xff, 0xcc, 0x1c,
                            0x15, 0xdd, 0x94, 0xfd, 0x4b, 0x58, 0x92, 0x4a, 0xa0, 0x02, 0x08, 0x6f,
                            0xf7, 0x1e, 0x67, 0xe5, 0xdc, 0x89, 0xae, 0xb7, 0xa6, 0x2e, 0xc0, 0xa9,
                            0x3e, 0xa0, 0x7a, 0xf0, 0xfb, 0x01]);

        expect_compressed(Format::DEFLATE, b"cad2e7d23285aff3cdb6d74df817c4c920e04cc2\n",
                          &[0x05, 0xc1, 0x47, 0x01, 0xc0, 0x30, 0x0c, 0x04, 0xb0, 0x7f, 0xc9, 0x64,
                            0x0f, 0xc3, 0x71, 0x6f, 0xf0, 0x87, 0x10, 0x09, 0xc9, 0xae, 0xc3, 0x3e,
                            0xfa, 0x5d, 0x69, 0x0f, 0xf0, 0xdf, 0x3c, 0x93, 0xbe, 0xed, 0x60, 0x22,
                            0x7a, 0x55, 0x9d, 0x40, 0xff, 0x1e]);
    }
}
