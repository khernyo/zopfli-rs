#![macro_use]
#![cfg_attr(all(test, feature = "nightly"), feature(test))]

#[macro_use]
extern crate log;
extern crate libc;

#[cfg(all(feature = "nightly", test))]
extern crate test;

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
    /// No longer used, left for compatibility.
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
pub unsafe fn compress(options: &Options, output_type: Format, input: &[u8]) -> Vec<u8> {
    match output_type {
        Format::GZIP    => gzip_container::compress(options, input),
        Format::ZLIB    => zlib_container::compress(options, input),
        Format::DEFLATE => {
            let mut bp: u8 = 0;
            let mut out = Vec::new();
            deflate::deflate(options, 2 /* Dynamic block */, true, input, &mut bp, &mut out);
            out
        },
    }
}

#[cfg(test)]
mod tests {
    extern crate flate2;

    use std::io::Read;

    use self::flate2::read::{DeflateDecoder, GzDecoder, ZlibDecoder};

    use super::*;

    fn roundtrip(format: Format, bytes: &[u8]) {
        let options = Options {
            verbose: false,
            verbose_more: false,
            ..Options::new()
        };
        let compressed = unsafe { compress(&options, format, bytes) };
        let decompressed = match format {
            Format::GZIP => {
                let mut d = GzDecoder::new(&compressed[..]).unwrap();
                let mut s = Vec::new();
                d.read_to_end(&mut s).unwrap();
                s
            }
            Format::ZLIB => {
                let mut d = ZlibDecoder::new(&compressed[..]);
                let mut s = Vec::new();
                d.read_to_end(&mut s).unwrap();
                s
            }
            Format::DEFLATE => {
                let mut d = DeflateDecoder::new(&compressed[..]);
                let mut s = Vec::new();
                d.read_to_end(&mut s).unwrap();
                s
            }
        };
        assert_eq!(decompressed, bytes);
    }

    #[test]
    fn roundtrips() {
        for format in vec![Format::GZIP, Format::ZLIB, Format::DEFLATE] {
                roundtrip(format, b"");
            roundtrip(format, b"1");
            roundtrip(format, b"foobar");
        }
    }

    fn expect_compressed(format: Format, data: &[u8], compressed: &[u8]) {
        let options = Options {
            verbose: false,
            verbose_more: false,
            ..Options::new()
        };
        let result = unsafe { compress(&options, format, data) };
        assert_eq!(result, compressed);
    }

    #[test]
    fn test_compression() {
        expect_compressed(Format::DEFLATE,
                          b"44098c409eb5a2f2",
                          &[0x33, 0x31, 0x31, 0xb0, 0xb4, 0x48, 0x06, 0x12, 0xa9, 0x49, 0xa6,
                            0x89, 0x46, 0x69, 0x46, 0x00]);

        expect_compressed(Format::DEFLATE,
                          b"0ff2837fae317edf2d54e4b31d62db77731ecf48\n",
                          &[0x04, 0xc1, 0x05, 0x01, 0x00, 0x30, 0x0c, 0x03, 0x30, 0x49, 0xa7, 0x91,
                            0x9c, 0x61, 0xfd, 0x4b, 0x78, 0xb2, 0x81, 0x6b, 0x4f, 0x11, 0xf3, 0x8e,
                            0x4e, 0xe3, 0x36, 0xd3, 0x50, 0xbe, 0xd3, 0x72, 0x3b, 0x55, 0xf5, 0x9d,
                            0x29, 0x90, 0xfd, 0x71, 0x01, 0x00]);

        expect_compressed(Format::DEFLATE,
                          b"c9649845430e0fa797c0c5a92dfd2441de149915\n",
                          &[0x04, 0xc1, 0x05, 0x01, 0x00, 0x20, 0x0c, 0x00, 0xb0, 0x48, 0xd8, 0xb5,
                            0xcd, 0xbd, 0x7f, 0x04, 0xb6, 0x54, 0x02, 0x15, 0x40, 0x78, 0xbb, 0xf7,
                            0x38, 0x2b, 0xe7, 0x4e, 0x74, 0xbd, 0x35, 0x75, 0x01, 0x4e, 0xf5, 0x01,
                            0xd5, 0x83, 0x7f, 0x5c, 0x00]);

        expect_compressed(Format::DEFLATE,
                          b"cad2e7d23285aff3cdb6d74df817c4c920e04cc2\n",
                          &[0x05, 0xc1, 0x47, 0x01, 0xc0, 0x30, 0x0c, 0x04, 0xb0, 0x7f, 0xc9,
                            0x64, 0x0f, 0xc3, 0x71, 0x6f, 0xf0, 0x87, 0x10, 0x09, 0xc9, 0xae,
                            0xc3, 0x3e, 0xfa, 0x5d, 0x69, 0x0f, 0xf0, 0xdf, 0x3c, 0x93, 0xbe,
                            0xed, 0x60, 0x22, 0x7a, 0x55, 0x9d, 0x40, 0xff, 0x1e]);

        expect_compressed(Format::DEFLATE, b"# pack-refs with: peeled fully-peeled \nd676b34c3299da9200516d98fc6399205195e1b0 refs/heads/master\n",
                          &[0x2d, 0x8c, 0xb5, 0x01, 0x02, 0x31, 0x14, 0x86, 0xfb, 0x9b, 0x22, 0xd2,
                            0xc6, 0xfd, 0x31, 0x4d, 0x0c, 0x77, 0x87, 0xe9, 0xd1, 0xeb, 0x7e, 0xfd,
                            0x28, 0x3a, 0x94, 0xb6, 0xe6, 0xa7, 0xe9, 0xec, 0x8c, 0xee, 0xcb, 0xcb,
                            0x62, 0x82, 0x0e, 0xd3, 0xe9, 0x66, 0xda, 0xd1, 0xec, 0xba, 0xd9, 0x3c,
                            0xf9, 0x68, 0x86, 0x1e, 0x62, 0xa8, 0xd6, 0x35, 0x6b, 0x00, 0x7a, 0x01,
                            0xa3, 0x94, 0xd7, 0xa1, 0x43, 0x9a, 0xb5, 0x60, 0x01, 0xcc, 0xc7, 0x81,
                            0x9f, 0xea, 0xaa, 0xd0, 0x17, 0x24, 0x17, 0xd3, 0xd2, 0xcf, 0x72, 0x5b,
                            0xce, 0x97, 0xe9, 0x69, 0x78, 0x03]);
    }
}
