#[macro_use]
extern crate zopfli;
extern crate libc;

use std::env;
use std::fs::File;
use std::io::{Read, Write};
use std::ptr;
use std::ptr::null_mut;
use std::slice;

use libc::{c_void, size_t};
use libc::funcs::c95::stdlib::{free, malloc};

use zopfli::*;

fn main() {
    unsafe {
        let mut options = Options::new();
        let mut output_type = Format::GZIP;
        let mut output_to_stdout = false;

        for arg in env::args().skip(1) {
            if arg == "-v" {
                options.verbose = true;
            } else if arg == "-c" {
                output_to_stdout = true;
            } else if arg == "--deflate" {
                output_type = Format::DEFLATE;
            } else if arg == "--zlib" {
                output_type = Format::ZLIB;
            } else if arg == "--gzip" {
                output_type = Format::GZIP;
            } else if arg == "--splitlast" {
                options.blocksplittinglast = true;
            } else if arg.starts_with("--i") && arg.len() > 3 && arg.chars().nth(3).unwrap() >= '0' && arg.chars().nth(3).unwrap() <= '9' {
                options.numiterations = i32::from_str_radix(&arg[3..], 10).unwrap();
            } else if arg == "-h" {
                println_err!("\
Usage: zopfli [OPTION]... FILE...
  -h    gives this help
  -c    write the result on standard output, instead of disk filename + '.gz'
  -v    verbose mode
  --i#  perform # iterations (default 15). More gives more compression but is slower. Examples: --i10, --i50, --i1000
  --gzip        output to gzip format (default)
  --zlib        output to zlib format instead of gzip
  --deflate     output to deflate format instead of gzip
  --splitlast   do block splitting last instead of first");
                std::process::exit(1);
            }
        }

        if options.numiterations < 1 {
            println_err!("Error: must have 1 or more iterations");
            std::process::exit(1);
        }

        let mut got_filename = false;
        for arg in env::args().skip(1) {
            if arg.chars().next().unwrap() != '-' {
                got_filename = true;
                let filename = arg.to_owned();
                let outfilename =
                    match &output_type {
                        _ if output_to_stdout => None,
                        &Format::GZIP         => Some(filename.clone() + ".gz"),
                        &Format::ZLIB         => Some(filename.clone() + ".zlib"),
                        &Format::DEFLATE      => Some(filename.clone() + ".deflate"),
                    };
                match outfilename {
                    Some(ref f) if options.verbose => println_err!("Saving to: {}", f),
                    _ => (),
                }
                compress_file(&mut options, output_type, &filename, outfilename);
            }
        }

        if !got_filename {
            println_err!("Please provide filename\nFor help, type: {} -h", env::args().next().unwrap());
            std::process::exit(1);
        }
    }
}

/// outfilename: filename to write output to, or 0 to write to stdout instead
unsafe fn compress_file(options: *const Options, output_type: Format, infilename: &str, outfilename: Option<String>) {
    let mut input: *mut u8 = null_mut();
    let mut insize: usize = 0;
    load_file(infilename, &mut input, &mut insize);
    if insize == 0 {
        println_err!("Invalid filename: {}", infilename);
    } else {
        let mut output: *mut u8 = null_mut();
        let mut outsize: usize = 0;
        compress(options, output_type, input, insize, &mut output, &mut outsize);

        if let Some(f) = outfilename {
            save_file(&f, output, outsize);
        } else {
            std::io::stdout().write(slice::from_raw_parts(output, outsize)).unwrap();
        }
        free(output as *mut c_void);
        free(input as *mut c_void);
    }
}

unsafe fn load_file(filename: &str, buf: *mut *mut u8, size: *mut usize) {
    let mut f = File::open(filename).unwrap();
    *size = f.metadata().unwrap().len() as usize;
    if *size > 2147483647 {
        println_err!("Files larger than 2GB are not supported.");
        std::process::exit(1);
    }
    let mut b = Vec::new();
    assert_eq!(f.read_to_end(&mut b).unwrap(), *size);
    *buf = malloc(*size as size_t) as *mut u8;
    ptr::copy_nonoverlapping(b.as_ptr(), *buf, *size);
}

unsafe fn save_file(filename: &str, buf: *mut u8, size: usize) {
    let mut f = File::create(filename).unwrap();
    f.write(slice::from_raw_parts(buf, size)).unwrap();
}
