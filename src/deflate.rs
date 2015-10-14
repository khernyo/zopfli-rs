use std::ptr;

use libc::{c_void, size_t};
use libc::funcs::c95::stdlib::{free, malloc};

use super::Options;

pub unsafe fn compress(options: *const Options, btype: i32, is_final: bool, input: *const u8, insize: usize, bp: *mut u8, out: *mut *mut u8, outsize: *mut usize) {
    *out = malloc(insize as u64) as *mut u8;
    ptr::copy_nonoverlapping(input, *out, insize);
    *outsize = insize;
}
