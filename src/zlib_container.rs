use std::mem;
use std::ptr;

use libc::{c_void, size_t};
use libc::funcs::c95::stdlib::{free, malloc};

use super::Options;

pub unsafe fn compress(options: *const Options, input: *const u8, insize: usize, out: *mut *mut u8, outsize: *mut usize) {
    *out = mem::transmute(malloc(insize as u64));
    ptr::copy_nonoverlapping(input, *out, insize);
    *outsize = insize;
}
