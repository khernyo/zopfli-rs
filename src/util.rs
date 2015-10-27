#![macro_use]

//! Several utilities, including: #defines to try different compression results,
//! basic deflate specification values and generic program options.

/// Minimum and maximum length that can be encoded in deflate.
pub const MAX_MATCH: usize = 258;
pub const MIN_MATCH: usize = 3;

/// The window size for deflate. Must be a power of two. This should be 32768, the
/// maximum possible by the deflate spec. Anything less hurts compression more than
/// speed.
pub const WINDOW_SIZE: usize = 32768;

/// The window mask used to wrap indices into the window. This is why the
/// window size must be a power of two.
pub const WINDOW_MASK: usize = WINDOW_SIZE - 1;

/// A block structure of huge, non-smart, blocks to divide the input into, to allow
/// operating on huge files without exceeding memory, such as the 1GB wiki9 corpus.
/// The whole compression algorithm, including the smarter block splitting, will
/// be executed independently on each huge block.
/// Dividing into huge blocks hurts compression, but not much relative to the size.
/// Set this to, for example, 20MB (20000000). Set it to 0 to disable master blocks.
pub const MASTER_BLOCK_SIZE: usize = 20000000;

/// Used to initialize costs for example
pub const LARGE_FLOAT: f64 = 1e30;

/// For longest match cache. max 256. Uses huge amounts of memory but makes it
/// faster. Uses this many times three bytes per single byte of the input data.
/// This is so because longest match finding has to find the exact distance
/// that belongs to each length for the best lz77 strategy.
/// Good values: e.g. 5, 8.
#[cfg(feature = "longest-match-cache")]
pub const CACHE_LENGTH: usize = 8;

/// limit the max hash chain hits for this hash value. This has an effect only
/// on files where the hash value is the same very often. On these files, this
/// gives worse compression (the value should ideally be 32768, which is the
/// ZOPFLI_WINDOW_SIZE, while zlib uses 4096 even for best level), but makes it
/// faster on some specific files.
/// Good value: e.g. 8192.
pub const MAX_CHAIN_HITS: usize = 8192;

/// Gets the amount of extra bits for the given dist, cfr. the DEFLATE spec.
pub fn get_dist_extra_bits(dist: i32) -> i32 {
    if dist < 5 {
        0
    } else {
        ((31 ^ (dist - 1).leading_zeros()) - 1) as i32 // log2(dist - 1) - 1
    }
}

/// Gets value of the extra bits for the given dist, cfr. the DEFLATE spec.
pub fn get_dist_extra_bits_value(dist: i32) -> i32 {
    if dist < 5 {
        0
    } else {
        let l = 31 ^ (dist - 1).leading_zeros(); // log2(dist - 1)
        (dist - (1 + (1 << l))) & ((1 << (l - 1)) - 1)
    }
}

/// Gets the symbol for the given dist, cfr. the DEFLATE spec.
pub fn get_dist_symbol(dist: i32) -> i32 {
    if dist < 5 {
        dist - 1
    } else {
        let l = 31 ^ (dist - 1).leading_zeros(); // log2(dist - 1)
        let r = ((dist - 1) >> (l - 1)) & 1;
        l as i32 * 2 + r
    }
}

/// Gets the amount of extra bits for the given length, cfr. the DEFLATE spec.
pub fn get_length_extra_bits(l: i32) -> i32 {
    const TABLE: [i32; 259] = [
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1,
        2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
        3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
        3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
        4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
        4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
        4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
        4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
        5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5,
        5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5,
        5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5,
        5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5,
        5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5,
        5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5,
        5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5,
        5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 0];
    TABLE[l as usize]
}

/// Gets value of the extra bits for the given length, cfr. the DEFLATE spec.
pub fn get_length_extra_bits_value(l: i32) -> i32 {
    const TABLE: [i32; 259] = [
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 2, 3, 0,
        1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5,
        6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 4, 5, 6,
        7, 8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12,
        13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2,
        3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
        10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28,
        29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17,
        18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6,
        7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26,
        27, 28, 29, 30, 31, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
        16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 0];
    TABLE[l as usize]
}

/// Gets the symbol for the given length, cfr. the DEFLATE spec.
/// Returns the symbol in the range [257-285] (inclusive)
pub fn get_length_symbol(l: i32) -> i32 {
    static TABLE: [i32; 259] = [
        0, 0, 0, 257, 258, 259, 260, 261, 262, 263, 264,
        265, 265, 266, 266, 267, 267, 268, 268,
        269, 269, 269, 269, 270, 270, 270, 270,
        271, 271, 271, 271, 272, 272, 272, 272,
        273, 273, 273, 273, 273, 273, 273, 273,
        274, 274, 274, 274, 274, 274, 274, 274,
        275, 275, 275, 275, 275, 275, 275, 275,
        276, 276, 276, 276, 276, 276, 276, 276,
        277, 277, 277, 277, 277, 277, 277, 277,
        277, 277, 277, 277, 277, 277, 277, 277,
        278, 278, 278, 278, 278, 278, 278, 278,
        278, 278, 278, 278, 278, 278, 278, 278,
        279, 279, 279, 279, 279, 279, 279, 279,
        279, 279, 279, 279, 279, 279, 279, 279,
        280, 280, 280, 280, 280, 280, 280, 280,
        280, 280, 280, 280, 280, 280, 280, 280,
        281, 281, 281, 281, 281, 281, 281, 281,
        281, 281, 281, 281, 281, 281, 281, 281,
        281, 281, 281, 281, 281, 281, 281, 281,
        281, 281, 281, 281, 281, 281, 281, 281,
        282, 282, 282, 282, 282, 282, 282, 282,
        282, 282, 282, 282, 282, 282, 282, 282,
        282, 282, 282, 282, 282, 282, 282, 282,
        282, 282, 282, 282, 282, 282, 282, 282,
        283, 283, 283, 283, 283, 283, 283, 283,
        283, 283, 283, 283, 283, 283, 283, 283,
        283, 283, 283, 283, 283, 283, 283, 283,
        283, 283, 283, 283, 283, 283, 283, 283,
        284, 284, 284, 284, 284, 284, 284, 284,
        284, 284, 284, 284, 284, 284, 284, 284,
        284, 284, 284, 284, 284, 284, 284, 284,
        284, 284, 284, 284, 284, 284, 284, 285];
    TABLE[l as usize]
}

macro_rules! append_data {
    ($value:expr, $data:expr, $size:expr) => {{
        #[inline]
        unsafe fn append_data<T>(value: T, data: *mut *mut T, size: *mut usize) {
            use ::std::mem::size_of_val;
            use ::libc::{c_void, size_t};
            use ::libc::funcs::c95::stdlib::{malloc, realloc};
            if *size == 0 || (*size).is_power_of_two() {
                // double alloc size if it's a power of two
                *data =
                    if *size == 0 {
                        let malloc_size = size_of_val(&**data) as size_t;
                        ::std::mem::transmute(malloc(malloc_size))
                    } else {
                        let new_size = (*size * 2 * size_of_val(&**data)) as size_t;
                        ::std::mem::transmute(realloc(*data as *mut c_void, new_size))
                    }
            }
            *(*data).offset(*size as isize) = value;
            *size += 1;
        }
        append_data($value, &mut $data, &mut $size);
    }}
}

#[macro_export]
macro_rules! println_err {
    ($($arg:tt)*) => {
        match writeln!(&mut ::std::io::stderr(), $($arg)*) {
            Ok(_)  => (),
            Err(e) => panic!("Unable to write to stderr: {}", e),
        }
    }
}

#[macro_export]
macro_rules! print_err {
    ($($arg:tt)*) => {
        match write!(&mut ::std::io::stderr(), $($arg)*) {
            Ok(_)  => (),
            Err(e) => panic!("Unable to write to stderr: {}", e),
        }
    }
}

#[cfg(test)]
mod test {
    use std::ptr;
    use std::slice;

    #[test]
    fn test_get_dist_extra_bits() {
        assert_eq!(super::get_dist_extra_bits(-1), 0);
        assert_eq!(super::get_dist_extra_bits(0), 0);
        assert_eq!(super::get_dist_extra_bits(1), 0);
        assert_eq!(super::get_dist_extra_bits(4), 0);
        assert_eq!(super::get_dist_extra_bits(5), 1);
        assert_eq!(super::get_dist_extra_bits(256), 6);
        assert_eq!(super::get_dist_extra_bits(257), 7);
        assert_eq!(super::get_dist_extra_bits(16384), 12);
        assert_eq!(super::get_dist_extra_bits(16385), 13);
        assert_eq!(super::get_dist_extra_bits(32767), 13);
    }

    #[test]
    fn test_get_dist_extra_bits_value() {
        assert_eq!(super::get_dist_extra_bits_value(-1), 0);
        assert_eq!(super::get_dist_extra_bits_value(0), 0);
        assert_eq!(super::get_dist_extra_bits_value(1), 0);
        assert_eq!(super::get_dist_extra_bits_value(4), 0);
        assert_eq!(super::get_dist_extra_bits_value(5), (5 - 5) & 1);
        assert_eq!(super::get_dist_extra_bits_value(8), (8 - 5) & 1);
        assert_eq!(super::get_dist_extra_bits_value(9), (9 - 9) & 3);
        assert_eq!(super::get_dist_extra_bits_value(16), (16 - 9) & 3);
        assert_eq!(super::get_dist_extra_bits_value(256), (256 - 129) & 63);
        assert_eq!(super::get_dist_extra_bits_value(300), (300 - 257) & 127);
        assert_eq!(super::get_dist_extra_bits_value(16384), (16384 - 8193) & 4095);
        assert_eq!(super::get_dist_extra_bits_value(16385), (16385 - 16385) & 8191);
        assert_eq!(super::get_dist_extra_bits_value(20000), (20000 - 16385) & 8191);
        assert_eq!(super::get_dist_extra_bits_value(32767), (32767 - 16385) & 8191);
    }

    #[test]
    fn test_get_dist_symbol() {
        assert_eq!(super::get_dist_symbol(-1), -1 - 1);
        assert_eq!(super::get_dist_symbol(0), 0 - 1);
        assert_eq!(super::get_dist_symbol(4), 4 - 1);
        assert_eq!(super::get_dist_symbol(5), 4);
        assert_eq!(super::get_dist_symbol(6), 4);
        assert_eq!(super::get_dist_symbol(7), 5);
        assert_eq!(super::get_dist_symbol(8), 5);
        assert_eq!(super::get_dist_symbol(9), 6);
        assert_eq!(super::get_dist_symbol(12), 6);
        assert_eq!(super::get_dist_symbol(13), 7);
        assert_eq!(super::get_dist_symbol(16), 7);
        assert_eq!(super::get_dist_symbol(17), 8);
        assert_eq!(super::get_dist_symbol(24), 8);
        assert_eq!(super::get_dist_symbol(25), 9);
        assert_eq!(super::get_dist_symbol(32), 9);
        assert_eq!(super::get_dist_symbol(96), 12);
        assert_eq!(super::get_dist_symbol(97), 13);
        assert_eq!(super::get_dist_symbol(768), 18);
        assert_eq!(super::get_dist_symbol(769), 19);
        assert_eq!(super::get_dist_symbol(2048), 21);
        assert_eq!(super::get_dist_symbol(2049), 22);
        assert_eq!(super::get_dist_symbol(12288), 26);
        assert_eq!(super::get_dist_symbol(12289), 27);
        assert_eq!(super::get_dist_symbol(20000), 28);
        assert_eq!(super::get_dist_symbol(24576), 28);
        assert_eq!(super::get_dist_symbol(24577), 29);
        assert_eq!(super::get_dist_symbol(32767), 29);
    }

    #[test]
    fn test_append_data() {
        unsafe {
            let mut data: *mut i32 = ptr::null_mut();
            let mut size = 0;
            append_data!(1i32, data, size);
            append_data!(2i32, data, size);
            append_data!(3i32, data, size);
            append_data!(4i32, data, size);
            append_data!(5i32, data, size);
            assert_eq!(slice::from_raw_parts(data, size), [1, 2, 3, 4, 5]);
        }
    }
}
