
fn get_dist_extra_bits(dist: i32) -> i32 {
    if dist < 5 {
        0
    } else {
        ((31 ^ (dist - 1).leading_zeros()) - 1) as i32 // log2(dist - 1) - 1
    }
}

fn get_dist_extra_bits_value(dist: i32) -> i32 {
    if dist < 5 {
        0
    } else {
        let l = 31 ^ (dist - 1).leading_zeros(); // log2(dist - 1)
        (dist - (1 + (1 << l))) & ((1 << (l - 1)) - 1)
    }
}

fn get_dist_symbol(dist: i32) -> i32 {
    if dist < 5 {
        dist - 1
    } else {
        let l = 31 ^ (dist - 1).leading_zeros(); // log2(dist - 1)
        let r = ((dist - 1) >> (l - 1)) & 1;
        l as i32 * 2 + r
    }
}

fn get_length_extra_bits(l: i32) -> i32 {
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

fn get_length_extra_bits_value(l: i32) -> i32 {
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

/// Returns symbol in range [257-285] (inclusive).
fn get_length_symbol(l: i32) -> i32 {
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

#[cfg(test)]
mod test {
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
}
