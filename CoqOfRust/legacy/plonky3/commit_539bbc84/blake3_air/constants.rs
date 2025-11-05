pub const BITS_PER_LIMB: usize = 16;
pub const U32_LIMBS: usize = 32 / BITS_PER_LIMB;

// The constants from the reference implementation.
// Saved as pairs of 16 bit integers in [lo, hi] format.
pub(crate) const IV: [[u32; 2]; 8] = [
    [0xE667, 0x6A09],
    [0xAE85, 0xBB67],
    [0xF372, 0x3C6E],
    [0xF53A, 0xA54F],
    [0x527F, 0x510E],
    [0x688C, 0x9B05],
    [0xD9AB, 0x1F83],
    [0xCD19, 0x5BE0],
];

// The index map for the permutation used to permute the block words is:
// `[2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8]`
//
// This permutation decomposes into 2 cycles of length 8:
// `0 -> 2 -> 3 -> 10 -> 12 -> 9 -> 11 -> 5 -> 0`
// `1 -> 6 -> 4 -> 7 -> 13 -> 14 -> 15 -> 8 -> 1`
//
// There might be a way to use this decomposition to slightly speed permute up.

/// The index map for the permutation used to permute the block words.
const MSG_PERMUTATION: [usize; 16] = [2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8];

/// Apply the MSG_PERMUTATION to an array.
pub(crate) fn permute<T: Clone>(m: &mut [T; 16]) {
    let mut permuted = m.clone();
    for i in 0..16 {
        permuted[i] = m[MSG_PERMUTATION[i]].clone();
    }
    *m = permuted;
}
