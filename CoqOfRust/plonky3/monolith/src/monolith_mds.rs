//! Monolith-31's default MDS permutation.
//! With significant inspiration from https://extgit.iaik.tugraz.at/krypto/zkfriendlyhashzoo/

use p3_field::PrimeField32;
use p3_mds::MdsPermutation;
use p3_mds::util::apply_circulant;
use p3_mersenne_31::Mersenne31;
use p3_symmetric::Permutation;
use sha3::digest::{ExtendableOutput, Update};
use sha3::{Shake128, Shake128Reader};

use crate::util::get_random_u32;

#[derive(Clone, Debug)]
pub struct MonolithMdsMatrixMersenne31<const NUM_ROUNDS: usize>;

const MATRIX_CIRC_MDS_16_MERSENNE31_MONOLITH: [u64; 16] = [
    61402, 17845, 26798, 59689, 12021, 40901, 41351, 27521, 56951, 12034, 53865, 43244, 7454,
    33823, 28750, 1108,
];

impl<const WIDTH: usize, const NUM_ROUNDS: usize> Permutation<[Mersenne31; WIDTH]>
    for MonolithMdsMatrixMersenne31<NUM_ROUNDS>
{
    fn permute(&self, input: [Mersenne31; WIDTH]) -> [Mersenne31; WIDTH] {
        if WIDTH == 16 {
            let matrix: [u64; WIDTH] = MATRIX_CIRC_MDS_16_MERSENNE31_MONOLITH[..]
                .try_into()
                .unwrap();
            apply_circulant(&matrix, input)
        } else {
            let mut shake = Shake128::default();
            shake.update(b"Monolith");
            shake.update(&[WIDTH as u8, NUM_ROUNDS as u8]);
            shake.update(&Mersenne31::ORDER_U32.to_le_bytes());
            shake.update(&[16, 15]);
            shake.update(b"MDS");
            let mut shake_finalized = shake.finalize_xof();
            apply_cauchy_mds_matrix(&mut shake_finalized, input)
        }
    }

    fn permute_mut(&self, input: &mut [Mersenne31; WIDTH]) {
        *input = self.permute(*input);
    }
}

impl<const WIDTH: usize, const NUM_ROUNDS: usize> MdsPermutation<Mersenne31, WIDTH>
    for MonolithMdsMatrixMersenne31<NUM_ROUNDS>
{
}

fn apply_cauchy_mds_matrix<F: PrimeField32, const WIDTH: usize>(
    shake: &mut Shake128Reader,
    to_multiply: [F; WIDTH],
) -> [F; WIDTH] {
    let mut output: [F; WIDTH] = [F::ZERO; WIDTH];

    // As F is a PrimeField, it's order is equal to its characteristic.
    // Thus 2|F| > 2^bits > |F|.
    let bits = F::bits();
    let x_mask = (1 << (bits - 9)) - 1;
    let y_mask = ((1 << bits) - 1) >> 2;

    let y = get_random_y_i::<WIDTH>(shake, x_mask, y_mask);
    let mut x = y;
    x.iter_mut().for_each(|x_i| *x_i &= x_mask);

    for (i, x_i) in x.iter().enumerate() {
        for (j, y_j) in y.iter().enumerate() {
            let val = unsafe {
                // Safety:
                // x_i < x_mask < 2^{-8}|F|
                // y_j < y_mask < 2^{-1}|F|
                // Hence x_i + y_j < |F|.
                F::from_canonical_unchecked(x_i + y_j).inverse()
            };
            output[i] += val * to_multiply[j];
        }
    }

    output
}

fn get_random_y_i<const WIDTH: usize>(
    shake: &mut Shake128Reader,
    x_mask: u32,
    y_mask: u32,
) -> [u32; WIDTH] {
    let mut res = [0; WIDTH];

    for i in 0..WIDTH {
        let mut y_i = get_random_u32(shake) & y_mask;
        let mut x_i = y_i & x_mask;
        while res.iter().take(i).any(|r| r & x_mask == x_i) {
            y_i = get_random_u32(shake) & y_mask;
            x_i = y_i & x_mask;
        }
        res[i] = y_i;
    }

    res
}
