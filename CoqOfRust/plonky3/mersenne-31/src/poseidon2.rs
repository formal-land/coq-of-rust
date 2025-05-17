//! Implementation of Poseidon2, see: `<https://eprint.iacr.org/2023/323>`
//!
//! For the diffusion matrix, 1 + Diag(V), we perform a search to find an optimized
//! vector V composed of elements with efficient multiplication algorithms in AVX2/AVX512/NEON.
//!
//! This leads to using small values (e.g. 1, 2) where multiplication is implemented using addition
//! and powers of 2 where multiplication is implemented using shifts.
//! Additionally, for technical reasons, having the first entry be -2 is useful.
//!
//! Optimized Diagonal for Mersenne31 width 16:
//! [-2, 2^0, 2, 4, 8, 16, 32, 64, 2^7, 2^8, 2^10, 2^12, 2^13, 2^14, 2^15, 2^16]
//! Optimized Diagonal for Mersenne31 width 24:
//! [-2, 2^0, 2, 4, 8, 16, 32, 64, 2^7, 2^8, 2^9, 2^10, 2^11, 2^12, 2^13, 2^14, 2^15, 2^16, 2^17, 2^18, 2^19, 2^20, 2^21, 2^22]
//! See poseidon2\src\diffusion.rs for information on how to double check these matrices in Sage.

use p3_field::Algebra;
use p3_poseidon2::{
    ExternalLayer, GenericPoseidon2LinearLayers, InternalLayer, MDSMat4, Poseidon2,
    add_rc_and_sbox_generic, external_initial_permute_state, external_terminal_permute_state,
    internal_permute_state,
};

use crate::{
    Mersenne31, Poseidon2ExternalLayerMersenne31, Poseidon2InternalLayerMersenne31, from_u62,
};

/// Degree of the chosen permutation polynomial for Mersenne31, used as the Poseidon2 S-Box.
///
/// As p - 1 = 2×3^2×7×11×... the smallest choice for a degree D satisfying gcd(p - 1, D) = 1 is 5.
/// Currently pub(crate) as it is used in the default neon implementation. Once that is optimized
/// this should no longer be public.
pub(crate) const MERSENNE31_S_BOX_DEGREE: u64 = 5;

/// An implementation of the Poseidon2 hash function specialised to run on the current architecture.
///
/// It acts on arrays of the form either `[Mersenne31::Packing; WIDTH]` or `[Mersenne31; WIDTH]`. For speed purposes,
/// wherever possible, input arrays should of the form `[Mersenne31::Packing; WIDTH]`.
pub type Poseidon2Mersenne31<const WIDTH: usize> = Poseidon2<
    Mersenne31,
    Poseidon2ExternalLayerMersenne31<WIDTH>,
    Poseidon2InternalLayerMersenne31,
    WIDTH,
    MERSENNE31_S_BOX_DEGREE,
>;

/// An implementation of the matrix multiplications in the internal and external layers of Poseidon2.
///
/// This can act on `[A; WIDTH]` for any ring implementing `Algebra<Mersenne31>`.
/// If you have either `[Mersenne31::Packing; WIDTH]` or `[Mersenne31; WIDTH]` it will be much faster
/// to use `Poseidon2Mersenne31<WIDTH>` instead of building a Poseidon2 permutation using this.
pub struct GenericPoseidon2LinearLayersMersenne31 {}

const POSEIDON2_INTERNAL_MATRIX_DIAG_16_SHIFTS: [u8; 15] =
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 13, 14, 15, 16];

const POSEIDON2_INTERNAL_MATRIX_DIAG_24_SHIFTS: [u8; 23] = [
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22,
];

/// Multiply state by the matrix (1 + Diag(V))
///
/// Here V is the vector [-2] + 1 << shifts. This used delayed reduction to be slightly faster.
fn permute_mut<const N: usize>(state: &mut [Mersenne31; N], shifts: &[u8]) {
    debug_assert_eq!(shifts.len() + 1, N);
    let part_sum: u64 = state[1..].iter().map(|x| x.value as u64).sum();
    let full_sum = part_sum + (state[0].value as u64);
    let s0 = part_sum + (-state[0]).value as u64;
    state[0] = from_u62(s0);
    for i in 1..N {
        let si = full_sum + ((state[i].value as u64) << shifts[i - 1]);
        state[i] = from_u62(si);
    }
}

impl InternalLayer<Mersenne31, 16, MERSENNE31_S_BOX_DEGREE> for Poseidon2InternalLayerMersenne31 {
    /// Perform the internal layers of the Poseidon2 permutation on the given state.
    fn permute_state(&self, state: &mut [Mersenne31; 16]) {
        internal_permute_state(
            state,
            |x| permute_mut(x, &POSEIDON2_INTERNAL_MATRIX_DIAG_16_SHIFTS),
            &self.internal_constants,
        )
    }
}

impl InternalLayer<Mersenne31, 24, MERSENNE31_S_BOX_DEGREE> for Poseidon2InternalLayerMersenne31 {
    /// Perform the internal layers of the Poseidon2 permutation on the given state.
    fn permute_state(&self, state: &mut [Mersenne31; 24]) {
        internal_permute_state(
            state,
            |x| permute_mut(x, &POSEIDON2_INTERNAL_MATRIX_DIAG_24_SHIFTS),
            &self.internal_constants,
        )
    }
}

impl<const WIDTH: usize> ExternalLayer<Mersenne31, WIDTH, MERSENNE31_S_BOX_DEGREE>
    for Poseidon2ExternalLayerMersenne31<WIDTH>
{
    /// Perform the initial external layers of the Poseidon2 permutation on the given state.
    fn permute_state_initial(&self, state: &mut [Mersenne31; WIDTH]) {
        external_initial_permute_state(
            state,
            self.external_constants.get_initial_constants(),
            add_rc_and_sbox_generic,
            &MDSMat4,
        );
    }

    /// Perform the terminal external layers of the Poseidon2 permutation on the given state.
    fn permute_state_terminal(&self, state: &mut [Mersenne31; WIDTH]) {
        external_terminal_permute_state(
            state,
            self.external_constants.get_terminal_constants(),
            add_rc_and_sbox_generic,
            &MDSMat4,
        );
    }
}

impl<A: Algebra<Mersenne31>> GenericPoseidon2LinearLayers<A, 16>
    for GenericPoseidon2LinearLayersMersenne31
{
    fn internal_linear_layer(state: &mut [A; 16]) {
        let part_sum: A = state[1..].iter().cloned().sum();
        let full_sum = part_sum.clone() + state[0].clone();

        // The first three diagonal elements are -2, 1, 2 so we do something custom.
        state[0] = part_sum - state[0].clone();
        state[1] = full_sum.clone() + state[1].clone();
        state[2] = full_sum.clone() + state[2].double();

        // For the remaining elements we use the mul_2exp_u64 method.
        // We need state[1..] as POSEIDON2_INTERNAL_MATRIX_DIAG_16_SHIFTS
        // doesn't include the shift for the 0'th element as it is -2.
        state[1..]
            .iter_mut()
            .zip(POSEIDON2_INTERNAL_MATRIX_DIAG_16_SHIFTS)
            .skip(2)
            .for_each(|(val, diag_shift)| {
                *val = full_sum.clone() + val.clone().mul_2exp_u64(diag_shift as u64);
            });
    }
}

impl<A: Algebra<Mersenne31>> GenericPoseidon2LinearLayers<A, 24>
    for GenericPoseidon2LinearLayersMersenne31
{
    fn internal_linear_layer(state: &mut [A; 24]) {
        let part_sum: A = state[1..].iter().cloned().sum();
        let full_sum = part_sum.clone() + state[0].clone();

        // The first three diagonal elements are -2, 1, 2 so we do something custom.
        state[0] = part_sum - state[0].clone();
        state[1] = full_sum.clone() + state[1].clone();
        state[2] = full_sum.clone() + state[2].double();

        // For the remaining elements we use the mul_2exp_u64 method.
        // We need state[1..] as POSEIDON2_INTERNAL_MATRIX_DIAG_24_SHIFTS
        // doesn't include the shift for the 0'th element as it is -2.
        state[1..]
            .iter_mut()
            .zip(POSEIDON2_INTERNAL_MATRIX_DIAG_24_SHIFTS)
            .skip(2)
            .for_each(|(val, diag_shift)| {
                *val = full_sum.clone() + val.clone().mul_2exp_u64(diag_shift as u64);
            });
    }
}

#[cfg(test)]
mod tests {
    use p3_symmetric::Permutation;
    use rand::SeedableRng;
    use rand_xoshiro::Xoroshiro128Plus;

    use super::*;

    type F = Mersenne31;

    // We need to make some round constants. We use Xoroshiro128Plus for this as we can easily match this PRNG in sage.
    // See: https://github.com/0xPolygonZero/hash-constants for the sage code used to create all these tests.

    /// Test on a roughly random input.
    /// This random input is generated by the following sage code:
    /// set_random_seed(16)
    /// vector([M31.random_element() for t in range(16)]).
    #[test]
    fn test_poseidon2_width_16_random() {
        let mut input: [F; 16] = Mersenne31::new_array([
            894848333, 1437655012, 1200606629, 1690012884, 71131202, 1749206695, 1717947831,
            120589055, 19776022, 42382981, 1831865506, 724844064, 171220207, 1299207443, 227047920,
            1783754913,
        ]);

        let expected: [F; 16] = Mersenne31::new_array([
            1124552602, 2127602268, 1834113265, 1207687593, 1891161485, 245915620, 981277919,
            627265710, 1534924153, 1580826924, 887997842, 1526280482, 547791593, 1028672510,
            1803086471, 323071277,
        ]);

        let mut rng = Xoroshiro128Plus::seed_from_u64(1);
        let perm = Poseidon2Mersenne31::new_from_rng_128(&mut rng);

        perm.permute_mut(&mut input);
        assert_eq!(input, expected);
    }

    /// Test on a roughly random input.
    /// This random input is generated by the following sage code:
    /// set_random_seed(24)
    /// vector([M31.random_element() for t in range(24)]).
    #[test]
    fn test_poseidon2_width_24_random() {
        let mut input: [F; 24] = Mersenne31::new_array([
            886409618, 1327899896, 1902407911, 591953491, 648428576, 1844789031, 1198336108,
            355597330, 1799586834, 59617783, 790334801, 1968791836, 559272107, 31054313,
            1042221543, 474748436, 135686258, 263665994, 1962340735, 1741539604, 2026927696,
            449439011, 1131357108, 50869465,
        ]);

        let expected: [F; 24] = Mersenne31::new_array([
            87189408, 212775836, 954807335, 1424761838, 1222521810, 1264950009, 1891204592,
            710452896, 957091834, 1776630156, 1091081383, 786687731, 1101902149, 1281649821,
            436070674, 313565599, 1961711763, 2002894460, 2040173120, 854107426, 25198245,
            1967213543, 604802266, 2086190331,
        ]);

        let mut rng = Xoroshiro128Plus::seed_from_u64(1);
        let perm = Poseidon2Mersenne31::new_from_rng_128(&mut rng);

        perm.permute_mut(&mut input);
        assert_eq!(input, expected);
    }
}
