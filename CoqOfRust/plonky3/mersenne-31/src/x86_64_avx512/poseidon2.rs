use alloc::vec::Vec;
use core::arch::x86_64::{self, __m512i};

use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_poseidon2::{
    ExternalLayer, ExternalLayerConstants, ExternalLayerConstructor, InternalLayer,
    InternalLayerConstructor, MDSMat4, mds_light_permutation,
};

use crate::{Mersenne31, P, PackedMersenne31AVX512, exp5};

/// The internal layers of the Poseidon2 permutation for Mersenne31.
///
/// The packed constants are stored in negative form as this allows some optimizations.
/// This means given a constant `x`, we treat it as an `i32` and
/// pack 16 copies of `x - P` into the corresponding `__m512i` packed constant.
#[derive(Debug, Clone)]
pub struct Poseidon2InternalLayerMersenne31 {
    pub(crate) internal_constants: Vec<Mersenne31>,
    packed_internal_constants: Vec<__m512i>,
}

impl InternalLayerConstructor<Mersenne31> for Poseidon2InternalLayerMersenne31 {
    /// We save the round constants in the {-P, ..., 0} representation instead of the standard
    /// {0, ..., P} one. This saves several instructions later.
    fn new_from_constants(internal_constants: Vec<Mersenne31>) -> Self {
        Self::new_from_constants(internal_constants)
    }
}

/// The external layers of the Poseidon2 permutation for Mersenne31.
///
/// The packed constants are stored in negative form as this allows some optimizations.
/// This means given a constant `x`, we treat it as an `i32` and
/// pack 16 copies of `x - P` into the corresponding `__m512i` packed constant.
#[derive(Clone)]
pub struct Poseidon2ExternalLayerMersenne31<const WIDTH: usize> {
    pub(crate) external_constants: ExternalLayerConstants<Mersenne31, WIDTH>,
    packed_initial_external_constants: Vec<[__m512i; WIDTH]>,
    packed_terminal_external_constants: Vec<[__m512i; WIDTH]>,
}

impl<const WIDTH: usize> ExternalLayerConstructor<Mersenne31, WIDTH>
    for Poseidon2ExternalLayerMersenne31<WIDTH>
{
    fn new_from_constants(external_constants: ExternalLayerConstants<Mersenne31, WIDTH>) -> Self {
        Self::new_from_constants(external_constants)
    }
}

/// Convert elements from the standard form {0, ..., P} to {-P, ..., 0} and copy into a vector
fn convert_to_vec_neg_form(input: i32) -> __m512i {
    let input_sub_p = input - (Mersenne31::ORDER_U32 as i32);
    unsafe {
        // Safety: If this code got compiled then AVX512-F intrinsics are available.
        x86_64::_mm512_set1_epi32(input_sub_p)
    }
}

impl Poseidon2InternalLayerMersenne31 {
    /// Construct an instance of Poseidon2InternalLayerMersenne31 from a vector containing
    /// the constants for each round. Internally, the constants are transformed into the
    /// {-P, ..., 0} representation instead of the standard {0, ..., P} one.
    fn new_from_constants(internal_constants: Vec<Mersenne31>) -> Self {
        let packed_internal_constants = internal_constants
            .iter()
            .map(|constant| convert_to_vec_neg_form(constant.value as i32))
            .collect();
        Self {
            internal_constants,
            packed_internal_constants,
        }
    }
}

impl<const WIDTH: usize> Poseidon2ExternalLayerMersenne31<WIDTH> {
    /// Construct an instance of Poseidon2ExternalLayerMersenne31 from an array of
    /// vectors containing the constants for each round. Internally, the constants
    ///  are transformed into the {-P, ..., 0} representation instead of the standard {0, ..., P} one.
    fn new_from_constants(external_constants: ExternalLayerConstants<Mersenne31, WIDTH>) -> Self {
        let packed_initial_external_constants = external_constants
            .get_initial_constants()
            .iter()
            .map(|array| array.map(|constant| convert_to_vec_neg_form(constant.value as i32)))
            .collect();
        let packed_terminal_external_constants = external_constants
            .get_terminal_constants()
            .iter()
            .map(|array| array.map(|constant| convert_to_vec_neg_form(constant.value as i32)))
            .collect();
        Self {
            external_constants,
            packed_initial_external_constants,
            packed_terminal_external_constants,
        }
    }
}

/// Compute the map x -> 2^I x on Mersenne-31 field elements.
/// x must be represented as a value in {0..P}.
/// This requires 2 generic parameters, I and I_PRIME satisfying I + I_PRIME = 31.
/// If the inputs do not conform to this representations, the result is undefined.
#[inline(always)]
fn mul_2exp_i<const I: u32, const I_PRIME: u32>(
    val: PackedMersenne31AVX512,
) -> PackedMersenne31AVX512 {
    assert_eq!(I + I_PRIME, 31);
    unsafe {
        // Safety: If this code got compiled then AVX512-F intrinsics are available.
        let input = val.to_vector();

        // In M31, multiplication by 2^n corresponds to a cyclic rotation which
        // is much faster than the naive multiplication method.

        // Shift the low bits up. This also shifts something unwanted into
        // the sign bit so we mark it dirty.
        let hi_bits_dirty = x86_64::_mm512_slli_epi32::<I>(input);

        // Shift the high bits down.
        let lo_bits = x86_64::_mm512_srli_epi32::<I_PRIME>(input);

        // Clear the sign bit and combine the lo and high bits.
        // The simplest description of the operation we want is lo OR (hi_dirty AND P) which has bit pattern:
        // 111 => 1, 110 => 1, 101 => 1, 100 => 1, 011 => 1, 010 => 0, 001 => 0, 000 => 0
        // Note that the input patterns: 111, 110, 100 cannot occur so any constant of the form **1*1000 should work.
        let output = x86_64::_mm512_ternarylogic_epi32::<0b11111000>(lo_bits, hi_bits_dirty, P);
        PackedMersenne31AVX512::from_vector(output)
    }
}

/// We hard code multiplication by the diagonal minus 1 of our internal matrix (1 + Diag(V))
/// In the Mersenne31, WIDTH = 16 case, the diagonal minus 1 is:
/// [-2] + 1 << [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 13, 14, 15, 16]
/// i.e. The first entry is -2 and all other entries are powers of 2.
#[inline(always)]
fn diagonal_mul_16(state: &mut [PackedMersenne31AVX512; 16]) {
    // The first three entries involve multiplication by -2, 1, 2 which are simple:
    // state[0] -> -2*state[0] is handled by the calling code.

    // We could use mul_2exp_i here as it is also 3 instructions but add should have better throughput as its instructions work on more ports.
    state[2] = state[2] + state[2];

    // For the remaining entries we use our fast shift code.
    state[3] = mul_2exp_i::<2, 29>(state[3]);
    state[4] = mul_2exp_i::<3, 28>(state[4]);
    state[5] = mul_2exp_i::<4, 27>(state[5]);
    state[6] = mul_2exp_i::<5, 26>(state[6]);
    state[7] = mul_2exp_i::<6, 25>(state[7]);
    state[8] = mul_2exp_i::<7, 24>(state[8]);
    state[9] = mul_2exp_i::<8, 23>(state[9]);
    state[10] = mul_2exp_i::<10, 21>(state[10]);
    state[11] = mul_2exp_i::<12, 19>(state[11]);
    state[12] = mul_2exp_i::<13, 18>(state[12]);
    state[13] = mul_2exp_i::<14, 17>(state[13]);
    state[14] = mul_2exp_i::<15, 16>(state[14]);
    state[15] = mul_2exp_i::<16, 15>(state[15]);
}

/// We hard code multiplication by the diagonal minus 1 of our internal matrix (1 + Diag(V))
/// In the Mersenne31, WIDTH = 24 case, the diagonal minus 1 is:
/// [-2] + 1 << [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]
/// i.e. The first entry is -2 and all other entries a power of 2.
#[inline(always)]
fn diagonal_mul_24(state: &mut [PackedMersenne31AVX512; 24]) {
    // The first three entries involve multiplication by -2, 1, 2 which are simple:
    // state[0] -> -2*state[0] is handled by the calling code.

    // We could use mul_2exp_i here as it is also 3 instructions but add should have better throughput as its instructions work on more ports.
    state[2] = state[2] + state[2];

    // For the remaining entries we use our fast shift code.
    state[3] = mul_2exp_i::<2, 29>(state[3]);
    state[4] = mul_2exp_i::<3, 28>(state[4]);
    state[5] = mul_2exp_i::<4, 27>(state[5]);
    state[6] = mul_2exp_i::<5, 26>(state[6]);
    state[7] = mul_2exp_i::<6, 25>(state[7]);
    state[8] = mul_2exp_i::<7, 24>(state[8]);
    state[9] = mul_2exp_i::<8, 23>(state[9]);
    state[10] = mul_2exp_i::<9, 22>(state[10]);
    state[11] = mul_2exp_i::<10, 21>(state[11]);
    state[12] = mul_2exp_i::<11, 20>(state[12]);
    state[13] = mul_2exp_i::<12, 19>(state[13]);
    state[14] = mul_2exp_i::<13, 18>(state[14]);
    state[15] = mul_2exp_i::<14, 17>(state[15]);
    state[16] = mul_2exp_i::<15, 16>(state[16]);
    state[17] = mul_2exp_i::<16, 15>(state[17]);
    state[18] = mul_2exp_i::<17, 14>(state[18]);
    state[19] = mul_2exp_i::<18, 13>(state[19]);
    state[20] = mul_2exp_i::<19, 12>(state[20]);
    state[21] = mul_2exp_i::<20, 11>(state[21]);
    state[22] = mul_2exp_i::<21, 10>(state[22]);
    state[23] = mul_2exp_i::<22, 9>(state[23]);
}

/// Compute the map x -> (x + rc)^5 on Mersenne-31 field elements.
/// x must be represented as a value in {0..P}.
/// rc must be represented as a value in {-P, ..., 0}.
/// If the inputs do not conform to these representations, the result is undefined.
/// The output will be represented as a value in {0..P}.
#[inline(always)]
fn add_rc_and_sbox(input: PackedMersenne31AVX512, rc: __m512i) -> PackedMersenne31AVX512 {
    unsafe {
        // Safety: If this code got compiled then AVX512-F intrinsics are available.
        let input_vec = input.to_vector();
        let input_plus_rc = x86_64::_mm512_add_epi32(input_vec, rc);

        // Due to the representations of input and rc, input_plus_rc is in {-P, ..., P}.
        // This is exactly the required bound to apply sbox.
        let input_post_sbox = exp5(input_plus_rc);
        PackedMersenne31AVX512::from_vector(input_post_sbox)
    }
}

/// Compute a single Poseidon2 internal layer on a state of width 16.
#[inline(always)]
fn internal_16(state: &mut [PackedMersenne31AVX512; 16], rc: __m512i) {
    state[0] = add_rc_and_sbox(state[0], rc);
    let sum_tail = PackedMersenne31AVX512::sum_array::<15>(&state[1..]);
    let sum = sum_tail + state[0];
    state[0] = sum_tail - state[0];
    diagonal_mul_16(state);
    state[1..].iter_mut().for_each(|x| *x += sum);
}

impl InternalLayer<PackedMersenne31AVX512, 16, 5> for Poseidon2InternalLayerMersenne31 {
    /// Perform the internal layers of the Poseidon2 permutation on the given state.
    fn permute_state(&self, state: &mut [PackedMersenne31AVX512; 16]) {
        self.packed_internal_constants
            .iter()
            .for_each(|&rc| internal_16(state, rc))
    }
}

/// Compute a single Poseidon2 internal layer on a state of width 24.
#[inline(always)]
fn internal_24(state: &mut [PackedMersenne31AVX512; 24], rc: __m512i) {
    state[0] = add_rc_and_sbox(state[0], rc);
    let sum_tail = PackedMersenne31AVX512::sum_array::<23>(&state[1..]);
    let sum = sum_tail + state[0];
    state[0] = sum_tail - state[0];
    diagonal_mul_24(state);
    state[1..].iter_mut().for_each(|x| *x += sum);
}

impl InternalLayer<PackedMersenne31AVX512, 24, 5> for Poseidon2InternalLayerMersenne31 {
    /// Perform the internal layers of the Poseidon2 permutation on the given state.
    fn permute_state(&self, state: &mut [PackedMersenne31AVX512; 24]) {
        self.packed_internal_constants
            .iter()
            .for_each(|&rc| internal_24(state, rc))
    }
}

/// Compute a collection of Poseidon2 external layers.
/// One layer for every constant supplied.
#[inline]
fn external_rounds<const WIDTH: usize>(
    state: &mut [PackedMersenne31AVX512; WIDTH],
    packed_external_constants: &[[__m512i; WIDTH]],
) {
    packed_external_constants.iter().for_each(|round_consts| {
        state
            .iter_mut()
            .zip(round_consts.iter())
            .for_each(|(val, &rc)| *val = add_rc_and_sbox(*val, rc));
        mds_light_permutation(state, &MDSMat4);
    });
}

impl<const WIDTH: usize> ExternalLayer<PackedMersenne31AVX512, WIDTH, 5>
    for Poseidon2ExternalLayerMersenne31<WIDTH>
{
    /// Perform the initial external layers of the Poseidon2 permutation on the given state.
    fn permute_state_initial(&self, state: &mut [PackedMersenne31AVX512; WIDTH]) {
        mds_light_permutation(state, &MDSMat4);
        external_rounds(state, &self.packed_initial_external_constants);
    }

    /// Perform the terminal external layers of the Poseidon2 permutation on the given state.
    fn permute_state_terminal(&self, state: &mut [PackedMersenne31AVX512; WIDTH]) {
        external_rounds(state, &self.packed_terminal_external_constants);
    }
}

#[cfg(test)]
mod tests {
    use p3_symmetric::Permutation;
    use rand::rngs::SmallRng;
    use rand::{Rng, SeedableRng};

    use super::*;
    use crate::Poseidon2Mersenne31;

    type F = Mersenne31;
    type Perm16 = Poseidon2Mersenne31<16>;
    type Perm24 = Poseidon2Mersenne31<24>;

    /// Test that the output is the same as the scalar version on a random input of length 16.
    #[test]
    fn test_avx512_poseidon2_width_16() {
        let mut rng = SmallRng::seed_from_u64(1);

        // Our Poseidon2 implementation.
        let poseidon2 = Perm16::new_from_rng_128(&mut rng);

        let input: [F; 16] = rng.random();

        let mut expected = input;
        poseidon2.permute_mut(&mut expected);

        let mut avx512_input = input.map(Into::<PackedMersenne31AVX512>::into);
        poseidon2.permute_mut(&mut avx512_input);

        let avx512_output = avx512_input.map(|x| x.0[0]);

        assert_eq!(avx512_output, expected);
    }

    /// Test that the output is the same as the scalar version on a random input of length 24.
    #[test]
    fn test_avx512_poseidon2_width_24() {
        let mut rng = SmallRng::seed_from_u64(1);

        // Our Poseidon2 implementation.
        let poseidon2 = Perm24::new_from_rng_128(&mut rng);

        let input: [F; 24] = rng.random();

        let mut expected = input;
        poseidon2.permute_mut(&mut expected);

        let mut avx512_input = input.map(Into::<PackedMersenne31AVX512>::into);
        poseidon2.permute_mut(&mut avx512_input);

        let avx512_output = avx512_input.map(|x| x.0[0]);

        assert_eq!(avx512_output, expected);
    }
}
