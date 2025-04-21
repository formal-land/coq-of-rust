//! Implementation of Poseidon2, see: https://eprint.iacr.org/2023/323
//!
//! For the diffusion matrix, 1 + Diag(V), we perform a search to find an optimized
//! vector V composed of elements with efficient multiplication algorithms in AVX2/AVX512/NEON.
//!
//! This leads to using small values (e.g. 1, 2, 3, 4) where multiplication is implemented using addition
//! and inverse powers of 2 where it is possible to avoid monty reductions.
//! Additionally, for technical reasons, having the first entry be -2 is useful.
//!
//! Optimized Diagonal for KoalaBear16:
//! [-2, 1, 2, 1/2, 3, 4, -1/2, -3, -4, 1/2^8, 1/8, 1/2^24, -1/2^8, -1/8, -1/16, -1/2^24]
//! Optimized Diagonal for KoalaBear24:
//! [-2, 1, 2, 1/2, 3, 4, -1/2, -3, -4, 1/2^8, 1/4, 1/8, 1/16, 1/32, 1/64, 1/2^24, -1/2^8, -1/8, -1/16, -1/32, -1/64, -1/2^7, -1/2^9, -1/2^24]
//! See poseidon2\src\diffusion.rs for information on how to double check these matrices in Sage.

use p3_field::{Algebra, Field, PrimeCharacteristicRing, PrimeField32};
use p3_monty_31::{
    GenericPoseidon2LinearLayersMonty31, InternalLayerBaseParameters, InternalLayerParameters,
    MontyField31, Poseidon2ExternalLayerMonty31, Poseidon2InternalLayerMonty31,
};
use p3_poseidon2::Poseidon2;

use crate::{KoalaBear, KoalaBearParameters};

pub type Poseidon2InternalLayerKoalaBear<const WIDTH: usize> =
    Poseidon2InternalLayerMonty31<KoalaBearParameters, WIDTH, KoalaBearInternalLayerParameters>;

pub type Poseidon2ExternalLayerKoalaBear<const WIDTH: usize> =
    Poseidon2ExternalLayerMonty31<KoalaBearParameters, WIDTH>;

/// Degree of the chosen permutation polynomial for KoalaBear, used as the Poseidon2 S-Box.
///
/// As p - 1 = 127 * 2^{24} we have a lot of choice in degree D satisfying gcd(p - 1, D) = 1.
/// Experimentation suggests that the optimal choice is the smallest available one, namely 3.
const KOALABEAR_S_BOX_DEGREE: u64 = 3;

/// An implementation of the Poseidon2 hash function specialised to run on the current architecture.
///
/// It acts on arrays of the form either `[KoalaBear::Packing; WIDTH]` or `[KoalaBear; WIDTH]`. For speed purposes,
/// wherever possible, input arrays should of the form `[KoalaBear::Packing; WIDTH]`.
pub type Poseidon2KoalaBear<const WIDTH: usize> = Poseidon2<
    KoalaBear,
    Poseidon2ExternalLayerKoalaBear<WIDTH>,
    Poseidon2InternalLayerKoalaBear<WIDTH>,
    WIDTH,
    KOALABEAR_S_BOX_DEGREE,
>;

/// An implementation of the matrix multiplications in the internal and external layers of Poseidon2.
///
/// This can act on `[A; WIDTH]` for any ring implementing `Algebra<BabyBear>`.
/// If you have either `[KoalaBear::Packing; WIDTH]` or `[KoalaBear; WIDTH]` it will be much faster
/// to use `Poseidon2KoalaBear<WIDTH>` instead of building a Poseidon2 permutation using this.
pub type GenericPoseidon2LinearLayersKoalaBear =
    GenericPoseidon2LinearLayersMonty31<KoalaBearParameters, KoalaBearInternalLayerParameters>;

// In order to use KoalaBear::new_array we need to convert our vector to a vector of u32's.
// To do this we make use of the fact that KoalaBear::ORDER_U32 - 1 = 127 * 2^24 so for 0 <= n <= 24:
// -1/2^n = (KoalaBear::ORDER_U32 - 1) >> n
// 1/2^n = -(-1/2^n) = KoalaBear::ORDER_U32 - ((KoalaBear::ORDER_U32 - 1) >> n)

/// The vector [-2, 1, 2, 1/2, 3, 4, -1/2, -3, -4, 1/2^8, 1/8, 1/2^24, -1/2^8, -1/8, -1/16, -1/2^24]
/// saved as an array of KoalaBear elements.
const INTERNAL_DIAG_MONTY_16: [KoalaBear; 16] = KoalaBear::new_array([
    KoalaBear::ORDER_U32 - 2,
    1,
    2,
    (KoalaBear::ORDER_U32 + 1) >> 1,
    3,
    4,
    (KoalaBear::ORDER_U32 - 1) >> 1,
    KoalaBear::ORDER_U32 - 3,
    KoalaBear::ORDER_U32 - 4,
    KoalaBear::ORDER_U32 - ((KoalaBear::ORDER_U32 - 1) >> 8),
    KoalaBear::ORDER_U32 - ((KoalaBear::ORDER_U32 - 1) >> 3),
    KoalaBear::ORDER_U32 - 127,
    (KoalaBear::ORDER_U32 - 1) >> 8,
    (KoalaBear::ORDER_U32 - 1) >> 3,
    (KoalaBear::ORDER_U32 - 1) >> 4,
    127,
]);

/// The vector [-2, 1, 2, 1/2, 3, 4, -1/2, -3, -4, 1/2^8, 1/4, 1/8, 1/16, 1/32, 1/64, 1/2^24, -1/2^8, -1/8, -1/16, -1/32, -1/64, -1/2^7, -1/2^9, -1/2^24]
/// saved as an array of KoalaBear elements.
const INTERNAL_DIAG_MONTY_24: [KoalaBear; 24] = KoalaBear::new_array([
    KoalaBear::ORDER_U32 - 2,
    1,
    2,
    (KoalaBear::ORDER_U32 + 1) >> 1,
    3,
    4,
    (KoalaBear::ORDER_U32 - 1) >> 1,
    KoalaBear::ORDER_U32 - 3,
    KoalaBear::ORDER_U32 - 4,
    KoalaBear::ORDER_U32 - ((KoalaBear::ORDER_U32 - 1) >> 8),
    KoalaBear::ORDER_U32 - ((KoalaBear::ORDER_U32 - 1) >> 2),
    KoalaBear::ORDER_U32 - ((KoalaBear::ORDER_U32 - 1) >> 3),
    KoalaBear::ORDER_U32 - ((KoalaBear::ORDER_U32 - 1) >> 4),
    KoalaBear::ORDER_U32 - ((KoalaBear::ORDER_U32 - 1) >> 5),
    KoalaBear::ORDER_U32 - ((KoalaBear::ORDER_U32 - 1) >> 6),
    KoalaBear::ORDER_U32 - 127,
    (KoalaBear::ORDER_U32 - 1) >> 8,
    (KoalaBear::ORDER_U32 - 1) >> 3,
    (KoalaBear::ORDER_U32 - 1) >> 4,
    (KoalaBear::ORDER_U32 - 1) >> 5,
    (KoalaBear::ORDER_U32 - 1) >> 6,
    (KoalaBear::ORDER_U32 - 1) >> 7,
    (KoalaBear::ORDER_U32 - 1) >> 9,
    127,
]);

/// Contains data needed to define the internal layers of the Poseidon2 permutation.
#[derive(Debug, Clone, Default)]
pub struct KoalaBearInternalLayerParameters;

impl InternalLayerBaseParameters<KoalaBearParameters, 16> for KoalaBearInternalLayerParameters {
    type ArrayLike = [MontyField31<KoalaBearParameters>; 15];

    const INTERNAL_DIAG_MONTY: [MontyField31<KoalaBearParameters>; 16] = INTERNAL_DIAG_MONTY_16;

    /// Perform the internal matrix multiplication: s -> (1 + Diag(V))s.
    /// We ignore `state[0]` as it is handled separately.
    fn internal_layer_mat_mul(
        state: &mut [MontyField31<KoalaBearParameters>; 16],
        sum: MontyField31<KoalaBearParameters>,
    ) {
        // The diagonal matrix is defined by the vector:
        // V = [-2, 1, 2, 1/2, 3, 4, -1/2, -3, -4, 1/2^8, 1/8, 1/2^24, -1/2^8, -1/8, -1/16, -1/2^24]
        state[1] += sum;
        state[2] = state[2].double() + sum;
        state[3] = state[3].halve() + sum;
        state[4] = sum + state[4].double() + state[4];
        state[5] = sum + state[5].double().double();
        state[6] = sum - state[6].halve();
        state[7] = sum - (state[7].double() + state[7]);
        state[8] = sum - state[8].double().double();
        state[9] = state[9].div_2exp_u64(8);
        state[9] += sum;
        state[10] = state[10].div_2exp_u64(3);
        state[10] += sum;
        state[11] = state[11].div_2exp_u64(24);
        state[11] += sum;
        state[12] = state[12].div_2exp_u64(8);
        state[12] = sum - state[12];
        state[13] = state[13].div_2exp_u64(3);
        state[13] = sum - state[13];
        state[14] = state[14].div_2exp_u64(4);
        state[14] = sum - state[14];
        state[15] = state[15].div_2exp_u64(24);
        state[15] = sum - state[15];
    }

    fn generic_internal_linear_layer<A: Algebra<KoalaBear>>(state: &mut [A; 16]) {
        let part_sum: A = state[1..].iter().cloned().sum();
        let full_sum = part_sum.clone() + state[0].clone();

        // The first three diagonal elements are -2, 1, 2 so we do something custom.
        state[0] = part_sum - state[0].clone();
        state[1] = full_sum.clone() + state[1].clone();
        state[2] = full_sum.clone() + state[2].double();

        // For the remaining elements we use multiplication.
        // This could probably be improved slightly by making use of the
        // mul_2exp_u64 and div_2exp_u64 but this would involve porting div_2exp_u64 to PrimeCharacteristicRing.
        state
            .iter_mut()
            .zip(INTERNAL_DIAG_MONTY_16)
            .skip(3)
            .for_each(|(val, diag_elem)| {
                *val = full_sum.clone() + val.clone() * diag_elem;
            });
    }
}

impl InternalLayerBaseParameters<KoalaBearParameters, 24> for KoalaBearInternalLayerParameters {
    type ArrayLike = [MontyField31<KoalaBearParameters>; 23];

    const INTERNAL_DIAG_MONTY: [MontyField31<KoalaBearParameters>; 24] = INTERNAL_DIAG_MONTY_24;

    /// Perform the internal matrix multiplication: s -> (1 + Diag(V))s.
    /// We ignore `state[0]` as it is handled separately.
    fn internal_layer_mat_mul(
        state: &mut [MontyField31<KoalaBearParameters>; 24],
        sum: MontyField31<KoalaBearParameters>,
    ) {
        // The diagonal matrix is defined by the vector:
        // V = [-2, 1, 2, 1/2, 3, 4, -1/2, -3, -4, 1/2^8, 1/4, 1/8, 1/16, 1/32, 1/64, 1/2^24, -1/2^8, -1/8, -1/16, -1/32, -1/64, -1/2^7, -1/2^9, -1/2^24]
        state[1] += sum;
        state[2] = state[2].double() + sum;
        state[3] = state[3].halve() + sum;
        state[4] = sum + state[4].double() + state[4];
        state[5] = sum + state[5].double().double();
        state[6] = sum - state[6].halve();
        state[7] = sum - (state[7].double() + state[7]);
        state[8] = sum - state[8].double().double();
        state[9] = state[9].div_2exp_u64(8);
        state[9] += sum;
        state[10] = state[10].div_2exp_u64(2);
        state[10] += sum;
        state[11] = state[11].div_2exp_u64(3);
        state[11] += sum;
        state[12] = state[12].div_2exp_u64(4);
        state[12] += sum;
        state[13] = state[13].div_2exp_u64(5);
        state[13] += sum;
        state[14] = state[14].div_2exp_u64(6);
        state[14] += sum;
        state[15] = state[15].div_2exp_u64(24);
        state[15] += sum;
        state[16] = state[16].div_2exp_u64(8);
        state[16] = sum - state[16];
        state[17] = state[17].div_2exp_u64(3);
        state[17] = sum - state[17];
        state[18] = state[18].div_2exp_u64(4);
        state[18] = sum - state[18];
        state[19] = state[19].div_2exp_u64(5);
        state[19] = sum - state[19];
        state[20] = state[20].div_2exp_u64(6);
        state[20] = sum - state[20];
        state[21] = state[21].div_2exp_u64(7);
        state[21] = sum - state[21];
        state[22] = state[22].div_2exp_u64(9);
        state[22] = sum - state[22];
        state[23] = state[23].div_2exp_u64(24);
        state[23] = sum - state[23];
    }

    fn generic_internal_linear_layer<A: Algebra<KoalaBear>>(state: &mut [A; 24]) {
        let part_sum: A = state[1..].iter().cloned().sum();
        let full_sum = part_sum.clone() + state[0].clone();

        // The first three diagonal elements are -2, 1, 2 so we do something custom.
        state[0] = part_sum - state[0].clone();
        state[1] = full_sum.clone() + state[1].clone();
        state[2] = full_sum.clone() + state[2].double();

        // For the remaining elements we use multiplication.
        // This could probably be improved slightly by making use of the
        // mul_2exp_u64 and div_2exp_u64 but this would involve porting div_2exp_u64 to PrimeCharacteristicRing.
        state
            .iter_mut()
            .zip(INTERNAL_DIAG_MONTY_24)
            .skip(3)
            .for_each(|(val, diag_elem)| {
                *val = full_sum.clone() + val.clone() * diag_elem;
            });
    }
}

impl InternalLayerParameters<KoalaBearParameters, 16> for KoalaBearInternalLayerParameters {}
impl InternalLayerParameters<KoalaBearParameters, 24> for KoalaBearInternalLayerParameters {}

#[cfg(test)]
mod tests {
    use p3_symmetric::Permutation;
    use rand::{Rng, SeedableRng};
    use rand_xoshiro::Xoroshiro128Plus;

    use super::*;

    type F = KoalaBear;

    // We need to make some round constants. We use Xoroshiro128Plus for this as we can easily match this PRNG in sage.
    // See: https://github.com/0xPolygonZero/hash-constants for the sage code used to create all these tests.

    /// Test on a roughly random input.
    /// This random input is generated by the following sage code:
    /// set_random_seed(16)
    /// vector([KB.random_element() for t in range(16)]).
    #[test]
    fn test_poseidon2_width_16_random() {
        let mut input: [F; 16] = KoalaBear::new_array([
            894848333, 1437655012, 1200606629, 1690012884, 71131202, 1749206695, 1717947831,
            120589055, 19776022, 42382981, 1831865506, 724844064, 171220207, 1299207443, 227047920,
            1783754913,
        ]);

        let expected: [F; 16] = KoalaBear::new_array([
            652590279, 1200629963, 1013089423, 1840372851, 19101828, 561050015, 1714865585,
            994637181, 498949829, 729884572, 1957973925, 263012103, 535029297, 2121808603,
            964663675, 1473622080,
        ]);

        let mut rng = Xoroshiro128Plus::seed_from_u64(1);
        let perm = Poseidon2KoalaBear::new_from_rng_128(&mut rng);

        perm.permute_mut(&mut input);
        assert_eq!(input, expected);
    }

    /// Test on a roughly random input.
    /// This random input is generated by the following sage code:
    /// set_random_seed(24)
    /// vector([KB.random_element() for t in range(24)]).
    #[test]
    fn test_poseidon2_width_24_random() {
        let mut input: [F; 24] = KoalaBear::new_array([
            886409618, 1327899896, 1902407911, 591953491, 648428576, 1844789031, 1198336108,
            355597330, 1799586834, 59617783, 790334801, 1968791836, 559272107, 31054313,
            1042221543, 474748436, 135686258, 263665994, 1962340735, 1741539604, 2026927696,
            449439011, 1131357108, 50869465,
        ]);

        let expected: [F; 24] = KoalaBear::new_array([
            3825456, 486989921, 613714063, 282152282, 1027154688, 1171655681, 879344953,
            1090688809, 1960721991, 1604199242, 1329947150, 1535171244, 781646521, 1156559780,
            1875690339, 368140677, 457503063, 304208551, 1919757655, 835116474, 1293372648,
            1254825008, 810923913, 1773631109,
        ]);

        let mut rng = Xoroshiro128Plus::seed_from_u64(1);
        let perm = Poseidon2KoalaBear::new_from_rng_128(&mut rng);

        perm.permute_mut(&mut input);
        assert_eq!(input, expected);
    }

    /// Test the generic internal layer against the optimized internal layer
    /// for a random input of width 16.
    #[test]
    fn test_generic_internal_linear_layer_16() {
        let mut rng = Xoroshiro128Plus::seed_from_u64(1);
        let mut input1: [F; 16] = rng.random();
        let mut input2 = input1;

        let part_sum: F = input1[1..].iter().copied().sum();
        let full_sum = part_sum + input1[0];

        input1[0] = part_sum - input1[0];

        KoalaBearInternalLayerParameters::internal_layer_mat_mul(&mut input1, full_sum);
        KoalaBearInternalLayerParameters::generic_internal_linear_layer(&mut input2);

        assert_eq!(input1, input2);
    }

    /// Test the generic internal layer against the optimized internal layer
    /// for a random input of width 16.
    #[test]
    fn test_generic_internal_linear_layer_24() {
        let mut rng = Xoroshiro128Plus::seed_from_u64(1);
        let mut input1: [F; 24] = rng.random();
        let mut input2 = input1;

        let part_sum: F = input1[1..].iter().copied().sum();
        let full_sum = part_sum + input1[0];

        input1[0] = part_sum - input1[0];

        KoalaBearInternalLayerParameters::internal_layer_mat_mul(&mut input1, full_sum);
        KoalaBearInternalLayerParameters::generic_internal_linear_layer(&mut input2);

        assert_eq!(input1, input2);
    }
}
