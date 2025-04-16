//! Implementation of Poseidon2, see: https://eprint.iacr.org/2023/323
//!
//! For the diffusion matrix, 1 + Diag(V), we perform a search to find an optimized
//! vector V composed of elements with efficient multiplication algorithms in AVX2/AVX512/NEON.
//!
//! This leads to using small values (e.g. 1, 2, 3, 4) where multiplication is implemented using addition
//! and inverse powers of 2 where it is possible to avoid monty reductions.
//! Additionally, for technical reasons, having the first entry be -2 is useful.
//!
//! Optimized Diagonal for BabyBear16:
//! [-2, 1, 2, 1/2, 3, 4, -1/2, -3, -4, 1/2^8, 1/4, 1/8, 1/2^27, -1/2^8, -1/16, -1/2^27].
//! Optimized Diagonal for BabyBear24:
//! [-2, 1, 2, 1/2, 3, 4, -1/2, -3, -4, 1/2^8, 1/4, 1/8, 1/16, 1/2^7, 1/2^9, 1/2^27, -1/2^8, -1/4, -1/8, -1/16, -1/32, -1/64, -1/2^7, -1/2^27]
//! See poseidon2\src\diffusion.rs for information on how to double check these matrices in Sage.

use p3_field::{Algebra, Field, PrimeCharacteristicRing, PrimeField32};
use p3_monty_31::{
    GenericPoseidon2LinearLayersMonty31, InternalLayerBaseParameters, InternalLayerParameters,
    MontyField31, Poseidon2ExternalLayerMonty31, Poseidon2InternalLayerMonty31,
};
use p3_poseidon2::{ExternalLayerConstants, Poseidon2};

use crate::{BabyBear, BabyBearParameters};

pub type Poseidon2InternalLayerBabyBear<const WIDTH: usize> =
    Poseidon2InternalLayerMonty31<BabyBearParameters, WIDTH, BabyBearInternalLayerParameters>;

pub type Poseidon2ExternalLayerBabyBear<const WIDTH: usize> =
    Poseidon2ExternalLayerMonty31<BabyBearParameters, WIDTH>;

/// Degree of the chosen permutation polynomial for BabyBear, used as the Poseidon2 S-Box.
///
/// As p - 1 = 15 * 2^{27} the neither 3 nor 5 satisfy gcd(p - 1, D) = 1.
/// Instead we use the next smallest available value, namely 7.
const BABYBEAR_S_BOX_DEGREE: u64 = 7;

/// An implementation of the Poseidon2 hash function specialised to run on the current architecture.
///
/// It acts on arrays of the form either `[BabyBear::Packing; WIDTH]` or `[BabyBear; WIDTH]`. For speed purposes,
/// wherever possible, input arrays should of the form `[BabyBear::Packing; WIDTH]`.
pub type Poseidon2BabyBear<const WIDTH: usize> = Poseidon2<
    BabyBear,
    Poseidon2ExternalLayerBabyBear<WIDTH>,
    Poseidon2InternalLayerBabyBear<WIDTH>,
    WIDTH,
    BABYBEAR_S_BOX_DEGREE,
>;

/// An implementation of the matrix multiplications in the internal and external layers of Poseidon2.
///
/// This can act on `[A; WIDTH]` for any ring implementing `Algebra<BabyBear>`.
/// If you have either `[BabyBear::Packing; WIDTH]` or `[BabyBear; WIDTH]` it will be much faster
/// to use `Poseidon2BabyBear<WIDTH>` instead of building a Poseidon2 permutation using this.
pub type GenericPoseidon2LinearLayersBabyBear =
    GenericPoseidon2LinearLayersMonty31<BabyBearParameters, BabyBearInternalLayerParameters>;

// In order to use BabyBear::new_array we need to convert our vector to a vector of u32's.
// To do this we make use of the fact that BabyBear::ORDER_U32 - 1 = 15 * 2^27 so for 0 <= n <= 27:
// -1/2^n = (BabyBear::ORDER_U32 - 1) >> n
// 1/2^n = -(-1/2^n) = BabyBear::ORDER_U32 - ((BabyBear::ORDER_U32 - 1) >> n)

/// The vector `[-2, 1, 2, 1/2, 3, 4, -1/2, -3, -4, 1/2^8, 1/4, 1/8, 1/2^27, -1/2^8, -1/16, -1/2^27]`
/// saved as an array of BabyBear elements.
const INTERNAL_DIAG_MONTY_16: [BabyBear; 16] = BabyBear::new_array([
    BabyBear::ORDER_U32 - 2,
    1,
    2,
    (BabyBear::ORDER_U32 + 1) >> 1,
    3,
    4,
    (BabyBear::ORDER_U32 - 1) >> 1,
    BabyBear::ORDER_U32 - 3,
    BabyBear::ORDER_U32 - 4,
    BabyBear::ORDER_U32 - ((BabyBear::ORDER_U32 - 1) >> 8),
    BabyBear::ORDER_U32 - ((BabyBear::ORDER_U32 - 1) >> 2),
    BabyBear::ORDER_U32 - ((BabyBear::ORDER_U32 - 1) >> 3),
    BabyBear::ORDER_U32 - 15,
    (BabyBear::ORDER_U32 - 1) >> 8,
    (BabyBear::ORDER_U32 - 1) >> 4,
    15,
]);

/// The vector [-2, 1, 2, 1/2, 3, 4, -1/2, -3, -4, 1/2^8, 1/4, 1/8, 1/16, 1/2^7, 1/2^9, 1/2^27, -1/2^8, -1/4, -1/8, -1/16, -1/32, -1/64, -1/2^7, -1/2^27]
/// saved as an array of BabyBear elements.
const INTERNAL_DIAG_MONTY_24: [BabyBear; 24] = BabyBear::new_array([
    BabyBear::ORDER_U32 - 2,
    1,
    2,
    (BabyBear::ORDER_U32 + 1) >> 1,
    3,
    4,
    (BabyBear::ORDER_U32 - 1) >> 1,
    BabyBear::ORDER_U32 - 3,
    BabyBear::ORDER_U32 - 4,
    BabyBear::ORDER_U32 - ((BabyBear::ORDER_U32 - 1) >> 8),
    BabyBear::ORDER_U32 - ((BabyBear::ORDER_U32 - 1) >> 2),
    BabyBear::ORDER_U32 - ((BabyBear::ORDER_U32 - 1) >> 3),
    BabyBear::ORDER_U32 - ((BabyBear::ORDER_U32 - 1) >> 4),
    BabyBear::ORDER_U32 - ((BabyBear::ORDER_U32 - 1) >> 7),
    BabyBear::ORDER_U32 - ((BabyBear::ORDER_U32 - 1) >> 9),
    BabyBear::ORDER_U32 - 15,
    (BabyBear::ORDER_U32 - 1) >> 8,
    (BabyBear::ORDER_U32 - 1) >> 2,
    (BabyBear::ORDER_U32 - 1) >> 3,
    (BabyBear::ORDER_U32 - 1) >> 4,
    (BabyBear::ORDER_U32 - 1) >> 5,
    (BabyBear::ORDER_U32 - 1) >> 6,
    (BabyBear::ORDER_U32 - 1) >> 7,
    15,
]);

/// Initial round constants for the 16-width Poseidon2 external layer on BabyBear.
///
/// See https://github.com/HorizenLabs/poseidon2/blob/main/plain_implementations/src/poseidon2/poseidon2_instance_babybear.rs
pub const BABYBEAR_RC16_EXTERNAL_INITIAL: [[BabyBear; 16]; 4] = BabyBear::new_2d_array([
    [
        0x69cbb6af, 0x46ad93f9, 0x60a00f4e, 0x6b1297cd, 0x23189afe, 0x732e7bef, 0x72c246de,
        0x2c941900, 0x0557eede, 0x1580496f, 0x3a3ea77b, 0x54f3f271, 0x0f49b029, 0x47872fe1,
        0x221e2e36, 0x1ab7202e,
    ],
    [
        0x487779a6, 0x3851c9d8, 0x38dc17c0, 0x209f8849, 0x268dcee8, 0x350c48da, 0x5b9ad32e,
        0x0523272b, 0x3f89055b, 0x01e894b2, 0x13ddedde, 0x1b2ef334, 0x7507d8b4, 0x6ceeb94e,
        0x52eb6ba2, 0x50642905,
    ],
    [
        0x05453f3f, 0x06349efc, 0x6922787c, 0x04bfff9c, 0x768c714a, 0x3e9ff21a, 0x15737c9c,
        0x2229c807, 0x0d47f88c, 0x097e0ecc, 0x27eadba0, 0x2d7d29e4, 0x3502aaa0, 0x0f475fd7,
        0x29fbda49, 0x018afffd,
    ],
    [
        0x0315b618, 0x6d4497d1, 0x1b171d9e, 0x52861abd, 0x2e5d0501, 0x3ec8646c, 0x6e5f250a,
        0x148ae8e6, 0x17f5fa4a, 0x3e66d284, 0x0051aa3b, 0x483f7913, 0x2cfe5f15, 0x023427ca,
        0x2cc78315, 0x1e36ea47,
    ],
]);

/// Final round constants for the 16-width Poseidon2's external layer on BabyBear.
///
/// See https://github.com/HorizenLabs/poseidon2/blob/main/plain_implementations/src/poseidon2/poseidon2_instance_babybear.rs
pub const BABYBEAR_RC16_EXTERNAL_FINAL: [[BabyBear; 16]; 4] = BabyBear::new_2d_array([
    [
        0x7290a80d, 0x6f7e5329, 0x598ec8a8, 0x76a859a0, 0x6559e868, 0x657b83af, 0x13271d3f,
        0x1f876063, 0x0aeeae37, 0x706e9ca6, 0x46400cee, 0x72a05c26, 0x2c589c9e, 0x20bd37a7,
        0x6a2d3d10, 0x20523767,
    ],
    [
        0x5b8fe9c4, 0x2aa501d6, 0x1e01ac3e, 0x1448bc54, 0x5ce5ad1c, 0x4918a14d, 0x2c46a83f,
        0x4fcf6876, 0x61d8d5c8, 0x6ddf4ff9, 0x11fda4d3, 0x02933a8f, 0x170eaf81, 0x5a9c314f,
        0x49a12590, 0x35ec52a1,
    ],
    [
        0x58eb1611, 0x5e481e65, 0x367125c9, 0x0eba33ba, 0x1fc28ded, 0x066399ad, 0x0cbec0ea,
        0x75fd1af0, 0x50f5bf4e, 0x643d5f41, 0x6f4fe718, 0x5b3cbbde, 0x1e3afb3e, 0x296fb027,
        0x45e1547b, 0x4a8db2ab,
    ],
    [
        0x59986d19, 0x30bcdfa3, 0x1db63932, 0x1d7c2824, 0x53b33681, 0x0673b747, 0x038a98a3,
        0x2c5bce60, 0x351979cd, 0x5008fb73, 0x547bca78, 0x711af481, 0x3f93bf64, 0x644d987b,
        0x3c8bcd87, 0x608758b8,
    ],
]);

/// Round constants for the 16-width Poseidon2's internal layer on BabyBear.
///
/// See https://github.com/HorizenLabs/poseidon2/blob/main/plain_implementations/src/poseidon2/poseidon2_instance_babybear.rs
pub const BABYBEAR_RC16_INTERNAL: [BabyBear; 13] = BabyBear::new_array([
    0x5a8053c0, 0x693be639, 0x3858867d, 0x19334f6b, 0x128f0fd8, 0x4e2b1ccb, 0x61210ce0, 0x3c318939,
    0x0b5b2f22, 0x2edb11d5, 0x213effdf, 0x0cac4606, 0x241af16d,
]);

/// A default Poseidon2 for BabyBear using the round constants from the Horizon Labs implementation.
///
/// See https://github.com/HorizenLabs/poseidon2/blob/main/plain_implementations/src/poseidon2/poseidon2_instance_babybear.rs
pub fn default_babybear_poseidon2_16() -> Poseidon2BabyBear<16> {
    Poseidon2::new(
        ExternalLayerConstants::new(
            BABYBEAR_RC16_EXTERNAL_INITIAL.to_vec(),
            BABYBEAR_RC16_EXTERNAL_FINAL.to_vec(),
        ),
        BABYBEAR_RC16_INTERNAL.to_vec(),
    )
}

/// Initial round constants for the 24-width Poseidon2 external layer on BabyBear.
///
/// See https://github.com/HorizenLabs/poseidon2/blob/main/plain_implementations/src/poseidon2/poseidon2_instance_babybear.rs
pub const BABYBEAR_RC24_EXTERNAL_INITIAL: [[BabyBear; 24]; 4] = BabyBear::new_2d_array([
    [
        0x0fa20c37, 0x0795bb97, 0x12c60b9c, 0x0eabd88e, 0x096485ca, 0x07093527, 0x1b1d4e50,
        0x30a01ace, 0x3bd86f5a, 0x69af7c28, 0x3f94775f, 0x731560e8, 0x465a0ecd, 0x574ef807,
        0x62fd4870, 0x52ccfe44, 0x14772b14, 0x4dedf371, 0x260acd7c, 0x1f51dc58, 0x75125532,
        0x686a4d7b, 0x54bac179, 0x31947706,
    ],
    [
        0x29799d3b, 0x6e01ae90, 0x203a7a64, 0x4f7e25be, 0x72503f77, 0x45bd3b69, 0x769bd6b4,
        0x5a867f08, 0x4fdba082, 0x251c4318, 0x28f06201, 0x6788c43a, 0x4c6d6a99, 0x357784a8,
        0x2abaf051, 0x770f7de6, 0x1794b784, 0x4796c57a, 0x724b7a10, 0x449989a7, 0x64935cf1,
        0x59e14aac, 0x0e620bb8, 0x3af5a33b,
    ],
    [
        0x4465cc0e, 0x019df68f, 0x4af8d068, 0x08784f82, 0x0cefdeae, 0x6337a467, 0x32fa7a16,
        0x486f62d6, 0x386a7480, 0x20f17c4a, 0x54e50da8, 0x2012cf03, 0x5fe52950, 0x09afb6cd,
        0x2523044e, 0x5c54d0ef, 0x71c01f3c, 0x60b2c4fb, 0x4050b379, 0x5e6a70a5, 0x418543f5,
        0x71debe56, 0x1aad2994, 0x3368a483,
    ],
    [
        0x07a86f3a, 0x5ea43ff1, 0x2443780e, 0x4ce444f7, 0x146f9882, 0x3132b089, 0x197ea856,
        0x667030c3, 0x2317d5dc, 0x0c2c48a7, 0x56b2df66, 0x67bd81e9, 0x4fcdfb19, 0x4baaef32,
        0x0328d30a, 0x6235760d, 0x12432912, 0x0a49e258, 0x030e1b70, 0x48caeb03, 0x49e4d9e9,
        0x1051b5c6, 0x6a36dbbe, 0x4cff27a5,
    ],
]);

/// Final round constants for the 24-width Poseidon2's external layer on BabyBear.
///
/// See https://github.com/HorizenLabs/poseidon2/blob/main/plain_implementations/src/poseidon2/poseidon2_instance_babybear.rs
pub const BABYBEAR_RC24_EXTERNAL_FINAL: [[BabyBear; 24]; 4] = BabyBear::new_2d_array([
    [
        0x032959ad, 0x2b18af6a, 0x55d3dc8c, 0x43bd26c8, 0x0c41595f, 0x7048d2e2, 0x00db8983,
        0x2af563d7, 0x6e84758f, 0x611d64e1, 0x1f9977e2, 0x64163a0a, 0x5c5fc27b, 0x02e22561,
        0x3a2d75db, 0x1ba7b71a, 0x34343f64, 0x7406b35d, 0x19df8299, 0x6ff4480a, 0x514a81c8,
        0x57ab52ce, 0x6ad69f52, 0x3e0c0e0d,
    ],
    [
        0x48126114, 0x2a9d62cc, 0x17441f23, 0x485762bb, 0x2f218674, 0x06fdc64a, 0x0861b7f2,
        0x3b36eee6, 0x70a11040, 0x04b31737, 0x3722a872, 0x2a351c63, 0x623560dc, 0x62584ab2,
        0x382c7c04, 0x3bf9edc7, 0x0e38fe51, 0x376f3b10, 0x5381e178, 0x3afc61c7, 0x5c1bcb4d,
        0x6643ce1f, 0x2d0af1c1, 0x08f583cc,
    ],
    [
        0x5d6ff60f, 0x6324c1e5, 0x74412fb7, 0x70c0192e, 0x0b72f141, 0x4067a111, 0x57388c4f,
        0x351009ec, 0x0974c159, 0x539a58b3, 0x038c0cff, 0x476c0392, 0x3f7bc15f, 0x4491dd2c,
        0x4d1fef55, 0x04936ae3, 0x58214dd4, 0x683c6aad, 0x1b42f16b, 0x6dc79135, 0x2d4e71ec,
        0x3e2946ea, 0x59dce8db, 0x6cee892a,
    ],
    [
        0x47f07350, 0x7106ce93, 0x3bd4a7a9, 0x2bfe636a, 0x430011e9, 0x001cd66a, 0x307faf5b,
        0x0d9ef3fe, 0x6d40043a, 0x2e8f470c, 0x1b6865e8, 0x0c0e6c01, 0x4d41981f, 0x423b9d3d,
        0x410408cc, 0x263f0884, 0x5311bbd0, 0x4dae58d8, 0x30401cea, 0x09afa575, 0x4b3d5b42,
        0x63ac0b37, 0x5fe5bb14, 0x5244e9d4,
    ],
]);

/// Round constants for the 24-width Poseidon2's internal layer on BabyBear.
///
/// See https://github.com/HorizenLabs/poseidon2/blob/main/plain_implementations/src/poseidon2/poseidon2_instance_babybear.rs
pub const BABYBEAR_RC24_INTERNAL: [BabyBear; 21] = BabyBear::new_array([
    0x1da78ec2, 0x730b0924, 0x3eb56cf3, 0x5bd93073, 0x37204c97, 0x51642d89, 0x66e943e8, 0x1a3e72de,
    0x70beb1e9, 0x30ff3b3f, 0x4240d1c4, 0x12647b8d, 0x65d86965, 0x49ef4d7c, 0x47785697, 0x46b3969f,
    0x5c7b7a0e, 0x7078fc60, 0x4f22d482, 0x482a9aee, 0x6beb839d,
]);

/// A default Poseidon2 for BabyBear using the round constants from the Horizon Labs implementation.
///
/// See https://github.com/HorizenLabs/poseidon2/blob/main/plain_implementations/src/poseidon2/poseidon2_instance_babybear.rs
pub fn default_babybear_poseidon2_24() -> Poseidon2BabyBear<24> {
    Poseidon2::new(
        ExternalLayerConstants::new(
            BABYBEAR_RC24_EXTERNAL_INITIAL.to_vec(),
            BABYBEAR_RC24_EXTERNAL_FINAL.to_vec(),
        ),
        BABYBEAR_RC24_INTERNAL.to_vec(),
    )
}

/// Contains data needed to define the internal layers of the Poseidon2 permutation.
#[derive(Debug, Clone, Default)]
pub struct BabyBearInternalLayerParameters;

impl InternalLayerBaseParameters<BabyBearParameters, 16> for BabyBearInternalLayerParameters {
    type ArrayLike = [MontyField31<BabyBearParameters>; 15];

    const INTERNAL_DIAG_MONTY: [BabyBear; 16] = INTERNAL_DIAG_MONTY_16;

    /// Perform the internal matrix multiplication: s -> (1 + Diag(V))s.
    /// We ignore `state[0]` as it is handled separately.
    fn internal_layer_mat_mul(
        state: &mut [MontyField31<BabyBearParameters>; 16],
        sum: MontyField31<BabyBearParameters>,
    ) {
        // The diagonal matrix is defined by the vector:
        // V = [-2, 1, 2, 1/2, 3, 4, -1/2, -3, -4, 1/2^8, 1/4, 1/8, 1/2^27, -1/2^8, -1/16, -1/2^27]
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
        state[12] = state[12].div_2exp_u64(27);
        state[12] += sum;
        state[13] = state[13].div_2exp_u64(8);
        state[13] = sum - state[13];
        state[14] = state[14].div_2exp_u64(4);
        state[14] = sum - state[14];
        state[15] = state[15].div_2exp_u64(27);
        state[15] = sum - state[15];
    }

    fn generic_internal_linear_layer<A: Algebra<BabyBear>>(state: &mut [A; 16]) {
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

impl InternalLayerBaseParameters<BabyBearParameters, 24> for BabyBearInternalLayerParameters {
    type ArrayLike = [MontyField31<BabyBearParameters>; 23];

    const INTERNAL_DIAG_MONTY: [BabyBear; 24] = INTERNAL_DIAG_MONTY_24;

    /// Perform the internal matrix multiplication: s -> (1 + Diag(V))s.
    /// We ignore `state[0]` as it is handled separately.
    fn internal_layer_mat_mul(
        state: &mut [MontyField31<BabyBearParameters>; 24],
        sum: MontyField31<BabyBearParameters>,
    ) {
        // The diagonal matrix is defined by the vector:
        // V = [-2, 1, 2, 1/2, 3, 4, -1/2, -3, -4, 1/2^8, 1/4, 1/8, 1/16, 1/2^7, 1/2^9, 1/2^27, -1/2^8, -1/4, -1/8, -1/16, -1/32, -1/64, -1/2^7, -1/2^27]
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
        state[13] = state[13].div_2exp_u64(7);
        state[13] += sum;
        state[14] = state[14].div_2exp_u64(9);
        state[14] += sum;
        state[15] = state[15].div_2exp_u64(27);
        state[15] += sum;
        state[16] = state[16].div_2exp_u64(8);
        state[16] = sum - state[16];
        state[17] = state[17].div_2exp_u64(2);
        state[17] = sum - state[17];
        state[18] = state[18].div_2exp_u64(3);
        state[18] = sum - state[18];
        state[19] = state[19].div_2exp_u64(4);
        state[19] = sum - state[19];
        state[20] = state[20].div_2exp_u64(5);
        state[20] = sum - state[20];
        state[21] = state[21].div_2exp_u64(6);
        state[21] = sum - state[21];
        state[22] = state[22].div_2exp_u64(7);
        state[22] = sum - state[22];
        state[23] = state[23].div_2exp_u64(27);
        state[23] = sum - state[23];
    }

    fn generic_internal_linear_layer<A: Algebra<BabyBear>>(state: &mut [A; 24]) {
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

impl InternalLayerParameters<BabyBearParameters, 16> for BabyBearInternalLayerParameters {}
impl InternalLayerParameters<BabyBearParameters, 24> for BabyBearInternalLayerParameters {}

#[cfg(test)]
mod tests {
    use p3_symmetric::Permutation;
    use rand::{Rng, SeedableRng};
    use rand_xoshiro::Xoroshiro128Plus;

    use super::*;

    type F = BabyBear;

    // We need to make some round constants. We use Xoroshiro128Plus for this as we can easily match this PRNG in sage.
    // See: https://github.com/0xPolygonZero/hash-constants for the sage code used to create all these tests.

    /// Test on a roughly random input.
    /// This random input is generated by the following sage code:
    /// set_random_seed(16)
    /// vector([BB.random_element() for t in range(16)]).
    #[test]
    fn test_poseidon2_width_16_random() {
        let mut input: [F; 16] = BabyBear::new_array([
            894848333, 1437655012, 1200606629, 1690012884, 71131202, 1749206695, 1717947831,
            120589055, 19776022, 42382981, 1831865506, 724844064, 171220207, 1299207443, 227047920,
            1783754913,
        ]);

        let expected: [F; 16] = BabyBear::new_array([
            1255099308, 941729227, 93609187, 112406640, 492658670, 1824768948, 812517469,
            1055381989, 670973674, 1407235524, 891397172, 1003245378, 1381303998, 1564172645,
            1399931635, 1005462965,
        ]);

        let mut rng = Xoroshiro128Plus::seed_from_u64(1);
        let perm = Poseidon2BabyBear::new_from_rng_128(&mut rng);

        perm.permute_mut(&mut input);
        assert_eq!(input, expected);
    }

    /// Test on a roughly random input.
    /// This random input is generated by the following sage code:
    /// set_random_seed(24)
    /// vector([BB.random_element() for t in range(24)]).
    #[test]
    fn test_poseidon2_width_24_random() {
        let mut input: [F; 24] = BabyBear::new_array([
            886409618, 1327899896, 1902407911, 591953491, 648428576, 1844789031, 1198336108,
            355597330, 1799586834, 59617783, 790334801, 1968791836, 559272107, 31054313,
            1042221543, 474748436, 135686258, 263665994, 1962340735, 1741539604, 449439011,
            1131357108, 50869465, 1589724894,
        ]);

        let expected: [F; 24] = BabyBear::new_array([
            249424342, 562262148, 757431114, 354243402, 57767055, 976981973, 1393169022,
            1774550827, 1527742125, 1019514605, 1776327602, 266236737, 1412355182, 1070239213,
            426390978, 1775539440, 1527732214, 1101406020, 1417710778, 1699632661, 413672313,
            820348291, 1067197851, 1669055675,
        ]);

        let mut rng = Xoroshiro128Plus::seed_from_u64(1);
        let perm = Poseidon2BabyBear::new_from_rng_128(&mut rng);

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

        BabyBearInternalLayerParameters::internal_layer_mat_mul(&mut input1, full_sum);
        BabyBearInternalLayerParameters::generic_internal_linear_layer(&mut input2);

        assert_eq!(input1, input2);
    }

    /// Test the generic internal layer against the optimized internal layer
    /// for a random input of width 24.
    #[test]
    fn test_generic_internal_linear_layer_24() {
        let mut rng = Xoroshiro128Plus::seed_from_u64(1);
        let mut input1: [F; 24] = rng.random();
        let mut input2 = input1;

        let part_sum: F = input1[1..].iter().copied().sum();
        let full_sum = part_sum + input1[0];

        input1[0] = part_sum - input1[0];

        BabyBearInternalLayerParameters::internal_layer_mat_mul(&mut input1, full_sum);
        BabyBearInternalLayerParameters::generic_internal_linear_layer(&mut input2);

        assert_eq!(input1, input2);
    }
}
