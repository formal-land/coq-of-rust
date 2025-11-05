use std::array;

use openvm_stark_backend::p3_field::PrimeField32;
use rand::{rngs::StdRng, Rng};

pub fn i32_to_f<F: PrimeField32>(val: i32) -> F {
    if val.signum() == -1 {
        -F::from_canonical_u32(val.unsigned_abs())
    } else {
        F::from_canonical_u32(val as u32)
    }
}

pub fn generate_long_number<const NUM_LIMBS: usize, const LIMB_BITS: usize>(
    rng: &mut StdRng,
) -> [u32; NUM_LIMBS] {
    array::from_fn(|_| rng.gen_range(0..(1 << LIMB_BITS)))
}

// in little endian
pub fn u32_into_limbs<const NUM_LIMBS: usize, const LIMB_BITS: usize>(
    num: u32,
) -> [u32; NUM_LIMBS] {
    array::from_fn(|i| (num >> (LIMB_BITS * i)) & ((1 << LIMB_BITS) - 1))
}

pub fn u32_sign_extend<const IMM_BITS: usize>(num: u32) -> u32 {
    if num & (1 << (IMM_BITS - 1)) != 0 {
        num | (u32::MAX - (1 << IMM_BITS) + 1)
    } else {
        num
    }
}
