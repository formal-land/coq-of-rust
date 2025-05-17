//! Eventually this will hold a vectorized Neon implementation of Poseidon2 for PackedBabyBearNeon
//! Currently this is essentially a placeholder to allow compilation and testing on Neon devices.
//!
//! Converting the AVX2/AVX512 code across to Neon is on the TODO list.

#[cfg(test)]
mod tests {
    use p3_symmetric::Permutation;
    use rand::rngs::SmallRng;
    use rand::{Rng, SeedableRng};

    use crate::{BabyBear, PackedBabyBearNeon, Poseidon2BabyBear};

    type F = BabyBear;
    type Perm16 = Poseidon2BabyBear<16>;
    type Perm24 = Poseidon2BabyBear<24>;

    /// Test that the output is the same as the scalar version on a random input.
    #[test]
    fn test_neon_poseidon2_width_16() {
        let mut rng = SmallRng::seed_from_u64(1);

        // Our Poseidon2 implementation.
        let poseidon2 = Perm16::new_from_rng_128(&mut rng);

        let input: [F; 16] = rng.random();

        let mut expected = input;
        poseidon2.permute_mut(&mut expected);

        let mut neon_input = input.map(Into::<PackedBabyBearNeon>::into);
        poseidon2.permute_mut(&mut neon_input);

        let neon_output = neon_input.map(|x| x.0[0]);

        assert_eq!(neon_output, expected);
    }

    /// Test that the output is the same as the scalar version on a random input.
    #[test]
    fn test_neon_poseidon2_width_24() {
        let mut rng = SmallRng::seed_from_u64(1);

        // Our Poseidon2 implementation.
        let poseidon2 = Perm24::new_from_rng_128(&mut rng);

        let input: [F; 24] = rng.random();

        let mut expected = input;
        poseidon2.permute_mut(&mut expected);

        let mut neon_input = input.map(Into::<PackedBabyBearNeon>::into);
        poseidon2.permute_mut(&mut neon_input);

        let neon_output = neon_input.map(|x| x.0[0]);

        assert_eq!(neon_output, expected);
    }
}
