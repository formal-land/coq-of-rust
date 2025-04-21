//! Eventually this will hold a vectorized Neon implementation of Poseidon2 for PackedMersenne31Neon
//! Currently this is essentially a placeholder to allow compilation on Neon devices.
//!
//! Converting the AVX2/AVX512 code across to Neon is on the TODO list.

use alloc::vec::Vec;

use p3_poseidon2::{
    ExternalLayer, ExternalLayerConstants, ExternalLayerConstructor, GenericPoseidon2LinearLayers,
    InternalLayer, InternalLayerConstructor, MDSMat4, add_rc_and_sbox_generic,
    external_initial_permute_state, external_terminal_permute_state,
};

use crate::{GenericPoseidon2LinearLayersMersenne31, Mersenne31, PackedMersenne31Neon};

/// The internal layers of the Poseidon2 permutation.
#[derive(Debug, Clone)]
pub struct Poseidon2InternalLayerMersenne31 {
    pub(crate) internal_constants: Vec<Mersenne31>,
}

/// The external layers of the Poseidon2 permutation.
#[derive(Clone)]
pub struct Poseidon2ExternalLayerMersenne31<const WIDTH: usize> {
    pub(crate) external_constants: ExternalLayerConstants<Mersenne31, WIDTH>,
}

impl InternalLayerConstructor<Mersenne31> for Poseidon2InternalLayerMersenne31 {
    fn new_from_constants(internal_constants: Vec<Mersenne31>) -> Self {
        Self { internal_constants }
    }
}

impl<const WIDTH: usize> ExternalLayerConstructor<Mersenne31, WIDTH>
    for Poseidon2ExternalLayerMersenne31<WIDTH>
{
    fn new_from_constants(external_constants: ExternalLayerConstants<Mersenne31, WIDTH>) -> Self {
        Self { external_constants }
    }
}

impl<const WIDTH: usize, const D: u64> InternalLayer<PackedMersenne31Neon, WIDTH, D>
    for Poseidon2InternalLayerMersenne31
where
    GenericPoseidon2LinearLayersMersenne31:
        GenericPoseidon2LinearLayers<PackedMersenne31Neon, WIDTH>,
{
    /// Perform the internal layers of the Poseidon2 permutation on the given state.
    fn permute_state(&self, state: &mut [PackedMersenne31Neon; WIDTH]) {
        self.internal_constants.iter().for_each(|&rc| {
            add_rc_and_sbox_generic(&mut state[0], rc);
            GenericPoseidon2LinearLayersMersenne31::internal_linear_layer(state);
        })
    }
}

impl<const D: u64, const WIDTH: usize> ExternalLayer<PackedMersenne31Neon, WIDTH, D>
    for Poseidon2ExternalLayerMersenne31<WIDTH>
{
    /// Perform the initial external layers of the Poseidon2 permutation on the given state.
    fn permute_state_initial(&self, state: &mut [PackedMersenne31Neon; WIDTH]) {
        external_initial_permute_state(
            state,
            self.external_constants.get_initial_constants(),
            add_rc_and_sbox_generic,
            &MDSMat4,
        );
    }

    /// Perform the terminal external layers of the Poseidon2 permutation on the given state.
    fn permute_state_terminal(&self, state: &mut [PackedMersenne31Neon; WIDTH]) {
        external_terminal_permute_state(
            state,
            self.external_constants.get_terminal_constants(),
            add_rc_and_sbox_generic,
            &MDSMat4,
        );
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

    /// Test that the output is the same as the scalar version on a random input.
    #[test]
    fn test_neon_poseidon2_width_16() {
        let mut rng = SmallRng::seed_from_u64(1);

        // Our Poseidon2 implementation.
        let poseidon2 = Perm16::new_from_rng_128(&mut rng);

        let input: [F; 16] = rng.random();

        let mut expected = input;
        poseidon2.permute_mut(&mut expected);

        let mut neon_input = input.map(Into::<PackedMersenne31Neon>::into);
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

        let mut neon_input = input.map(Into::<PackedMersenne31Neon>::into);
        poseidon2.permute_mut(&mut neon_input);

        let neon_output = neon_input.map(|x| x.0[0]);

        assert_eq!(neon_output, expected);
    }
}
