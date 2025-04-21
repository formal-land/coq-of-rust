//! Eventually this will hold a Vectorized Neon implementation of Poseidon2 for MontyField31
//! Currently this is essentially a placeholder to allow compilation on Neon devices.
//!
//! Converting the AVX2/AVX512 code across to Neon is on the TODO list.

use alloc::vec::Vec;
use core::marker::PhantomData;

use p3_poseidon2::{
    ExternalLayer, ExternalLayerConstants, ExternalLayerConstructor, InternalLayer,
    InternalLayerConstructor, MDSMat4, add_rc_and_sbox_generic, external_initial_permute_state,
    external_terminal_permute_state,
};

use crate::{
    FieldParameters, InternalLayerBaseParameters, MontyField31, MontyParameters,
    PackedMontyField31Neon, RelativelyPrimePower,
};

/// The internal layers of the Poseidon2 permutation for Monty31 fields.
///
/// This is currently not optimized for the Neon architecture but this is on the TODO list.
#[derive(Debug, Clone)]
pub struct Poseidon2InternalLayerMonty31<
    MP: MontyParameters,
    const WIDTH: usize,
    ILP: InternalLayerBaseParameters<MP, WIDTH>,
> {
    pub(crate) internal_constants: Vec<MontyField31<MP>>,
    _phantom: PhantomData<ILP>,
}

/// The external layers of the Poseidon2 permutation for Monty31 fields.
///
/// This is currently not optimized for the Neon architecture but this is on the TODO list.
#[derive(Debug, Clone)]
pub struct Poseidon2ExternalLayerMonty31<MP: MontyParameters, const WIDTH: usize> {
    pub(crate) external_constants: ExternalLayerConstants<MontyField31<MP>, WIDTH>,
}

impl<FP: FieldParameters, const WIDTH: usize, ILP: InternalLayerBaseParameters<FP, WIDTH>>
    InternalLayerConstructor<MontyField31<FP>> for Poseidon2InternalLayerMonty31<FP, WIDTH, ILP>
{
    fn new_from_constants(internal_constants: Vec<MontyField31<FP>>) -> Self {
        Self {
            internal_constants,
            _phantom: PhantomData,
        }
    }
}

impl<FP: FieldParameters, const WIDTH: usize> ExternalLayerConstructor<MontyField31<FP>, WIDTH>
    for Poseidon2ExternalLayerMonty31<FP, WIDTH>
{
    fn new_from_constants(
        external_constants: ExternalLayerConstants<MontyField31<FP>, WIDTH>,
    ) -> Self {
        Self { external_constants }
    }
}

impl<FP, ILP, const WIDTH: usize, const D: u64> InternalLayer<PackedMontyField31Neon<FP>, WIDTH, D>
    for Poseidon2InternalLayerMonty31<FP, WIDTH, ILP>
where
    FP: FieldParameters + RelativelyPrimePower<D>,
    ILP: InternalLayerBaseParameters<FP, WIDTH>,
{
    /// Perform the internal layers of the Poseidon2 permutation on the given state.
    fn permute_state(&self, state: &mut [PackedMontyField31Neon<FP>; WIDTH]) {
        self.internal_constants.iter().for_each(|&rc| {
            add_rc_and_sbox_generic(&mut state[0], rc);
            ILP::generic_internal_linear_layer(state);
        })
    }
}

impl<FP, const D: u64, const WIDTH: usize> ExternalLayer<PackedMontyField31Neon<FP>, WIDTH, D>
    for Poseidon2ExternalLayerMonty31<FP, WIDTH>
where
    FP: FieldParameters + RelativelyPrimePower<D>,
{
    /// Perform the initial external layers of the Poseidon2 permutation on the given state.
    fn permute_state_initial(&self, state: &mut [PackedMontyField31Neon<FP>; WIDTH]) {
        external_initial_permute_state(
            state,
            self.external_constants.get_initial_constants(),
            add_rc_and_sbox_generic,
            &MDSMat4,
        );
    }

    /// Perform the terminal external layers of the Poseidon2 permutation on the given state.
    fn permute_state_terminal(&self, state: &mut [PackedMontyField31Neon<FP>; WIDTH]) {
        external_terminal_permute_state(
            state,
            self.external_constants.get_terminal_constants(),
            add_rc_and_sbox_generic,
            &MDSMat4,
        );
    }
}
