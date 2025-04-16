//! These are just simple wrapper structs allowing us to implement Poseidon2 Internal/ExternalLayer on top of them.
//!
//! They are used only in the case that none of the vectorization architectures (AVX2/AVX512/NEON) are available.

use alloc::vec::Vec;
use core::marker::PhantomData;

use p3_poseidon2::{ExternalLayerConstants, ExternalLayerConstructor, InternalLayerConstructor};

use crate::{FieldParameters, InternalLayerBaseParameters, MontyField31, MontyParameters};

/// The internal layers of the Poseidon2 permutation for Monty31 fields.
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
