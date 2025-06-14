use std::{borrow::Borrow, mem::size_of};

use openvm_circuit_primitives_derive::AlignedBorrow;
use openvm_stark_backend::{
    interaction::InteractionBuilder,
    p3_air::{Air, BaseAir},
    p3_matrix::Matrix,
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
};

use crate::system::memory::{offline_checker::MemoryBus, MemoryAddress};

#[derive(Clone, Copy, Debug, AlignedBorrow, derive_new::new)]
#[repr(C)]
pub struct DummyMemoryInteractionCols<T, const BLOCK_SIZE: usize> {
    pub address: MemoryAddress<T, T>,
    pub data: [T; BLOCK_SIZE],
    pub timestamp: T,
    /// The send frequency. Send corresponds to write. To read, set to negative.
    pub count: T,
}

#[derive(Clone, Copy, Debug, derive_new::new)]
pub struct MemoryDummyAir<const BLOCK_SIZE: usize> {
    pub bus: MemoryBus,
}

impl<const BLOCK_SIZE: usize, F> BaseAirWithPublicValues<F> for MemoryDummyAir<BLOCK_SIZE> {}
impl<const BLOCK_SIZE: usize, F> PartitionedBaseAir<F> for MemoryDummyAir<BLOCK_SIZE> {}
impl<const BLOCK_SIZE: usize, F> BaseAir<F> for MemoryDummyAir<BLOCK_SIZE> {
    fn width(&self) -> usize {
        size_of::<DummyMemoryInteractionCols<u8, BLOCK_SIZE>>()
    }
}

impl<const BLOCK_SIZE: usize, AB: InteractionBuilder> Air<AB> for MemoryDummyAir<BLOCK_SIZE> {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0);
        let local: &DummyMemoryInteractionCols<AB::Var, BLOCK_SIZE> = (*local).borrow();

        self.bus
            .send(local.address, local.data.to_vec(), local.timestamp)
            .eval(builder, local.count);
    }
}
