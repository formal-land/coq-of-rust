use openvm_stark_backend::{interaction::PermutationCheckBus, p3_field::PrimeField32};

use crate::system::memory::{
    merkle::MemoryMerkleChip, persistent::PersistentBoundaryChip, volatile::VolatileBoundaryChip,
    MemoryImage, CHUNK,
};

#[allow(clippy::large_enum_variant)]
pub enum MemoryInterface<F> {
    Volatile {
        boundary_chip: VolatileBoundaryChip<F>,
    },
    Persistent {
        boundary_chip: PersistentBoundaryChip<F, CHUNK>,
        merkle_chip: MemoryMerkleChip<CHUNK, F>,
        initial_memory: MemoryImage<F>,
    },
}

impl<F: PrimeField32> MemoryInterface<F> {
    pub fn touch_range(&mut self, addr_space: u32, pointer: u32, len: u32) {
        match self {
            MemoryInterface::Volatile { .. } => {}
            MemoryInterface::Persistent {
                boundary_chip,
                merkle_chip,
                ..
            } => {
                boundary_chip.touch_range(addr_space, pointer, len);
                merkle_chip.touch_range(addr_space, pointer, len);
            }
        }
    }

    pub fn compression_bus(&self) -> Option<PermutationCheckBus> {
        match self {
            MemoryInterface::Volatile { .. } => None,
            MemoryInterface::Persistent { merkle_chip, .. } => {
                Some(merkle_chip.air.compression_bus)
            }
        }
    }
}
