use openvm_stark_backend::{interaction::PermutationCheckBus, p3_field::PrimeField32};
use rustc_hash::FxHashSet;

use super::controller::dimensions::MemoryDimensions;
mod air;
mod columns;
mod trace;

pub use air::*;
pub use columns::*;
pub(super) use trace::SerialReceiver;

#[cfg(test)]
mod tests;

pub struct MemoryMerkleChip<const CHUNK: usize, F> {
    pub air: MemoryMerkleAir<CHUNK>,
    touched_nodes: FxHashSet<(usize, u32, u32)>,
    num_touched_nonleaves: usize,
    final_state: Option<FinalState<CHUNK, F>>,
    overridden_height: Option<usize>,
}
#[derive(Debug)]
struct FinalState<const CHUNK: usize, F> {
    rows: Vec<MemoryMerkleCols<F, CHUNK>>,
    init_root: [F; CHUNK],
    final_root: [F; CHUNK],
}

impl<const CHUNK: usize, F: PrimeField32> MemoryMerkleChip<CHUNK, F> {
    /// `compression_bus` is the bus for direct (no-memory involved) interactions to call the
    /// cryptographic compression function.
    pub fn new(
        memory_dimensions: MemoryDimensions,
        merkle_bus: PermutationCheckBus,
        compression_bus: PermutationCheckBus,
    ) -> Self {
        assert!(memory_dimensions.as_height > 0);
        assert!(memory_dimensions.address_height > 0);
        let mut touched_nodes = FxHashSet::default();
        touched_nodes.insert((memory_dimensions.overall_height(), 0, 0));
        Self {
            air: MemoryMerkleAir {
                memory_dimensions,
                merkle_bus,
                compression_bus,
            },
            touched_nodes,
            num_touched_nonleaves: 1,
            final_state: None,
            overridden_height: None,
        }
    }
    pub fn set_overridden_height(&mut self, override_height: usize) {
        self.overridden_height = Some(override_height);
    }

    fn touch_node(&mut self, height: usize, as_label: u32, address_label: u32) {
        if self.touched_nodes.insert((height, as_label, address_label)) {
            assert_ne!(height, self.air.memory_dimensions.overall_height());
            if height != 0 {
                self.num_touched_nonleaves += 1;
            }
            if height >= self.air.memory_dimensions.address_height {
                self.touch_node(height + 1, as_label / 2, address_label);
            } else {
                self.touch_node(height + 1, as_label, address_label / 2);
            }
        }
    }

    pub fn touch_range(&mut self, address_space: u32, address: u32, len: u32) {
        let as_label = address_space - self.air.memory_dimensions.as_offset;
        let first_address_label = address / CHUNK as u32;
        let last_address_label = (address + len - 1) / CHUNK as u32;
        for address_label in first_address_label..=last_address_label {
            self.touch_node(0, as_label, address_label);
        }
    }
}
