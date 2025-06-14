use std::{
    borrow::BorrowMut,
    cmp::Reverse,
    sync::{atomic::AtomicU32, Arc},
};

use openvm_stark_backend::{
    config::{StarkGenericConfig, Val},
    p3_field::{FieldAlgebra, PrimeField32},
    p3_matrix::dense::RowMajorMatrix,
    prover::types::AirProofInput,
    AirRef, Chip, ChipUsageGetter,
};
use rustc_hash::FxHashSet;

use crate::{
    arch::hasher::HasherChip,
    system::{
        memory::{
            controller::dimensions::MemoryDimensions,
            merkle::{FinalState, MemoryMerkleChip, MemoryMerkleCols},
            tree::MemoryNode::{self, NonLeaf},
            Equipartition,
        },
        poseidon2::{
            Poseidon2PeripheryBaseChip, Poseidon2PeripheryChip, PERIPHERY_POSEIDON2_WIDTH,
        },
    },
};

impl<const CHUNK: usize, F: PrimeField32> MemoryMerkleChip<CHUNK, F> {
    pub fn finalize(
        &mut self,
        initial_tree: &MemoryNode<CHUNK, F>,
        final_memory: &Equipartition<F, CHUNK>,
        hasher: &mut impl HasherChip<CHUNK, F>,
    ) {
        assert!(self.final_state.is_none(), "Merkle chip already finalized");
        // there needs to be a touched node with `height_section` = 0
        // shouldn't be a leaf because
        // trace generation will expect an interaction from MemoryInterfaceChip in that case
        if self.touched_nodes.len() == 1 {
            self.touch_node(1, 0, 0);
        }

        let mut rows = vec![];
        let mut tree_helper = TreeHelper {
            memory_dimensions: self.air.memory_dimensions,
            final_memory,
            touched_nodes: &self.touched_nodes,
            trace_rows: &mut rows,
        };
        let final_tree = tree_helper.recur(
            self.air.memory_dimensions.overall_height(),
            initial_tree,
            0,
            0,
            hasher,
        );
        self.final_state = Some(FinalState {
            rows,
            init_root: initial_tree.hash(),
            final_root: final_tree.hash(),
        });
    }
}

impl<const CHUNK: usize, SC: StarkGenericConfig> Chip<SC> for MemoryMerkleChip<CHUNK, Val<SC>>
where
    Val<SC>: PrimeField32,
{
    fn air(&self) -> AirRef<SC> {
        Arc::new(self.air.clone())
    }

    fn generate_air_proof_input(self) -> AirProofInput<SC> {
        assert!(
            self.final_state.is_some(),
            "Merkle chip must finalize before trace generation"
        );
        let FinalState {
            mut rows,
            init_root,
            final_root,
        } = self.final_state.unwrap();
        // important that this sort be stable,
        // because we need the initial root to be first and the final root to be second
        rows.sort_by_key(|row| Reverse(row.parent_height));

        let width = MemoryMerkleCols::<Val<SC>, CHUNK>::width();
        let mut height = rows.len().next_power_of_two();
        if let Some(mut oh) = self.overridden_height {
            oh = oh.next_power_of_two();
            assert!(
                oh >= height,
                "Overridden height {oh} is less than the required height {height}"
            );
            height = oh;
        }
        let mut trace = Val::<SC>::zero_vec(width * height);

        for (trace_row, row) in trace.chunks_exact_mut(width).zip(rows) {
            *trace_row.borrow_mut() = row;
        }

        let trace = RowMajorMatrix::new(trace, width);
        let pvs = init_root.into_iter().chain(final_root).collect();
        AirProofInput::simple(trace, pvs)
    }
}
impl<const CHUNK: usize, F: PrimeField32> ChipUsageGetter for MemoryMerkleChip<CHUNK, F> {
    fn air_name(&self) -> String {
        "Merkle".to_string()
    }

    fn current_trace_height(&self) -> usize {
        2 * self.num_touched_nonleaves
    }

    fn trace_width(&self) -> usize {
        MemoryMerkleCols::<F, CHUNK>::width()
    }
}

struct TreeHelper<'a, const CHUNK: usize, F: PrimeField32> {
    memory_dimensions: MemoryDimensions,
    final_memory: &'a Equipartition<F, CHUNK>,
    touched_nodes: &'a FxHashSet<(usize, u32, u32)>,
    trace_rows: &'a mut Vec<MemoryMerkleCols<F, CHUNK>>,
}

impl<const CHUNK: usize, F: PrimeField32> TreeHelper<'_, CHUNK, F> {
    fn recur(
        &mut self,
        height: usize,
        initial_node: &MemoryNode<CHUNK, F>,
        as_label: u32,
        address_label: u32,
        hasher: &mut impl HasherChip<CHUNK, F>,
    ) -> MemoryNode<CHUNK, F> {
        if height == 0 {
            let address_space = as_label + self.memory_dimensions.as_offset;
            let leaf_values = *self
                .final_memory
                .get(&(address_space, address_label))
                .unwrap_or(&[F::ZERO; CHUNK]);
            MemoryNode::new_leaf(hasher.hash(&leaf_values))
        } else if let NonLeaf {
            left: initial_left_node,
            right: initial_right_node,
            ..
        } = initial_node.clone()
        {
            // Tell the hasher about this hash.
            hasher.compress_and_record(&initial_left_node.hash(), &initial_right_node.hash());

            let is_as_section = height > self.memory_dimensions.address_height;

            let (left_as_label, right_as_label) = if is_as_section {
                (2 * as_label, 2 * as_label + 1)
            } else {
                (as_label, as_label)
            };
            let (left_address_label, right_address_label) = if is_as_section {
                (address_label, address_label)
            } else {
                (2 * address_label, 2 * address_label + 1)
            };

            let left_is_final =
                !self
                    .touched_nodes
                    .contains(&(height - 1, left_as_label, left_address_label));

            let final_left_node = if left_is_final {
                initial_left_node
            } else {
                Arc::new(self.recur(
                    height - 1,
                    &initial_left_node,
                    left_as_label,
                    left_address_label,
                    hasher,
                ))
            };

            let right_is_final =
                !self
                    .touched_nodes
                    .contains(&(height - 1, right_as_label, right_address_label));

            let final_right_node = if right_is_final {
                initial_right_node
            } else {
                Arc::new(self.recur(
                    height - 1,
                    &initial_right_node,
                    right_as_label,
                    right_address_label,
                    hasher,
                ))
            };

            let final_node = MemoryNode::new_nonleaf(final_left_node, final_right_node, hasher);
            self.add_trace_row(height, as_label, address_label, initial_node, None);
            self.add_trace_row(
                height,
                as_label,
                address_label,
                &final_node,
                Some([left_is_final, right_is_final]),
            );
            final_node
        } else {
            panic!("Leaf {:?} found at nonzero height {}", initial_node, height);
        }
    }

    /// Expects `node` to be NonLeaf
    fn add_trace_row(
        &mut self,
        parent_height: usize,
        as_label: u32,
        address_label: u32,
        node: &MemoryNode<CHUNK, F>,
        direction_changes: Option<[bool; 2]>,
    ) {
        let [left_direction_change, right_direction_change] =
            direction_changes.unwrap_or([false; 2]);
        let cols = if let NonLeaf { hash, left, right } = node {
            MemoryMerkleCols {
                expand_direction: if direction_changes.is_none() {
                    F::ONE
                } else {
                    F::NEG_ONE
                },
                height_section: F::from_bool(parent_height > self.memory_dimensions.address_height),
                parent_height: F::from_canonical_usize(parent_height),
                is_root: F::from_bool(parent_height == self.memory_dimensions.overall_height()),
                parent_as_label: F::from_canonical_u32(as_label),
                parent_address_label: F::from_canonical_u32(address_label),
                parent_hash: *hash,
                left_child_hash: left.hash(),
                right_child_hash: right.hash(),
                left_direction_different: F::from_bool(left_direction_change),
                right_direction_different: F::from_bool(right_direction_change),
            }
        } else {
            panic!("trace_rows expects node = {:?} to be NonLeaf", node);
        };
        self.trace_rows.push(cols);
    }
}

pub trait SerialReceiver<T> {
    fn receive(&mut self, msg: T);
}

impl<'a, F: PrimeField32, const SBOX_REGISTERS: usize> SerialReceiver<&'a [F]>
    for Poseidon2PeripheryBaseChip<F, SBOX_REGISTERS>
{
    /// Receives a permutation preimage, pads with zeros to the permutation width, and records.
    /// The permutation preimage must have length at most the permutation width (panics otherwise).
    fn receive(&mut self, perm_preimage: &'a [F]) {
        assert!(perm_preimage.len() <= PERIPHERY_POSEIDON2_WIDTH);
        let mut state = [F::ZERO; PERIPHERY_POSEIDON2_WIDTH];
        state[..perm_preimage.len()].copy_from_slice(perm_preimage);
        let count = self.records.entry(state).or_insert(AtomicU32::new(0));
        count.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    }
}

impl<'a, F: PrimeField32> SerialReceiver<&'a [F]> for Poseidon2PeripheryChip<F> {
    fn receive(&mut self, perm_preimage: &'a [F]) {
        match self {
            Poseidon2PeripheryChip::Register0(chip) => chip.receive(perm_preimage),
            Poseidon2PeripheryChip::Register1(chip) => chip.receive(perm_preimage),
        }
    }
}
