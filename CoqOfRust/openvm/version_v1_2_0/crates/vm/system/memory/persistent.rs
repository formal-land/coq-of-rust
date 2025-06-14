use std::{
    array,
    borrow::{Borrow, BorrowMut},
    iter,
    sync::Arc,
};

use openvm_circuit_primitives_derive::AlignedBorrow;
use openvm_stark_backend::{
    config::{StarkGenericConfig, Val},
    interaction::{InteractionBuilder, PermutationCheckBus},
    p3_air::{Air, AirBuilder, BaseAir},
    p3_field::{FieldAlgebra, PrimeField32},
    p3_matrix::{dense::RowMajorMatrix, Matrix},
    p3_maybe_rayon::prelude::*,
    prover::types::AirProofInput,
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
    AirRef, Chip, ChipUsageGetter,
};
use rustc_hash::FxHashSet;

use super::merkle::SerialReceiver;
use crate::{
    arch::hasher::Hasher,
    system::memory::{
        dimensions::MemoryDimensions, offline_checker::MemoryBus, MemoryAddress, MemoryImage,
        TimestampedEquipartition, INITIAL_TIMESTAMP,
    },
};

/// The values describe aligned chunk of memory of size `CHUNK`---the data together with the last
/// accessed timestamp---in either the initial or final memory state.
#[repr(C)]
#[derive(Debug, AlignedBorrow)]
pub struct PersistentBoundaryCols<T, const CHUNK: usize> {
    // `expand_direction` =  1 corresponds to initial memory state
    // `expand_direction` = -1 corresponds to final memory state
    // `expand_direction` =  0 corresponds to irrelevant row (all interactions multiplicity 0)
    pub expand_direction: T,
    pub address_space: T,
    pub leaf_label: T,
    pub values: [T; CHUNK],
    pub hash: [T; CHUNK],
    pub timestamp: T,
}

/// Imposes the following constraints:
/// - `expand_direction` should be -1, 0, 1
///
/// Sends the following interactions:
/// - if `expand_direction` is 1, sends `[0, 0, address_space_label, leaf_label]` to `merkle_bus`.
/// - if `expand_direction` is -1, receives `[1, 0, address_space_label, leaf_label]` from
///   `merkle_bus`.
#[derive(Clone, Debug)]
pub struct PersistentBoundaryAir<const CHUNK: usize> {
    pub memory_dims: MemoryDimensions,
    pub memory_bus: MemoryBus,
    pub merkle_bus: PermutationCheckBus,
    pub compression_bus: PermutationCheckBus,
}

impl<const CHUNK: usize, F> BaseAir<F> for PersistentBoundaryAir<CHUNK> {
    fn width(&self) -> usize {
        PersistentBoundaryCols::<F, CHUNK>::width()
    }
}

impl<const CHUNK: usize, F> BaseAirWithPublicValues<F> for PersistentBoundaryAir<CHUNK> {}
impl<const CHUNK: usize, F> PartitionedBaseAir<F> for PersistentBoundaryAir<CHUNK> {}

impl<const CHUNK: usize, AB: InteractionBuilder> Air<AB> for PersistentBoundaryAir<CHUNK> {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0);
        let local: &PersistentBoundaryCols<AB::Var, CHUNK> = (*local).borrow();

        // `direction` should be -1, 0, 1
        builder.assert_eq(
            local.expand_direction,
            local.expand_direction * local.expand_direction * local.expand_direction,
        );

        // Constrain that an "initial" row has timestamp zero.
        // Since `direction` is constrained to be in {-1, 0, 1}, we can select `direction == 1`
        // with the constraint below.
        builder
            .when(local.expand_direction * (local.expand_direction + AB::F::ONE))
            .assert_zero(local.timestamp);

        let mut expand_fields = vec![
            // direction =  1 => is_final = 0
            // direction = -1 => is_final = 1
            local.expand_direction.into(),
            AB::Expr::ZERO,
            local.address_space - AB::F::from_canonical_u32(self.memory_dims.as_offset),
            local.leaf_label.into(),
        ];
        expand_fields.extend(local.hash.map(Into::into));
        self.merkle_bus
            .interact(builder, expand_fields, local.expand_direction.into());

        self.compression_bus.interact(
            builder,
            iter::empty()
                .chain(local.values.map(Into::into))
                .chain(iter::repeat_n(AB::Expr::ZERO, CHUNK))
                .chain(local.hash.map(Into::into)),
            local.expand_direction * local.expand_direction,
        );

        self.memory_bus
            .send(
                MemoryAddress::new(
                    local.address_space,
                    local.leaf_label * AB::F::from_canonical_usize(CHUNK),
                ),
                local.values.to_vec(),
                local.timestamp,
            )
            .eval(builder, local.expand_direction);
    }
}

pub struct PersistentBoundaryChip<F, const CHUNK: usize> {
    pub air: PersistentBoundaryAir<CHUNK>,
    touched_labels: TouchedLabels<F, CHUNK>,
    overridden_height: Option<usize>,
}

#[derive(Debug)]
enum TouchedLabels<F, const CHUNK: usize> {
    Running(FxHashSet<(u32, u32)>),
    Final(Vec<FinalTouchedLabel<F, CHUNK>>),
}

#[derive(Debug)]
struct FinalTouchedLabel<F, const CHUNK: usize> {
    address_space: u32,
    label: u32,
    init_values: [F; CHUNK],
    final_values: [F; CHUNK],
    init_hash: [F; CHUNK],
    final_hash: [F; CHUNK],
    final_timestamp: u32,
}

impl<F: PrimeField32, const CHUNK: usize> Default for TouchedLabels<F, CHUNK> {
    fn default() -> Self {
        Self::Running(FxHashSet::default())
    }
}

impl<F: PrimeField32, const CHUNK: usize> TouchedLabels<F, CHUNK> {
    fn touch(&mut self, address_space: u32, label: u32) {
        match self {
            TouchedLabels::Running(touched_labels) => {
                touched_labels.insert((address_space, label));
            }
            _ => panic!("Cannot touch after finalization"),
        }
    }
    fn len(&self) -> usize {
        match self {
            TouchedLabels::Running(touched_labels) => touched_labels.len(),
            TouchedLabels::Final(touched_labels) => touched_labels.len(),
        }
    }
}

impl<const CHUNK: usize, F: PrimeField32> PersistentBoundaryChip<F, CHUNK> {
    pub fn new(
        memory_dimensions: MemoryDimensions,
        memory_bus: MemoryBus,
        merkle_bus: PermutationCheckBus,
        compression_bus: PermutationCheckBus,
    ) -> Self {
        Self {
            air: PersistentBoundaryAir {
                memory_dims: memory_dimensions,
                memory_bus,
                merkle_bus,
                compression_bus,
            },
            touched_labels: Default::default(),
            overridden_height: None,
        }
    }

    pub fn set_overridden_height(&mut self, overridden_height: usize) {
        self.overridden_height = Some(overridden_height);
    }

    pub fn touch_range(&mut self, address_space: u32, pointer: u32, len: u32) {
        let start_label = pointer / CHUNK as u32;
        let end_label = (pointer + len - 1) / CHUNK as u32;
        for label in start_label..=end_label {
            self.touched_labels.touch(address_space, label);
        }
    }

    pub fn finalize<H>(
        &mut self,
        initial_memory: &MemoryImage<F>,
        final_memory: &TimestampedEquipartition<F, CHUNK>,
        hasher: &mut H,
    ) where
        H: Hasher<CHUNK, F> + Sync + for<'a> SerialReceiver<&'a [F]>,
    {
        match &mut self.touched_labels {
            TouchedLabels::Running(touched_labels) => {
                let final_touched_labels: Vec<_> = touched_labels
                    .par_iter()
                    .map(|&(address_space, label)| {
                        let pointer = label * CHUNK as u32;
                        let init_values = array::from_fn(|i| {
                            *initial_memory
                                .get(&(address_space, pointer + i as u32))
                                .unwrap_or(&F::ZERO)
                        });
                        let initial_hash = hasher.hash(&init_values);
                        let timestamped_values = final_memory.get(&(address_space, label)).unwrap();
                        let final_hash = hasher.hash(&timestamped_values.values);
                        FinalTouchedLabel {
                            address_space,
                            label,
                            init_values,
                            final_values: timestamped_values.values,
                            init_hash: initial_hash,
                            final_hash,
                            final_timestamp: timestamped_values.timestamp,
                        }
                    })
                    .collect();
                for l in &final_touched_labels {
                    hasher.receive(&l.init_values);
                    hasher.receive(&l.final_values);
                }
                self.touched_labels = TouchedLabels::Final(final_touched_labels);
            }
            _ => panic!("Cannot finalize after finalization"),
        }
    }
}

impl<const CHUNK: usize, SC: StarkGenericConfig> Chip<SC> for PersistentBoundaryChip<Val<SC>, CHUNK>
where
    Val<SC>: PrimeField32,
{
    fn air(&self) -> AirRef<SC> {
        Arc::new(self.air.clone())
    }

    fn generate_air_proof_input(self) -> AirProofInput<SC> {
        let trace = {
            let width = PersistentBoundaryCols::<Val<SC>, CHUNK>::width();
            // Boundary AIR should always present in order to fix the AIR ID of merkle AIR.
            let mut height = (2 * self.touched_labels.len()).next_power_of_two();
            if let Some(mut oh) = self.overridden_height {
                oh = oh.next_power_of_two();
                assert!(
                    oh >= height,
                    "Overridden height is less than the required height"
                );
                height = oh;
            }
            let mut rows = Val::<SC>::zero_vec(height * width);

            let touched_labels = match self.touched_labels {
                TouchedLabels::Final(touched_labels) => touched_labels,
                _ => panic!("Cannot generate trace before finalization"),
            };

            rows.par_chunks_mut(2 * width)
                .zip(touched_labels.into_par_iter())
                .for_each(|(row, touched_label)| {
                    let (initial_row, final_row) = row.split_at_mut(width);
                    *initial_row.borrow_mut() = PersistentBoundaryCols {
                        expand_direction: Val::<SC>::ONE,
                        address_space: Val::<SC>::from_canonical_u32(touched_label.address_space),
                        leaf_label: Val::<SC>::from_canonical_u32(touched_label.label),
                        values: touched_label.init_values,
                        hash: touched_label.init_hash,
                        timestamp: Val::<SC>::from_canonical_u32(INITIAL_TIMESTAMP),
                    };

                    *final_row.borrow_mut() = PersistentBoundaryCols {
                        expand_direction: Val::<SC>::NEG_ONE,
                        address_space: Val::<SC>::from_canonical_u32(touched_label.address_space),
                        leaf_label: Val::<SC>::from_canonical_u32(touched_label.label),
                        values: touched_label.final_values,
                        hash: touched_label.final_hash,
                        timestamp: Val::<SC>::from_canonical_u32(touched_label.final_timestamp),
                    };
                });
            RowMajorMatrix::new(rows, width)
        };
        AirProofInput::simple_no_pis(trace)
    }
}

impl<const CHUNK: usize, F: PrimeField32> ChipUsageGetter for PersistentBoundaryChip<F, CHUNK> {
    fn air_name(&self) -> String {
        "Boundary".to_string()
    }

    fn current_trace_height(&self) -> usize {
        2 * self.touched_labels.len()
    }

    fn trace_width(&self) -> usize {
        PersistentBoundaryCols::<F, CHUNK>::width()
    }
}
