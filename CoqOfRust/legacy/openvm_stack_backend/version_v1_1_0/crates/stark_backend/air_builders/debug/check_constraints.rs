use itertools::izip;
use p3_air::BaseAir;
use p3_field::{Field, FieldAlgebra};
use p3_matrix::{dense::RowMajorMatrixView, stack::VerticalPair, Matrix};
use p3_maybe_rayon::prelude::*;

use crate::{
    air_builders::debug::DebugConstraintBuilder,
    config::{StarkGenericConfig, Val},
    interaction::{
        debug::{generate_logical_interactions, LogicalInteractions},
        RapPhaseSeqKind, SymbolicInteraction,
    },
    rap::{PartitionedBaseAir, Rap},
};

/// Check that all constraints vanish on the subgroup.
#[allow(clippy::too_many_arguments)]
pub fn check_constraints<R, SC>(
    rap: &R,
    rap_name: &str,
    preprocessed: &Option<RowMajorMatrixView<Val<SC>>>,
    partitioned_main: &[RowMajorMatrixView<Val<SC>>],
    public_values: &[Val<SC>],
) where
    R: for<'a> Rap<DebugConstraintBuilder<'a, SC>>
        + BaseAir<Val<SC>>
        + PartitionedBaseAir<Val<SC>>
        + ?Sized,
    SC: StarkGenericConfig,
{
    let height = partitioned_main[0].height();
    assert!(partitioned_main.iter().all(|mat| mat.height() == height));

    // Check that constraints are satisfied.
    (0..height).into_par_iter().for_each(|i| {
        let i_next = (i + 1) % height;

        let (preprocessed_local, preprocessed_next) = preprocessed
            .as_ref()
            .map(|preprocessed| {
                (
                    preprocessed.row_slice(i).to_vec(),
                    preprocessed.row_slice(i_next).to_vec(),
                )
            })
            .unwrap_or((vec![], vec![]));

        let partitioned_main_row_pair = partitioned_main
            .iter()
            .map(|part| (part.row_slice(i), part.row_slice(i_next)))
            .collect::<Vec<_>>();
        let partitioned_main = partitioned_main_row_pair
            .iter()
            .map(|(local, next)| {
                VerticalPair::new(
                    RowMajorMatrixView::new_row(local),
                    RowMajorMatrixView::new_row(next),
                )
            })
            .collect::<Vec<_>>();

        let mut builder = DebugConstraintBuilder {
            air_name: rap_name,
            row_index: i,
            preprocessed: VerticalPair::new(
                RowMajorMatrixView::new_row(preprocessed_local.as_slice()),
                RowMajorMatrixView::new_row(preprocessed_next.as_slice()),
            ),
            partitioned_main,
            after_challenge: vec![], // unreachable
            challenges: &[],         // unreachable
            public_values,
            exposed_values_after_challenge: &[], // unreachable
            is_first_row: Val::<SC>::ZERO,
            is_last_row: Val::<SC>::ZERO,
            is_transition: Val::<SC>::ONE,
            rap_phase_seq_kind: RapPhaseSeqKind::FriLogUp, // unused
            has_common_main: rap.common_main_width() > 0,
        };
        if i == 0 {
            builder.is_first_row = Val::<SC>::ONE;
        }
        if i == height - 1 {
            builder.is_last_row = Val::<SC>::ONE;
            builder.is_transition = Val::<SC>::ZERO;
        }

        rap.eval(&mut builder);
    });
}

pub fn check_logup<F: Field>(
    air_names: &[String],
    interactions: &[Vec<SymbolicInteraction<F>>],
    preprocessed: &[Option<RowMajorMatrixView<F>>],
    partitioned_main: &[Vec<RowMajorMatrixView<F>>],
    public_values: &[Vec<F>],
) {
    let mut logical_interactions = LogicalInteractions::<F>::default();
    for (air_idx, (interactions, preprocessed, partitioned_main, public_values)) in
        izip!(interactions, preprocessed, partitioned_main, public_values).enumerate()
    {
        generate_logical_interactions(
            air_idx,
            interactions,
            preprocessed,
            partitioned_main,
            public_values,
            &mut logical_interactions,
        );
    }

    let mut logup_failed = false;
    // For each bus, check each `fields` key by summing up multiplicities.
    for (bus_idx, bus_interactions) in logical_interactions.at_bus.into_iter() {
        for (fields, connections) in bus_interactions.into_iter() {
            let sum: F = connections.iter().map(|(_, count)| *count).sum();
            if !sum.is_zero() {
                logup_failed = true;
                println!(
                    "Bus {} failed to balance the multiplicities for fields={:?}. The bus connections for this were:",
                    bus_idx, fields
                );
                for (air_idx, count) in connections {
                    println!(
                        "   Air idx: {}, Air name: {}, count: {:?}",
                        air_idx, air_names[air_idx], count
                    );
                }
            }
        }
    }
    if logup_failed {
        panic!("LogUp multiset equality check failed.");
    }
}
