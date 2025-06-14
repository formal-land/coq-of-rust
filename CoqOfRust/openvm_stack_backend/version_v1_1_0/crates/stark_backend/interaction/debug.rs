use std::collections::{BTreeMap, HashMap};

use itertools::Itertools;
use p3_field::Field;
use p3_matrix::{dense::RowMajorMatrixView, Matrix};

use super::{trace::Evaluator, BusIndex, SymbolicInteraction};
use crate::air_builders::symbolic::symbolic_expression::SymbolicEvaluator;

/// The actual interactions that are sent/received during a single run
/// of trace generation. For debugging purposes only.
#[derive(Default, Clone, Debug)]
pub struct LogicalInteractions<F: Field> {
    /// Bus index => (fields => (air_idx, count))
    #[allow(clippy::type_complexity)]
    pub at_bus: BTreeMap<BusIndex, HashMap<Vec<F>, Vec<(usize, F)>>>,
}

pub fn generate_logical_interactions<F: Field>(
    air_idx: usize,
    all_interactions: &[SymbolicInteraction<F>],
    preprocessed: &Option<RowMajorMatrixView<F>>,
    partitioned_main: &[RowMajorMatrixView<F>],
    public_values: &[F],
    logical_interactions: &mut LogicalInteractions<F>,
) {
    if all_interactions.is_empty() {
        return;
    }

    let height = partitioned_main[0].height();

    for n in 0..height {
        let evaluator = Evaluator {
            preprocessed,
            partitioned_main,
            public_values,
            height,
            local_index: n,
        };
        for interaction in all_interactions {
            let fields = interaction
                .message
                .iter()
                .map(|expr| evaluator.eval_expr(expr))
                .collect_vec();
            let count = evaluator.eval_expr(&interaction.count);
            if count.is_zero() {
                continue;
            }
            logical_interactions
                .at_bus
                .entry(interaction.bus_index)
                .or_default()
                .entry(fields)
                .or_default()
                .push((air_idx, count));
        }
    }
}
