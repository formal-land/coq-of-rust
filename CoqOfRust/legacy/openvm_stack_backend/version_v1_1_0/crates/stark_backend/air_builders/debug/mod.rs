use std::sync::{Arc, Mutex};

use itertools::{izip, Itertools};
use p3_air::{
    AirBuilder, AirBuilderWithPublicValues, ExtensionBuilder, PairBuilder, PermutationAirBuilder,
};
use p3_field::FieldAlgebra;
use p3_matrix::{dense::RowMajorMatrixView, stack::VerticalPair};

use super::{symbolic::SymbolicConstraints, PartitionedAirBuilder, ViewPair};
use crate::{
    config::{StarkGenericConfig, Val},
    interaction::{
        rap::InteractionPhaseAirBuilder, Interaction, InteractionBuilder, RapPhaseSeqKind,
        SymbolicInteraction,
    },
    keygen::types::StarkProvingKey,
    rap::{AnyRap, PermutationAirBuilderWithExposedValues},
};

mod check_constraints;

use check_constraints::*;

use crate::interaction::BusIndex;

thread_local! {
   pub static USE_DEBUG_BUILDER: Arc<Mutex<bool>> = Arc::new(Mutex::new(true));
}

/// The debugging will check the main AIR constraints and then separately check LogUp constraints by
/// checking the actual multiset equalities. Currently it will not debug check any after challenge phase
/// constraints for implementation simplicity.
#[allow(dead_code)]
#[allow(clippy::too_many_arguments)]
pub fn debug_constraints_and_interactions<SC: StarkGenericConfig>(
    airs: &[Arc<dyn AnyRap<SC>>],
    pk: &[StarkProvingKey<SC>],
    main_views_per_air: &[Vec<RowMajorMatrixView<'_, Val<SC>>>],
    public_values_per_air: &[Vec<Val<SC>>],
) {
    USE_DEBUG_BUILDER.with(|debug| {
        if *debug.lock().unwrap() {
            let preprocessed = izip!(airs, pk, main_views_per_air, public_values_per_air,)
                .map(|(rap, pk, main, public_values)| {
                    let preprocessed_trace = pk
                        .preprocessed_data
                        .as_ref()
                        .map(|data| data.trace.as_view());
                    tracing::debug!("Checking constraints for {}", rap.name());
                    check_constraints(
                        rap.as_ref(),
                        &rap.name(),
                        &preprocessed_trace,
                        main,
                        public_values,
                    );
                    preprocessed_trace
                })
                .collect_vec();

            let (air_names, interactions): (Vec<_>, Vec<_>) = pk
                .iter()
                .map(|pk| {
                    let sym_constraints = SymbolicConstraints::from(&pk.vk.symbolic_constraints);
                    (pk.air_name.clone(), sym_constraints.interactions)
                })
                .unzip();
            check_logup(
                &air_names,
                &interactions,
                &preprocessed,
                main_views_per_air,
                public_values_per_air,
            );
        }
    });
}

/// An `AirBuilder` which asserts that each constraint is zero, allowing any failed constraints to
/// be detected early.
pub struct DebugConstraintBuilder<'a, SC: StarkGenericConfig> {
    pub air_name: &'a str,
    pub row_index: usize,
    pub preprocessed: ViewPair<'a, Val<SC>>,
    pub partitioned_main: Vec<ViewPair<'a, Val<SC>>>,
    pub after_challenge: Vec<ViewPair<'a, SC::Challenge>>,
    pub challenges: &'a [Vec<SC::Challenge>],
    pub is_first_row: Val<SC>,
    pub is_last_row: Val<SC>,
    pub is_transition: Val<SC>,
    pub public_values: &'a [Val<SC>],
    pub exposed_values_after_challenge: &'a [Vec<SC::Challenge>],
    pub rap_phase_seq_kind: RapPhaseSeqKind,
    pub has_common_main: bool,
}

impl<'a, SC> AirBuilder for DebugConstraintBuilder<'a, SC>
where
    SC: StarkGenericConfig,
{
    type F = Val<SC>;
    type Expr = Val<SC>;
    type Var = Val<SC>;
    type M = VerticalPair<RowMajorMatrixView<'a, Val<SC>>, RowMajorMatrixView<'a, Val<SC>>>;

    /// It is difficult to horizontally concatenate matrices when the main trace is partitioned, so we disable this method in that case.
    fn main(&self) -> Self::M {
        if self.partitioned_main.len() == 1 {
            self.partitioned_main[0]
        } else {
            panic!("Main trace is either empty or partitioned. This function should not be used.")
        }
    }

    fn is_first_row(&self) -> Self::Expr {
        self.is_first_row
    }

    fn is_last_row(&self) -> Self::Expr {
        self.is_last_row
    }

    fn is_transition_window(&self, size: usize) -> Self::Expr {
        if size == 2 {
            self.is_transition
        } else {
            panic!("only supports a window size of 2")
        }
    }

    fn assert_zero<I: Into<Self::Expr>>(&mut self, x: I) {
        assert_eq!(
            x.into(),
            Val::<SC>::ZERO,
            "constraints had nonzero value on air {},row {}",
            self.air_name,
            self.row_index
        );
    }

    fn assert_eq<I1: Into<Self::Expr>, I2: Into<Self::Expr>>(&mut self, x: I1, y: I2) {
        let x = x.into();
        let y = y.into();
        assert_eq!(
            x, y,
            "values didn't match on air {}, row {}: {} != {}",
            self.air_name, self.row_index, x, y
        );
    }
}

impl<SC> PairBuilder for DebugConstraintBuilder<'_, SC>
where
    SC: StarkGenericConfig,
{
    fn preprocessed(&self) -> Self::M {
        self.preprocessed
    }
}

impl<SC> ExtensionBuilder for DebugConstraintBuilder<'_, SC>
where
    SC: StarkGenericConfig,
{
    type EF = SC::Challenge;
    type ExprEF = SC::Challenge;
    type VarEF = SC::Challenge;

    fn assert_zero_ext<I>(&mut self, x: I)
    where
        I: Into<Self::ExprEF>,
    {
        assert_eq!(
            x.into(),
            SC::Challenge::ZERO,
            "constraints had nonzero value on row {}",
            self.row_index
        );
    }

    fn assert_eq_ext<I1, I2>(&mut self, x: I1, y: I2)
    where
        I1: Into<Self::ExprEF>,
        I2: Into<Self::ExprEF>,
    {
        let x = x.into();
        let y = y.into();
        assert_eq!(
            x, y,
            "values didn't match on air {}, row {}: {} != {}",
            self.air_name, self.row_index, x, y
        );
    }
}

impl<'a, SC> PermutationAirBuilder for DebugConstraintBuilder<'a, SC>
where
    SC: StarkGenericConfig,
{
    type MP = ViewPair<'a, SC::Challenge>;

    type RandomVar = SC::Challenge;

    fn permutation(&self) -> Self::MP {
        *self
            .after_challenge
            .first()
            .expect("Challenge phase not supported")
    }

    fn permutation_randomness(&self) -> &[Self::EF] {
        self.challenges
            .first()
            .expect("Challenge phase not supported")
    }
}

impl<SC> AirBuilderWithPublicValues for DebugConstraintBuilder<'_, SC>
where
    SC: StarkGenericConfig,
{
    type PublicVar = Val<SC>;

    fn public_values(&self) -> &[Self::F] {
        self.public_values
    }
}

impl<SC> PermutationAirBuilderWithExposedValues for DebugConstraintBuilder<'_, SC>
where
    SC: StarkGenericConfig,
{
    fn permutation_exposed_values(&self) -> &[Self::EF] {
        self.exposed_values_after_challenge
            .first()
            .expect("Challenge phase not supported")
    }
}

impl<SC> PartitionedAirBuilder for DebugConstraintBuilder<'_, SC>
where
    SC: StarkGenericConfig,
{
    fn cached_mains(&self) -> &[Self::M] {
        let mut num_cached_mains = self.partitioned_main.len();
        if self.has_common_main {
            num_cached_mains -= 1;
        }
        &self.partitioned_main[..num_cached_mains]
    }
    fn common_main(&self) -> &Self::M {
        assert!(self.has_common_main, "AIR doesn't have a common main trace");
        self.partitioned_main.last().unwrap()
    }
}

// No-op implementation
impl<SC> InteractionBuilder for DebugConstraintBuilder<'_, SC>
where
    SC: StarkGenericConfig,
{
    fn push_interaction<E: Into<Self::Expr>>(
        &mut self,
        _bus_index: BusIndex,
        _fields: impl IntoIterator<Item = E>,
        _count: impl Into<Self::Expr>,
        _count_weight: u32,
    ) {
        // no-op, interactions are debugged elsewhere
    }

    fn num_interactions(&self) -> usize {
        0
    }

    fn all_interactions(&self) -> &[Interaction<Self::Expr>] {
        &[]
    }
}

// No-op
impl<SC: StarkGenericConfig> InteractionPhaseAirBuilder for DebugConstraintBuilder<'_, SC> {
    fn finalize_interactions(&mut self) {}

    fn max_constraint_degree(&self) -> usize {
        0
    }

    fn rap_phase_seq_kind(&self) -> RapPhaseSeqKind {
        self.rap_phase_seq_kind
    }

    fn symbolic_interactions(&self) -> Vec<SymbolicInteraction<Val<SC>>> {
        vec![]
    }
}
