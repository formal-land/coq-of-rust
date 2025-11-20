// Originally copied from uni-stark/src/symbolic_builder.rs to allow A: ?Sized

use itertools::Itertools;
use p3_air::{
    AirBuilder, AirBuilderWithPublicValues, ExtensionBuilder, PairBuilder, PermutationAirBuilder,
};
use p3_field::Field;
use p3_matrix::{dense::RowMajorMatrix, Matrix};
use p3_util::log2_ceil_usize;
use tracing::instrument;

use self::{
    symbolic_expression::SymbolicExpression,
    symbolic_variable::{Entry, SymbolicVariable},
};
use super::PartitionedAirBuilder;
use crate::{
    interaction::{
        fri_log_up::find_interaction_chunks, rap::InteractionPhaseAirBuilder, Interaction,
        InteractionBuilder, RapPhaseSeqKind, SymbolicInteraction,
    },
    keygen::types::{StarkVerifyingParams, TraceWidth},
    rap::{BaseAirWithPublicValues, PermutationAirBuilderWithExposedValues, Rap},
};

mod dag;
pub mod symbolic_expression;
pub mod symbolic_variable;

pub use dag::*;

use crate::interaction::BusIndex;

/// Symbolic constraints for a single AIR with interactions.
/// The constraints contain the constraints on the logup partial sums.
#[derive(Clone, Debug)]
pub struct SymbolicConstraints<F> {
    /// All constraints of the RAP, including the constraints on the logup partial sums.
    pub constraints: Vec<SymbolicExpression<F>>,
    /// Symbolic representation of chip interactions. This is used by
    /// the prover for after challenge trace generation, and some partial
    /// information may be used by the verifier.
    ///
    /// **However**, any contributions to the quotient polynomial from
    /// logup are already included in `constraints` and do not need to
    /// be separately calculated from `interactions`.
    pub interactions: Vec<SymbolicInteraction<F>>,
}

impl<F: Field> SymbolicConstraints<F> {
    pub fn max_constraint_degree(&self) -> usize {
        Iterator::max(self.constraints.iter().map(|c| c.degree_multiple())).unwrap_or(0)
    }

    pub fn get_log_quotient_degree(&self) -> usize {
        // We pad to at least degree 2, since a quotient argument doesn't make sense with smaller degrees.
        let constraint_degree = self.max_constraint_degree().max(2);

        // The quotient's actual degree is approximately (max_constraint_degree - 1) * (trace height),
        // where subtracting 1 comes from division by the zerofier.
        // But we pad it to a power of two so that we can efficiently decompose the quotient.
        log2_ceil_usize(constraint_degree - 1)
    }

    /// Returns the maximum field degree and count degree across all interactions
    pub fn max_interaction_degrees(&self) -> (usize, usize) {
        let max_field_degree = self
            .interactions
            .iter()
            .map(|interaction| {
                interaction
                    .message
                    .iter()
                    .map(|field| field.degree_multiple())
                    .max()
                    .unwrap_or(0)
            })
            .max()
            .unwrap_or(0);

        let max_count_degree = self
            .interactions
            .iter()
            .map(|interaction| interaction.count.degree_multiple())
            .max()
            .unwrap_or(0);

        (max_field_degree, max_count_degree)
    }
}

#[instrument(name = "evaluate constraints symbolically", skip_all, level = "debug")]
pub fn get_symbolic_builder<F, R>(
    rap: &R,
    width: &TraceWidth,
    num_challenges_to_sample: &[usize],
    num_exposed_values_after_challenge: &[usize],
    rap_phase_seq_kind: RapPhaseSeqKind,
    max_constraint_degree: usize,
) -> SymbolicRapBuilder<F>
where
    F: Field,
    R: Rap<SymbolicRapBuilder<F>> + BaseAirWithPublicValues<F> + ?Sized,
{
    let mut builder = SymbolicRapBuilder::new(
        width,
        rap.num_public_values(),
        num_challenges_to_sample,
        num_exposed_values_after_challenge,
        rap_phase_seq_kind,
        max_constraint_degree,
    );
    Rap::eval(rap, &mut builder);
    builder
}

/// An `AirBuilder` for evaluating constraints symbolically, and recording them for later use.
#[derive(Debug)]
pub struct SymbolicRapBuilder<F> {
    preprocessed: RowMajorMatrix<SymbolicVariable<F>>,
    partitioned_main: Vec<RowMajorMatrix<SymbolicVariable<F>>>,
    after_challenge: Vec<RowMajorMatrix<SymbolicVariable<F>>>,
    public_values: Vec<SymbolicVariable<F>>,
    challenges: Vec<Vec<SymbolicVariable<F>>>,
    exposed_values_after_challenge: Vec<Vec<SymbolicVariable<F>>>,
    constraints: Vec<SymbolicExpression<F>>,
    interactions: Vec<SymbolicInteraction<F>>,
    max_constraint_degree: usize,
    rap_phase_seq_kind: RapPhaseSeqKind,
    trace_width: TraceWidth,

    /// Caching for FRI logup to avoid recomputation during keygen
    interaction_partitions: Option<Vec<Vec<usize>>>,
}

impl<F: Field> SymbolicRapBuilder<F> {
    /// - `num_challenges_to_sample`: for each challenge phase, how many challenges to sample
    /// - `num_exposed_values_after_challenge`: in each challenge phase, how many values to expose to verifier
    pub(crate) fn new(
        width: &TraceWidth,
        num_public_values: usize,
        num_challenges_to_sample: &[usize],
        num_exposed_values_after_challenge: &[usize],
        rap_phase_seq_kind: RapPhaseSeqKind,
        max_constraint_degree: usize,
    ) -> Self {
        let preprocessed_width = width.preprocessed.unwrap_or(0);
        let prep_values = [0, 1]
            .into_iter()
            .flat_map(|offset| {
                (0..width.preprocessed.unwrap_or(0))
                    .map(move |index| SymbolicVariable::new(Entry::Preprocessed { offset }, index))
            })
            .collect();
        let preprocessed = RowMajorMatrix::new(prep_values, preprocessed_width);

        let mut partitioned_main: Vec<_> = width
            .cached_mains
            .iter()
            .enumerate()
            .map(|(part_index, &width)| gen_main_trace(part_index, width))
            .collect();
        if width.common_main != 0 {
            partitioned_main.push(gen_main_trace(width.cached_mains.len(), width.common_main));
        }
        let after_challenge = Self::new_after_challenge(&width.after_challenge);

        let public_values = (0..num_public_values)
            .map(move |index| SymbolicVariable::new(Entry::Public, index))
            .collect();

        let challenges = Self::new_challenges(num_challenges_to_sample);

        let exposed_values_after_challenge =
            Self::new_exposed_values_after_challenge(num_exposed_values_after_challenge);

        Self {
            preprocessed,
            partitioned_main,
            after_challenge,
            public_values,
            challenges,
            exposed_values_after_challenge,
            constraints: vec![],
            interactions: vec![],
            max_constraint_degree,
            rap_phase_seq_kind,
            trace_width: width.clone(),
            interaction_partitions: None,
        }
    }

    pub fn constraints(self) -> SymbolicConstraints<F> {
        SymbolicConstraints {
            constraints: self.constraints,
            interactions: self.interactions,
        }
    }

    pub fn params(&self) -> StarkVerifyingParams {
        let width = self.width();
        let num_exposed_values_after_challenge = self.num_exposed_values_after_challenge();
        let num_challenges_to_sample = self.num_challenges_to_sample();
        StarkVerifyingParams {
            width,
            num_public_values: self.public_values.len(),
            num_exposed_values_after_challenge,
            num_challenges_to_sample,
        }
    }

    pub fn width(&self) -> TraceWidth {
        let mut ret = self.trace_width.clone();
        ret.after_challenge = self.after_challenge.iter().map(|m| m.width()).collect();
        ret
    }

    pub fn num_exposed_values_after_challenge(&self) -> Vec<usize> {
        self.exposed_values_after_challenge
            .iter()
            .map(|c| c.len())
            .collect()
    }

    pub fn num_challenges_to_sample(&self) -> Vec<usize> {
        self.challenges.iter().map(|c| c.len()).collect()
    }

    fn new_after_challenge(
        width_after_phase: &[usize],
    ) -> Vec<RowMajorMatrix<SymbolicVariable<F>>> {
        width_after_phase
            .iter()
            .map(|&width| {
                let mat_values = [0, 1]
                    .into_iter()
                    .flat_map(|offset| {
                        (0..width).map(move |index| {
                            SymbolicVariable::new(Entry::Permutation { offset }, index)
                        })
                    })
                    .collect_vec();
                RowMajorMatrix::new(mat_values, width)
            })
            .collect_vec()
    }

    fn new_challenges(num_challenges_to_sample: &[usize]) -> Vec<Vec<SymbolicVariable<F>>> {
        num_challenges_to_sample
            .iter()
            .map(|&num_challenges| {
                (0..num_challenges)
                    .map(|index| SymbolicVariable::new(Entry::Challenge, index))
                    .collect_vec()
            })
            .collect_vec()
    }

    fn new_exposed_values_after_challenge(
        num_exposed_values_after_challenge: &[usize],
    ) -> Vec<Vec<SymbolicVariable<F>>> {
        num_exposed_values_after_challenge
            .iter()
            .map(|&num| {
                (0..num)
                    .map(|index| SymbolicVariable::new(Entry::Exposed, index))
                    .collect_vec()
            })
            .collect_vec()
    }
}

impl<F: Field> AirBuilder for SymbolicRapBuilder<F> {
    type F = F;
    type Expr = SymbolicExpression<Self::F>;
    type Var = SymbolicVariable<Self::F>;
    type M = RowMajorMatrix<Self::Var>;

    /// It is difficult to horizontally concatenate matrices when the main trace is partitioned, so we disable this method in that case.
    fn main(&self) -> Self::M {
        if self.partitioned_main.len() == 1 {
            self.partitioned_main[0].clone()
        } else {
            panic!("Main trace is either empty or partitioned. This function should not be used.")
        }
    }

    fn is_first_row(&self) -> Self::Expr {
        SymbolicExpression::IsFirstRow
    }

    fn is_last_row(&self) -> Self::Expr {
        SymbolicExpression::IsLastRow
    }

    fn is_transition_window(&self, size: usize) -> Self::Expr {
        if size == 2 {
            SymbolicExpression::IsTransition
        } else {
            panic!("uni-stark only supports a window size of 2")
        }
    }

    fn assert_zero<I: Into<Self::Expr>>(&mut self, x: I) {
        self.constraints.push(x.into());
    }
}

impl<F: Field> PairBuilder for SymbolicRapBuilder<F> {
    fn preprocessed(&self) -> Self::M {
        self.preprocessed.clone()
    }
}

impl<F: Field> ExtensionBuilder for SymbolicRapBuilder<F> {
    type EF = F;
    type ExprEF = SymbolicExpression<F>;
    type VarEF = SymbolicVariable<F>;

    fn assert_zero_ext<I>(&mut self, x: I)
    where
        I: Into<Self::ExprEF>,
    {
        self.constraints.push(x.into());
    }
}

impl<F: Field> AirBuilderWithPublicValues for SymbolicRapBuilder<F> {
    type PublicVar = SymbolicVariable<F>;

    fn public_values(&self) -> &[Self::PublicVar] {
        &self.public_values
    }
}

impl<F: Field> PermutationAirBuilder for SymbolicRapBuilder<F> {
    type MP = RowMajorMatrix<Self::VarEF>;
    type RandomVar = SymbolicVariable<F>;

    fn permutation(&self) -> Self::MP {
        self.after_challenge
            .first()
            .expect("Challenge phase not supported")
            .clone()
    }

    fn permutation_randomness(&self) -> &[Self::RandomVar] {
        self.challenges
            .first()
            .map(|c| c.as_slice())
            .expect("Challenge phase not supported")
    }
}

impl<F: Field> PermutationAirBuilderWithExposedValues for SymbolicRapBuilder<F> {
    fn permutation_exposed_values(&self) -> &[Self::VarEF] {
        self.exposed_values_after_challenge
            .first()
            .map(|c| c.as_slice())
            .expect("Challenge phase not supported")
    }
}

impl<F: Field> InteractionBuilder for SymbolicRapBuilder<F> {
    fn push_interaction<E: Into<Self::Expr>>(
        &mut self,
        bus_index: BusIndex,
        fields: impl IntoIterator<Item = E>,
        count: impl Into<Self::Expr>,
        count_weight: u32,
    ) {
        let fields = fields.into_iter().map(|f| f.into()).collect();
        let count = count.into();
        self.interactions.push(Interaction {
            bus_index,
            message: fields,
            count,
            count_weight,
        });
    }

    fn num_interactions(&self) -> usize {
        self.interactions.len()
    }

    fn all_interactions(&self) -> &[Interaction<Self::Expr>] {
        &self.interactions
    }
}

impl<F: Field> InteractionPhaseAirBuilder for SymbolicRapBuilder<F> {
    fn finalize_interactions(&mut self) {
        let num_interactions = self.num_interactions();
        if num_interactions != 0 {
            assert!(
                self.after_challenge.is_empty(),
                "after_challenge width should be auto-populated by the InteractionBuilder"
            );
            assert!(self.challenges.is_empty());
            assert!(self.exposed_values_after_challenge.is_empty());

            if self.rap_phase_seq_kind == RapPhaseSeqKind::FriLogUp {
                let interaction_partitions =
                    find_interaction_chunks(&self.interactions, self.max_constraint_degree)
                        .interaction_partitions();
                let num_chunks = interaction_partitions.len();
                self.interaction_partitions.replace(interaction_partitions);
                let perm_width = num_chunks + 1;
                self.after_challenge = Self::new_after_challenge(&[perm_width]);
            }

            let phases_shapes = self.rap_phase_seq_kind.shape();
            let phase_shape = phases_shapes.first().unwrap();

            self.challenges = Self::new_challenges(&[phase_shape.num_challenges]);
            self.exposed_values_after_challenge =
                Self::new_exposed_values_after_challenge(&[phase_shape.num_exposed_values]);
        }
    }

    fn max_constraint_degree(&self) -> usize {
        self.max_constraint_degree
    }

    fn rap_phase_seq_kind(&self) -> RapPhaseSeqKind {
        self.rap_phase_seq_kind
    }

    fn symbolic_interactions(&self) -> Vec<SymbolicInteraction<F>> {
        self.interactions.clone()
    }
}

impl<F: Field> PartitionedAirBuilder for SymbolicRapBuilder<F> {
    fn cached_mains(&self) -> &[Self::M] {
        &self.partitioned_main[..self.trace_width.cached_mains.len()]
    }
    fn common_main(&self) -> &Self::M {
        assert_ne!(
            self.trace_width.common_main, 0,
            "AIR doesn't have a common main trace"
        );
        &self.partitioned_main[self.trace_width.cached_mains.len()]
    }
}

#[allow(dead_code)]
struct LocalOnlyChecker;

#[allow(dead_code)]
impl LocalOnlyChecker {
    fn check_var<F: Field>(var: SymbolicVariable<F>) -> bool {
        match var.entry {
            Entry::Preprocessed { offset } => offset == 0,
            Entry::Main { offset, .. } => offset == 0,
            Entry::Permutation { offset } => offset == 0,
            Entry::Public => true,
            Entry::Challenge => true,
            Entry::Exposed => true,
        }
    }

    fn check_expr<F: Field>(expr: &SymbolicExpression<F>) -> bool {
        match expr {
            SymbolicExpression::Variable(var) => Self::check_var(*var),
            SymbolicExpression::IsFirstRow => false,
            SymbolicExpression::IsLastRow => false,
            SymbolicExpression::IsTransition => false,
            SymbolicExpression::Constant(_) => true,
            SymbolicExpression::Add { x, y, .. } => Self::check_expr(x) && Self::check_expr(y),
            SymbolicExpression::Sub { x, y, .. } => Self::check_expr(x) && Self::check_expr(y),
            SymbolicExpression::Neg { x, .. } => Self::check_expr(x),
            SymbolicExpression::Mul { x, y, .. } => Self::check_expr(x) && Self::check_expr(y),
        }
    }
}

fn gen_main_trace<F: Field>(
    part_index: usize,
    width: usize,
) -> RowMajorMatrix<SymbolicVariable<F>> {
    let mat_values = [0, 1]
        .into_iter()
        .flat_map(|offset| {
            (0..width)
                .map(move |index| SymbolicVariable::new(Entry::Main { part_index, offset }, index))
        })
        .collect_vec();
    RowMajorMatrix::new(mat_values, width)
}
