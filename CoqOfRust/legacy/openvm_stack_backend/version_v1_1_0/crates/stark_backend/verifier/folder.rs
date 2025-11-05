use std::{
    marker::PhantomData,
    ops::{AddAssign, MulAssign},
};

use p3_field::{ExtensionField, Field, FieldAlgebra};
use p3_matrix::Matrix;

use crate::{
    air_builders::{
        symbolic::{
            symbolic_expression::SymbolicEvaluator,
            symbolic_variable::{Entry, SymbolicVariable},
            SymbolicExpressionDag,
        },
        ViewPair,
    },
    config::{StarkGenericConfig, Val},
};

pub type VerifierConstraintFolder<'a, SC> = GenericVerifierConstraintFolder<
    'a,
    Val<SC>,
    <SC as StarkGenericConfig>::Challenge,
    Val<SC>,
    <SC as StarkGenericConfig>::Challenge,
    <SC as StarkGenericConfig>::Challenge,
>;
// Struct definition copied from sp1 under MIT license.
/// A folder for verifier constraints with generic types.
///
/// `Var` is still a challenge type because this is a verifier.
pub struct GenericVerifierConstraintFolder<'a, F, EF, PubVar, Var, Expr> {
    pub preprocessed: ViewPair<'a, Var>,
    pub partitioned_main: Vec<ViewPair<'a, Var>>,
    pub after_challenge: Vec<ViewPair<'a, Var>>,
    pub challenges: &'a [Vec<Var>],
    pub is_first_row: Var,
    pub is_last_row: Var,
    pub is_transition: Var,
    pub alpha: Var,
    pub accumulator: Expr,
    pub public_values: &'a [PubVar],
    pub exposed_values_after_challenge: &'a [Vec<Var>],
    pub _marker: PhantomData<(F, EF)>,
}

impl<F, EF, PubVar, Var, Expr> GenericVerifierConstraintFolder<'_, F, EF, PubVar, Var, Expr>
where
    F: Field,
    EF: ExtensionField<F>,
    Expr: FieldAlgebra + From<F> + MulAssign<Var> + AddAssign<Var> + Send + Sync,
    Var: Into<Expr> + Copy + Send + Sync,
    PubVar: Into<Expr> + Copy + Send + Sync,
{
    pub fn eval_constraints(&mut self, constraints: &SymbolicExpressionDag<F>) {
        let dag = constraints;
        // node_idx -> evaluation
        // We do a simple serial evaluation in topological order.
        // This can be parallelized if necessary.
        let exprs = self.eval_nodes(&dag.nodes);
        for &idx in &dag.constraint_idx {
            self.assert_zero(exprs[idx].clone());
        }
    }

    pub fn assert_zero(&mut self, x: impl Into<Expr>) {
        let x = x.into();
        self.accumulator *= self.alpha;
        self.accumulator += x;
    }
}

impl<F, EF, PubVar, Var, Expr> SymbolicEvaluator<F, Expr>
    for GenericVerifierConstraintFolder<'_, F, EF, PubVar, Var, Expr>
where
    F: Field,
    EF: ExtensionField<F>,
    Expr: FieldAlgebra + From<F> + Send + Sync,
    Var: Into<Expr> + Copy + Send + Sync,
    PubVar: Into<Expr> + Copy + Send + Sync,
{
    fn eval_const(&self, c: F) -> Expr {
        c.into()
    }
    fn eval_is_first_row(&self) -> Expr {
        self.is_first_row.into()
    }
    fn eval_is_last_row(&self) -> Expr {
        self.is_last_row.into()
    }
    fn eval_is_transition(&self) -> Expr {
        self.is_transition.into()
    }
    fn eval_var(&self, symbolic_var: SymbolicVariable<F>) -> Expr {
        let index = symbolic_var.index;
        match symbolic_var.entry {
            Entry::Preprocessed { offset } => self.preprocessed.get(offset, index).into(),
            Entry::Main { part_index, offset } => {
                self.partitioned_main[part_index].get(offset, index).into()
            }
            Entry::Public => self.public_values[index].into(),
            Entry::Permutation { offset } => self
                .after_challenge
                .first()
                .expect("Challenge phase not supported")
                .get(offset, index)
                .into(),
            Entry::Challenge => self
                .challenges
                .first()
                .expect("Challenge phase not supported")[index]
                .into(),
            Entry::Exposed => self
                .exposed_values_after_challenge
                .first()
                .expect("Challenge phase not supported")[index]
                .into(),
        }
    }
    // NOTE: do not use the eval_expr function as it can have exponential complexity!
    // Instead use `eval_nodes`
}
