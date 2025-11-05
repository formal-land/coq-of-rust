use std::sync::Arc;

use p3_field::Field;
use rustc_hash::FxHashMap;
use serde::{Deserialize, Serialize};

use super::SymbolicConstraints;
use crate::{
    air_builders::symbolic::{
        symbolic_expression::SymbolicExpression, symbolic_variable::SymbolicVariable,
    },
    interaction::{Interaction, SymbolicInteraction},
};

/// A node in symbolic expression DAG.
/// Basically replace `Arc`s in `SymbolicExpression` with node IDs.
/// Intended to be serializable and deserializable.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(bound(serialize = "F: Serialize", deserialize = "F: Deserialize<'de>"))]
#[repr(C)]
pub enum SymbolicExpressionNode<F> {
    Variable(SymbolicVariable<F>),
    IsFirstRow,
    IsLastRow,
    IsTransition,
    Constant(F),
    Add {
        left_idx: usize,
        right_idx: usize,
        degree_multiple: usize,
    },
    Sub {
        left_idx: usize,
        right_idx: usize,
        degree_multiple: usize,
    },
    Neg {
        idx: usize,
        degree_multiple: usize,
    },
    Mul {
        left_idx: usize,
        right_idx: usize,
        degree_multiple: usize,
    },
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(bound(serialize = "F: Serialize", deserialize = "F: Deserialize<'de>"))]
#[repr(C)]
pub struct SymbolicExpressionDag<F> {
    /// Nodes in **topological** order.
    pub nodes: Vec<SymbolicExpressionNode<F>>,
    /// Node indices of expressions to assert equal zero.
    pub constraint_idx: Vec<usize>,
}

impl<F> SymbolicExpressionDag<F> {
    pub fn max_rotation(&self) -> usize {
        let mut rotation = 0;
        for node in &self.nodes {
            if let SymbolicExpressionNode::Variable(var) = node {
                rotation = rotation.max(var.entry.offset().unwrap_or(0));
            }
        }
        rotation
    }

    pub fn num_constraints(&self) -> usize {
        self.constraint_idx.len()
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound(serialize = "F: Serialize", deserialize = "F: Deserialize<'de>"))]
#[repr(C)]
pub struct SymbolicConstraintsDag<F> {
    /// DAG with all symbolic expressions as nodes.
    /// A subset of the nodes represents all constraints that will be
    /// included in the quotient polynomial via DEEP-ALI.
    pub constraints: SymbolicExpressionDag<F>,
    /// List of all interactions, where expressions in the interactions
    /// are referenced by node idx as `usize`.
    ///
    /// This is used by the prover for after challenge trace generation,
    /// and some partial information may be used by the verifier.
    ///
    /// **However**, any contributions to the quotient polynomial from
    /// logup are already included in `constraints` and do not need to
    /// be separately calculated from `interactions`.
    pub interactions: Vec<Interaction<usize>>,
}

pub(crate) fn build_symbolic_constraints_dag<F: Field>(
    constraints: &[SymbolicExpression<F>],
    interactions: &[SymbolicInteraction<F>],
) -> SymbolicConstraintsDag<F> {
    let mut expr_to_idx = FxHashMap::default();
    let mut nodes = Vec::new();
    let mut constraint_idx: Vec<usize> = constraints
        .iter()
        .map(|expr| topological_sort_symbolic_expr(expr, &mut expr_to_idx, &mut nodes))
        .collect();
    constraint_idx.sort();
    let interactions: Vec<Interaction<usize>> = interactions
        .iter()
        .map(|interaction| {
            let fields: Vec<usize> = interaction
                .message
                .iter()
                .map(|field_expr| {
                    topological_sort_symbolic_expr(field_expr, &mut expr_to_idx, &mut nodes)
                })
                .collect();
            let count =
                topological_sort_symbolic_expr(&interaction.count, &mut expr_to_idx, &mut nodes);
            Interaction {
                message: fields,
                count,
                bus_index: interaction.bus_index,
                count_weight: interaction.count_weight,
            }
        })
        .collect();
    // Note[jpw]: there could be few nodes created after `constraint_idx` is built
    // from `interactions` even though constraints already contain all interactions.
    // This should be marginal and is not optimized for now.
    let constraints = SymbolicExpressionDag {
        nodes,
        constraint_idx,
    };
    SymbolicConstraintsDag {
        constraints,
        interactions,
    }
}

/// `expr_to_idx` is a cache so that the `Arc<_>` references within symbolic expressions get
/// mapped to the same node ID if their underlying references are the same.
fn topological_sort_symbolic_expr<'a, F: Field>(
    expr: &'a SymbolicExpression<F>,
    expr_to_idx: &mut FxHashMap<&'a SymbolicExpression<F>, usize>,
    nodes: &mut Vec<SymbolicExpressionNode<F>>,
) -> usize {
    if let Some(&idx) = expr_to_idx.get(expr) {
        return idx;
    }
    let node = match expr {
        SymbolicExpression::Variable(var) => SymbolicExpressionNode::Variable(*var),
        SymbolicExpression::IsFirstRow => SymbolicExpressionNode::IsFirstRow,
        SymbolicExpression::IsLastRow => SymbolicExpressionNode::IsLastRow,
        SymbolicExpression::IsTransition => SymbolicExpressionNode::IsTransition,
        SymbolicExpression::Constant(cons) => SymbolicExpressionNode::Constant(*cons),
        SymbolicExpression::Add {
            x,
            y,
            degree_multiple,
        } => {
            let left_idx = topological_sort_symbolic_expr(x.as_ref(), expr_to_idx, nodes);
            let right_idx = topological_sort_symbolic_expr(y.as_ref(), expr_to_idx, nodes);
            SymbolicExpressionNode::Add {
                left_idx,
                right_idx,
                degree_multiple: *degree_multiple,
            }
        }
        SymbolicExpression::Sub {
            x,
            y,
            degree_multiple,
        } => {
            let left_idx = topological_sort_symbolic_expr(x.as_ref(), expr_to_idx, nodes);
            let right_idx = topological_sort_symbolic_expr(y.as_ref(), expr_to_idx, nodes);
            SymbolicExpressionNode::Sub {
                left_idx,
                right_idx,
                degree_multiple: *degree_multiple,
            }
        }
        SymbolicExpression::Neg { x, degree_multiple } => {
            let idx = topological_sort_symbolic_expr(x.as_ref(), expr_to_idx, nodes);
            SymbolicExpressionNode::Neg {
                idx,
                degree_multiple: *degree_multiple,
            }
        }
        SymbolicExpression::Mul {
            x,
            y,
            degree_multiple,
        } => {
            // An important case to remember: square will have Arc::as_ptr(&x) == Arc::as_ptr(&y)
            // The `expr_to_id` will ensure only one topological sort is done to prevent exponential
            // behavior.
            let left_idx = topological_sort_symbolic_expr(x.as_ref(), expr_to_idx, nodes);
            let right_idx = topological_sort_symbolic_expr(y.as_ref(), expr_to_idx, nodes);
            SymbolicExpressionNode::Mul {
                left_idx,
                right_idx,
                degree_multiple: *degree_multiple,
            }
        }
    };

    let idx = nodes.len();
    nodes.push(node);
    expr_to_idx.insert(expr, idx);
    idx
}

impl<F: Field> SymbolicExpressionDag<F> {
    /// Convert each node to a [`SymbolicExpression<F>`] reference and return
    /// the full list.
    fn to_symbolic_expressions(&self) -> Vec<Arc<SymbolicExpression<F>>> {
        let mut exprs: Vec<Arc<SymbolicExpression<_>>> = Vec::with_capacity(self.nodes.len());
        for node in &self.nodes {
            let expr = match *node {
                SymbolicExpressionNode::Variable(var) => SymbolicExpression::Variable(var),
                SymbolicExpressionNode::IsFirstRow => SymbolicExpression::IsFirstRow,
                SymbolicExpressionNode::IsLastRow => SymbolicExpression::IsLastRow,
                SymbolicExpressionNode::IsTransition => SymbolicExpression::IsTransition,
                SymbolicExpressionNode::Constant(f) => SymbolicExpression::Constant(f),
                SymbolicExpressionNode::Add {
                    left_idx,
                    right_idx,
                    degree_multiple,
                } => SymbolicExpression::Add {
                    x: exprs[left_idx].clone(),
                    y: exprs[right_idx].clone(),
                    degree_multiple,
                },
                SymbolicExpressionNode::Sub {
                    left_idx,
                    right_idx,
                    degree_multiple,
                } => SymbolicExpression::Sub {
                    x: exprs[left_idx].clone(),
                    y: exprs[right_idx].clone(),
                    degree_multiple,
                },
                SymbolicExpressionNode::Neg {
                    idx,
                    degree_multiple,
                } => SymbolicExpression::Neg {
                    x: exprs[idx].clone(),
                    degree_multiple,
                },
                SymbolicExpressionNode::Mul {
                    left_idx,
                    right_idx,
                    degree_multiple,
                } => SymbolicExpression::Mul {
                    x: exprs[left_idx].clone(),
                    y: exprs[right_idx].clone(),
                    degree_multiple,
                },
            };
            exprs.push(Arc::new(expr));
        }
        exprs
    }
}

// TEMPORARY conversions until we switch main interfaces to use SymbolicConstraintsDag
impl<'a, F: Field> From<&'a SymbolicConstraintsDag<F>> for SymbolicConstraints<F> {
    fn from(dag: &'a SymbolicConstraintsDag<F>) -> Self {
        let exprs = dag.constraints.to_symbolic_expressions();
        let constraints = dag
            .constraints
            .constraint_idx
            .iter()
            .map(|&idx| exprs[idx].as_ref().clone())
            .collect::<Vec<_>>();
        let interactions = dag
            .interactions
            .iter()
            .map(|interaction| {
                let fields = interaction
                    .message
                    .iter()
                    .map(|&idx| exprs[idx].as_ref().clone())
                    .collect();
                let count = exprs[interaction.count].as_ref().clone();
                Interaction {
                    message: fields,
                    count,
                    bus_index: interaction.bus_index,
                    count_weight: interaction.count_weight,
                }
            })
            .collect::<Vec<_>>();
        SymbolicConstraints {
            constraints,
            interactions,
        }
    }
}

impl<F: Field> From<SymbolicConstraintsDag<F>> for SymbolicConstraints<F> {
    fn from(dag: SymbolicConstraintsDag<F>) -> Self {
        (&dag).into()
    }
}

impl<F: Field> From<SymbolicConstraints<F>> for SymbolicConstraintsDag<F> {
    fn from(sc: SymbolicConstraints<F>) -> Self {
        build_symbolic_constraints_dag(&sc.constraints, &sc.interactions)
    }
}

#[cfg(test)]
mod tests {
    use p3_baby_bear::BabyBear;
    use p3_field::FieldAlgebra;

    use crate::{
        air_builders::symbolic::{
            dag::{build_symbolic_constraints_dag, SymbolicExpressionDag, SymbolicExpressionNode},
            symbolic_expression::SymbolicExpression,
            symbolic_variable::{Entry, SymbolicVariable},
        },
        interaction::Interaction,
    };

    type F = BabyBear;

    #[test]
    fn test_symbolic_constraints_dag() {
        let expr = SymbolicExpression::Constant(F::ONE)
            * SymbolicVariable::new(
                Entry::Main {
                    part_index: 1,
                    offset: 2,
                },
                3,
            );
        let constraints = vec![
            SymbolicExpression::IsFirstRow * SymbolicExpression::IsLastRow
                + SymbolicExpression::Constant(F::ONE)
                + SymbolicExpression::IsFirstRow * SymbolicExpression::IsLastRow
                + expr.clone(),
            expr.clone() * expr.clone(),
        ];
        let interactions = vec![Interaction {
            bus_index: 0,
            message: vec![expr.clone(), SymbolicExpression::Constant(F::TWO)],
            count: SymbolicExpression::Constant(F::ONE),
            count_weight: 1,
        }];
        let dag = build_symbolic_constraints_dag(&constraints, &interactions);
        assert_eq!(
            dag.constraints,
            SymbolicExpressionDag::<F> {
                nodes: vec![
                    SymbolicExpressionNode::IsFirstRow,
                    SymbolicExpressionNode::IsLastRow,
                    SymbolicExpressionNode::Mul {
                        left_idx: 0,
                        right_idx: 1,
                        degree_multiple: 2
                    },
                    SymbolicExpressionNode::Constant(F::ONE),
                    SymbolicExpressionNode::Add {
                        left_idx: 2,
                        right_idx: 3,
                        degree_multiple: 2
                    },
                    // Currently topological sort does not detect all subgraph isomorphisms. For example each IsFirstRow and IsLastRow is a new reference so ptr::hash is distinct.
                    SymbolicExpressionNode::Mul {
                        left_idx: 0,
                        right_idx: 1,
                        degree_multiple: 2
                    },
                    SymbolicExpressionNode::Add {
                        left_idx: 4,
                        right_idx: 5,
                        degree_multiple: 2
                    },
                    SymbolicExpressionNode::Variable(SymbolicVariable::new(
                        Entry::Main {
                            part_index: 1,
                            offset: 2
                        },
                        3
                    )),
                    SymbolicExpressionNode::Mul {
                        left_idx: 3,
                        right_idx: 7,
                        degree_multiple: 1
                    },
                    SymbolicExpressionNode::Add {
                        left_idx: 6,
                        right_idx: 8,
                        degree_multiple: 2
                    },
                    SymbolicExpressionNode::Mul {
                        left_idx: 8,
                        right_idx: 8,
                        degree_multiple: 2
                    },
                    SymbolicExpressionNode::Constant(F::TWO),
                ],
                constraint_idx: vec![9, 10],
            }
        );
        assert_eq!(
            dag.interactions,
            vec![Interaction {
                bus_index: 0,
                message: vec![8, 11],
                count: 3,
                count_weight: 1,
            }]
        );
    }
}
