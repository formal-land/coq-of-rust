// Copied from uni-stark/src/symbolic_expression.rs to use Arc instead of Rc.

use core::{
    fmt::Debug,
    iter::{Product, Sum},
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};
use std::{
    hash::{Hash, Hasher},
    ptr,
    sync::Arc,
};

use p3_field::{Field, FieldAlgebra};
use serde::{Deserialize, Serialize};

use super::{dag::SymbolicExpressionNode, symbolic_variable::SymbolicVariable};

/// An expression over `SymbolicVariable`s.
// Note: avoid deriving Hash because it will hash the entire sub-tree
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(bound = "F: Field")]
pub enum SymbolicExpression<F> {
    Variable(SymbolicVariable<F>),
    IsFirstRow,
    IsLastRow,
    IsTransition,
    Constant(F),
    Add {
        x: Arc<Self>,
        y: Arc<Self>,
        degree_multiple: usize,
    },
    Sub {
        x: Arc<Self>,
        y: Arc<Self>,
        degree_multiple: usize,
    },
    Neg {
        x: Arc<Self>,
        degree_multiple: usize,
    },
    Mul {
        x: Arc<Self>,
        y: Arc<Self>,
        degree_multiple: usize,
    },
}

impl<F: Field> Hash for SymbolicExpression<F> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // First hash the discriminant of the enum
        std::mem::discriminant(self).hash(state);
        // Degree multiple is not necessary
        match self {
            Self::Variable(v) => v.hash(state),
            Self::IsFirstRow => {}   // discriminant is enough
            Self::IsLastRow => {}    // discriminant is enough
            Self::IsTransition => {} // discriminant is enough
            Self::Constant(f) => f.hash(state),
            Self::Add { x, y, .. } => {
                ptr::hash(&**x, state);
                ptr::hash(&**y, state);
            }
            Self::Sub { x, y, .. } => {
                ptr::hash(&**x, state);
                ptr::hash(&**y, state);
            }
            Self::Neg { x, .. } => {
                ptr::hash(&**x, state);
            }
            Self::Mul { x, y, .. } => {
                ptr::hash(&**x, state);
                ptr::hash(&**y, state);
            }
        }
    }
}

// We intentionally do not compare degree_multiple in PartialEq and Eq because degree_multiple is
// metadata used for optimization/debugging purposes but it does not change the underlying expression.
impl<F: Field> PartialEq for SymbolicExpression<F> {
    fn eq(&self, other: &Self) -> bool {
        // First check if the variants match
        if std::mem::discriminant(self) != std::mem::discriminant(other) {
            return false;
        }

        // Then check equality based on variant-specific data
        match (self, other) {
            (Self::Variable(v1), Self::Variable(v2)) => v1 == v2,
            // IsFirstRow, IsLastRow, and IsTransition are all unit variants,
            // so if the discriminants match, they're equal
            (Self::IsFirstRow, Self::IsFirstRow) => true,
            (Self::IsLastRow, Self::IsLastRow) => true,
            (Self::IsTransition, Self::IsTransition) => true,
            (Self::Constant(c1), Self::Constant(c2)) => c1 == c2,
            // For compound expressions, compare pointers to match how Hash is implemented
            (Self::Add { x: x1, y: y1, .. }, Self::Add { x: x2, y: y2, .. }) => {
                Arc::ptr_eq(x1, x2) && Arc::ptr_eq(y1, y2)
            }
            (Self::Sub { x: x1, y: y1, .. }, Self::Sub { x: x2, y: y2, .. }) => {
                Arc::ptr_eq(x1, x2) && Arc::ptr_eq(y1, y2)
            }
            (Self::Neg { x: x1, .. }, Self::Neg { x: x2, .. }) => Arc::ptr_eq(x1, x2),
            (Self::Mul { x: x1, y: y1, .. }, Self::Mul { x: x2, y: y2, .. }) => {
                Arc::ptr_eq(x1, x2) && Arc::ptr_eq(y1, y2)
            }
            // This should never be reached because we've already checked the discriminants
            _ => false,
        }
    }
}

impl<F: Field> Eq for SymbolicExpression<F> {}

impl<F: Field> SymbolicExpression<F> {
    /// Returns the multiple of `n` (the trace length) in this expression's degree.
    pub const fn degree_multiple(&self) -> usize {
        match self {
            SymbolicExpression::Variable(v) => v.degree_multiple(),
            SymbolicExpression::IsFirstRow => 1,
            SymbolicExpression::IsLastRow => 1,
            SymbolicExpression::IsTransition => 0,
            SymbolicExpression::Constant(_) => 0,
            SymbolicExpression::Add {
                degree_multiple, ..
            } => *degree_multiple,
            SymbolicExpression::Sub {
                degree_multiple, ..
            } => *degree_multiple,
            SymbolicExpression::Neg {
                degree_multiple, ..
            } => *degree_multiple,
            SymbolicExpression::Mul {
                degree_multiple, ..
            } => *degree_multiple,
        }
    }
}

impl<F: Field> Default for SymbolicExpression<F> {
    fn default() -> Self {
        Self::Constant(F::ZERO)
    }
}

impl<F: Field> From<F> for SymbolicExpression<F> {
    fn from(value: F) -> Self {
        Self::Constant(value)
    }
}

impl<F: Field> FieldAlgebra for SymbolicExpression<F> {
    type F = F;

    const ZERO: Self = Self::Constant(F::ZERO);
    const ONE: Self = Self::Constant(F::ONE);
    const TWO: Self = Self::Constant(F::TWO);
    const NEG_ONE: Self = Self::Constant(F::NEG_ONE);

    #[inline]
    fn from_f(f: Self::F) -> Self {
        f.into()
    }

    fn from_bool(b: bool) -> Self {
        Self::Constant(F::from_bool(b))
    }

    fn from_canonical_u8(n: u8) -> Self {
        Self::Constant(F::from_canonical_u8(n))
    }

    fn from_canonical_u16(n: u16) -> Self {
        Self::Constant(F::from_canonical_u16(n))
    }

    fn from_canonical_u32(n: u32) -> Self {
        Self::Constant(F::from_canonical_u32(n))
    }

    fn from_canonical_u64(n: u64) -> Self {
        Self::Constant(F::from_canonical_u64(n))
    }

    fn from_canonical_usize(n: usize) -> Self {
        Self::Constant(F::from_canonical_usize(n))
    }

    fn from_wrapped_u32(n: u32) -> Self {
        Self::Constant(F::from_wrapped_u32(n))
    }

    fn from_wrapped_u64(n: u64) -> Self {
        Self::Constant(F::from_wrapped_u64(n))
    }
}

impl<F: Field> Add for SymbolicExpression<F> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        let degree_multiple = self.degree_multiple().max(rhs.degree_multiple());
        Self::Add {
            x: Arc::new(self),
            y: Arc::new(rhs),
            degree_multiple,
        }
    }
}

impl<F: Field> Add<F> for SymbolicExpression<F> {
    type Output = Self;

    fn add(self, rhs: F) -> Self {
        self + Self::from(rhs)
    }
}

impl<F: Field> AddAssign for SymbolicExpression<F> {
    fn add_assign(&mut self, rhs: Self) {
        *self = self.clone() + rhs;
    }
}

impl<F: Field> AddAssign<F> for SymbolicExpression<F> {
    fn add_assign(&mut self, rhs: F) {
        *self += Self::from(rhs);
    }
}

impl<F: Field> Sum for SymbolicExpression<F> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|x, y| x + y).unwrap_or(Self::ZERO)
    }
}

impl<F: Field> Sum<F> for SymbolicExpression<F> {
    fn sum<I: Iterator<Item = F>>(iter: I) -> Self {
        iter.map(|x| Self::from(x)).sum()
    }
}

impl<F: Field> Sub for SymbolicExpression<F> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        let degree_multiple = self.degree_multiple().max(rhs.degree_multiple());
        Self::Sub {
            x: Arc::new(self),
            y: Arc::new(rhs),
            degree_multiple,
        }
    }
}

impl<F: Field> Sub<F> for SymbolicExpression<F> {
    type Output = Self;

    fn sub(self, rhs: F) -> Self {
        self - Self::from(rhs)
    }
}

impl<F: Field> SubAssign for SymbolicExpression<F> {
    fn sub_assign(&mut self, rhs: Self) {
        *self = self.clone() - rhs;
    }
}

impl<F: Field> SubAssign<F> for SymbolicExpression<F> {
    fn sub_assign(&mut self, rhs: F) {
        *self -= Self::from(rhs);
    }
}

impl<F: Field> Neg for SymbolicExpression<F> {
    type Output = Self;

    fn neg(self) -> Self {
        let degree_multiple = self.degree_multiple();
        Self::Neg {
            x: Arc::new(self),
            degree_multiple,
        }
    }
}

impl<F: Field> Mul for SymbolicExpression<F> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self {
        #[allow(clippy::suspicious_arithmetic_impl)]
        let degree_multiple = self.degree_multiple() + rhs.degree_multiple();
        Self::Mul {
            x: Arc::new(self),
            y: Arc::new(rhs),
            degree_multiple,
        }
    }
}

impl<F: Field> Mul<F> for SymbolicExpression<F> {
    type Output = Self;

    fn mul(self, rhs: F) -> Self {
        self * Self::from(rhs)
    }
}

impl<F: Field> MulAssign for SymbolicExpression<F> {
    fn mul_assign(&mut self, rhs: Self) {
        *self = self.clone() * rhs;
    }
}

impl<F: Field> MulAssign<F> for SymbolicExpression<F> {
    fn mul_assign(&mut self, rhs: F) {
        *self *= Self::from(rhs);
    }
}

impl<F: Field> Product for SymbolicExpression<F> {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|x, y| x * y).unwrap_or(Self::ONE)
    }
}

impl<F: Field> Product<F> for SymbolicExpression<F> {
    fn product<I: Iterator<Item = F>>(iter: I) -> Self {
        iter.map(|x| Self::from(x)).product()
    }
}

pub trait SymbolicEvaluator<F, E>
where
    F: Field,
    E: Add<E, Output = E> + Sub<E, Output = E> + Mul<E, Output = E> + Neg<Output = E>,
{
    fn eval_const(&self, c: F) -> E;
    fn eval_var(&self, symbolic_var: SymbolicVariable<F>) -> E;
    fn eval_is_first_row(&self) -> E;
    fn eval_is_last_row(&self) -> E;
    fn eval_is_transition(&self) -> E;

    fn eval_expr(&self, symbolic_expr: &SymbolicExpression<F>) -> E {
        match symbolic_expr {
            SymbolicExpression::Variable(var) => self.eval_var(*var),
            SymbolicExpression::Constant(c) => self.eval_const(*c),
            SymbolicExpression::Add { x, y, .. } => self.eval_expr(x) + self.eval_expr(y),
            SymbolicExpression::Sub { x, y, .. } => self.eval_expr(x) - self.eval_expr(y),
            SymbolicExpression::Neg { x, .. } => -self.eval_expr(x),
            SymbolicExpression::Mul { x, y, .. } => self.eval_expr(x) * self.eval_expr(y),
            SymbolicExpression::IsFirstRow => self.eval_is_first_row(),
            SymbolicExpression::IsLastRow => self.eval_is_last_row(),
            SymbolicExpression::IsTransition => self.eval_is_transition(),
        }
    }

    /// Assumes that `nodes` are in topological order (if B references A, then B comes after A).
    /// Simple serial evaluation in order.
    fn eval_nodes(&self, nodes: &[SymbolicExpressionNode<F>]) -> Vec<E>
    where
        E: Clone,
    {
        let mut exprs: Vec<E> = Vec::with_capacity(nodes.len());
        for node in nodes {
            let expr = match *node {
                SymbolicExpressionNode::Variable(var) => self.eval_var(var),
                SymbolicExpressionNode::Constant(c) => self.eval_const(c),
                SymbolicExpressionNode::Add {
                    left_idx,
                    right_idx,
                    ..
                } => exprs[left_idx].clone() + exprs[right_idx].clone(),
                SymbolicExpressionNode::Sub {
                    left_idx,
                    right_idx,
                    ..
                } => exprs[left_idx].clone() - exprs[right_idx].clone(),
                SymbolicExpressionNode::Neg { idx, .. } => -exprs[idx].clone(),
                SymbolicExpressionNode::Mul {
                    left_idx,
                    right_idx,
                    ..
                } => exprs[left_idx].clone() * exprs[right_idx].clone(),
                SymbolicExpressionNode::IsFirstRow => self.eval_is_first_row(),
                SymbolicExpressionNode::IsLastRow => self.eval_is_last_row(),
                SymbolicExpressionNode::IsTransition => self.eval_is_transition(),
            };
            exprs.push(expr);
        }
        exprs
    }
}
