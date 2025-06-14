// Copied from uni-stark/src/symbolic_variable.rs.

use core::{
    marker::PhantomData,
    ops::{Add, Mul, Sub},
};

use p3_field::Field;
use serde::{Deserialize, Serialize};

use super::symbolic_expression::SymbolicExpression;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[repr(C)]
pub enum Entry {
    Preprocessed {
        offset: usize,
    },
    /// Main may be partitioned
    Main {
        part_index: usize,
        offset: usize,
    },
    Permutation {
        offset: usize,
    },
    Public,
    Challenge,
    Exposed,
}

impl Entry {
    pub fn offset(&self) -> Option<usize> {
        match self {
            Entry::Preprocessed { offset } => Some(*offset),
            Entry::Main { offset, .. } => Some(*offset),
            Entry::Permutation { offset } => Some(*offset),
            Entry::Public => None,
            Entry::Challenge => None,
            Entry::Exposed => None,
        }
    }

    /// Advance the internal offset of the entry by the given `offset`.
    pub fn rotate(self, offset: usize) -> Self {
        match self {
            Entry::Preprocessed { offset: old_offset } => Entry::Preprocessed {
                offset: old_offset + offset,
            },
            Entry::Main {
                part_index,
                offset: old_offset,
            } => Entry::Main {
                part_index,
                offset: old_offset + offset,
            },
            Entry::Permutation { offset: old_offset } => Entry::Permutation {
                offset: old_offset + offset,
            },
            Entry::Public | Entry::Challenge | Entry::Exposed => self,
        }
    }

    pub fn next(self) -> Self {
        self.rotate(1)
    }
}

/// A variable within the evaluation window, i.e. a column in either the local or next row.
#[derive(Copy, Clone, Debug, Hash, Eq, PartialEq, Serialize, Deserialize)]
#[repr(C)]
pub struct SymbolicVariable<F> {
    pub entry: Entry,
    pub index: usize,
    pub(crate) _phantom: PhantomData<F>,
}

impl<F: Field> SymbolicVariable<F> {
    pub const fn new(entry: Entry, index: usize) -> Self {
        Self {
            entry,
            index,
            _phantom: PhantomData,
        }
    }

    pub const fn degree_multiple(&self) -> usize {
        match self.entry {
            Entry::Preprocessed { .. } | Entry::Main { .. } | Entry::Permutation { .. } => 1,
            Entry::Public | Entry::Challenge | Entry::Exposed => 0,
        }
    }

    pub fn rotate(self, offset: usize) -> Self {
        Self {
            entry: self.entry.rotate(offset),
            index: self.index,
            _phantom: PhantomData,
        }
    }

    pub fn next(self) -> Self {
        self.rotate(1)
    }
}

impl<F: Field> From<SymbolicVariable<F>> for SymbolicExpression<F> {
    fn from(value: SymbolicVariable<F>) -> Self {
        SymbolicExpression::Variable(value)
    }
}

impl<F: Field> Add for SymbolicVariable<F> {
    type Output = SymbolicExpression<F>;

    fn add(self, rhs: Self) -> Self::Output {
        SymbolicExpression::from(self) + SymbolicExpression::from(rhs)
    }
}

impl<F: Field> Add<F> for SymbolicVariable<F> {
    type Output = SymbolicExpression<F>;

    fn add(self, rhs: F) -> Self::Output {
        SymbolicExpression::from(self) + SymbolicExpression::from(rhs)
    }
}

impl<F: Field> Add<SymbolicExpression<F>> for SymbolicVariable<F> {
    type Output = SymbolicExpression<F>;

    fn add(self, rhs: SymbolicExpression<F>) -> Self::Output {
        SymbolicExpression::from(self) + rhs
    }
}

impl<F: Field> Add<SymbolicVariable<F>> for SymbolicExpression<F> {
    type Output = Self;

    fn add(self, rhs: SymbolicVariable<F>) -> Self::Output {
        self + Self::from(rhs)
    }
}

impl<F: Field> Sub for SymbolicVariable<F> {
    type Output = SymbolicExpression<F>;

    fn sub(self, rhs: Self) -> Self::Output {
        SymbolicExpression::from(self) - SymbolicExpression::from(rhs)
    }
}

impl<F: Field> Sub<F> for SymbolicVariable<F> {
    type Output = SymbolicExpression<F>;

    fn sub(self, rhs: F) -> Self::Output {
        SymbolicExpression::from(self) - SymbolicExpression::from(rhs)
    }
}

impl<F: Field> Sub<SymbolicExpression<F>> for SymbolicVariable<F> {
    type Output = SymbolicExpression<F>;

    fn sub(self, rhs: SymbolicExpression<F>) -> Self::Output {
        SymbolicExpression::from(self) - rhs
    }
}

impl<F: Field> Sub<SymbolicVariable<F>> for SymbolicExpression<F> {
    type Output = Self;

    fn sub(self, rhs: SymbolicVariable<F>) -> Self::Output {
        self - Self::from(rhs)
    }
}

impl<F: Field> Mul for SymbolicVariable<F> {
    type Output = SymbolicExpression<F>;

    fn mul(self, rhs: Self) -> Self::Output {
        SymbolicExpression::from(self) * SymbolicExpression::from(rhs)
    }
}

impl<F: Field> Mul<F> for SymbolicVariable<F> {
    type Output = SymbolicExpression<F>;

    fn mul(self, rhs: F) -> Self::Output {
        SymbolicExpression::from(self) * SymbolicExpression::from(rhs)
    }
}

impl<F: Field> Mul<SymbolicExpression<F>> for SymbolicVariable<F> {
    type Output = SymbolicExpression<F>;

    fn mul(self, rhs: SymbolicExpression<F>) -> Self::Output {
        SymbolicExpression::from(self) * rhs
    }
}

impl<F: Field> Mul<SymbolicVariable<F>> for SymbolicExpression<F> {
    type Output = Self;

    fn mul(self, rhs: SymbolicVariable<F>) -> Self::Output {
        self * Self::from(rhs)
    }
}
