use alloc::rc::Rc;
use core::fmt::Debug;
use core::iter::{Product, Sum};
use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use p3_field::{Algebra, Field, InjectiveMonomial, PrimeCharacteristicRing};

use crate::symbolic_variable::SymbolicVariable;

/// An expression over `SymbolicVariable`s.
#[derive(Clone, Debug)]
pub enum SymbolicExpression<F> {
    Variable(SymbolicVariable<F>),
    IsFirstRow,
    IsLastRow,
    IsTransition,
    Constant(F),
    Add {
        x: Rc<Self>,
        y: Rc<Self>,
        degree_multiple: usize,
    },
    Sub {
        x: Rc<Self>,
        y: Rc<Self>,
        degree_multiple: usize,
    },
    Neg {
        x: Rc<Self>,
        degree_multiple: usize,
    },
    Mul {
        x: Rc<Self>,
        y: Rc<Self>,
        degree_multiple: usize,
    },
}

impl<F> SymbolicExpression<F> {
    /// Returns the multiple of `n` (the trace length) in this expression's degree.
    pub const fn degree_multiple(&self) -> usize {
        match self {
            Self::Variable(v) => v.degree_multiple(),
            Self::IsFirstRow | Self::IsLastRow => 1,
            Self::IsTransition | Self::Constant(_) => 0,
            Self::Add {
                degree_multiple, ..
            }
            | Self::Sub {
                degree_multiple, ..
            }
            | Self::Neg {
                degree_multiple, ..
            }
            | Self::Mul {
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

impl<F: Field> PrimeCharacteristicRing for SymbolicExpression<F> {
    type PrimeSubfield = F::PrimeSubfield;

    const ZERO: Self = Self::Constant(F::ZERO);
    const ONE: Self = Self::Constant(F::ONE);
    const TWO: Self = Self::Constant(F::TWO);
    const NEG_ONE: Self = Self::Constant(F::NEG_ONE);

    #[inline]
    fn from_prime_subfield(f: Self::PrimeSubfield) -> Self {
        F::from_prime_subfield(f).into()
    }
}

impl<F: Field> Algebra<F> for SymbolicExpression<F> {}

impl<F: Field> Algebra<SymbolicVariable<F>> for SymbolicExpression<F> {}

// Note we cannot implement PermutationMonomial due to the degree_multiple part which makes
// operations non invertible.
impl<F: Field + InjectiveMonomial<N>, const N: u64> InjectiveMonomial<N> for SymbolicExpression<F> {}

impl<F: Field, T> Add<T> for SymbolicExpression<F>
where
    T: Into<Self>,
{
    type Output = Self;

    fn add(self, rhs: T) -> Self {
        match (self, rhs.into()) {
            (Self::Constant(lhs), Self::Constant(rhs)) => Self::Constant(lhs + rhs),
            (lhs, rhs) => Self::Add {
                degree_multiple: lhs.degree_multiple().max(rhs.degree_multiple()),
                x: Rc::new(lhs),
                y: Rc::new(rhs),
            },
        }
    }
}

impl<F: Field, T> AddAssign<T> for SymbolicExpression<F>
where
    T: Into<Self>,
{
    fn add_assign(&mut self, rhs: T) {
        *self = self.clone() + rhs.into();
    }
}

impl<F: Field, T> Sum<T> for SymbolicExpression<F>
where
    T: Into<Self>,
{
    fn sum<I: Iterator<Item = T>>(iter: I) -> Self {
        iter.map(Into::into)
            .reduce(|x, y| x + y)
            .unwrap_or(Self::ZERO)
    }
}

impl<F: Field, T: Into<Self>> Sub<T> for SymbolicExpression<F> {
    type Output = Self;

    fn sub(self, rhs: T) -> Self {
        match (self, rhs.into()) {
            (Self::Constant(lhs), Self::Constant(rhs)) => Self::Constant(lhs - rhs),
            (lhs, rhs) => Self::Sub {
                degree_multiple: lhs.degree_multiple().max(rhs.degree_multiple()),
                x: Rc::new(lhs),
                y: Rc::new(rhs),
            },
        }
    }
}

impl<F: Field, T> SubAssign<T> for SymbolicExpression<F>
where
    T: Into<Self>,
{
    fn sub_assign(&mut self, rhs: T) {
        *self = self.clone() - rhs.into();
    }
}

impl<F: Field> Neg for SymbolicExpression<F> {
    type Output = Self;

    fn neg(self) -> Self {
        match self {
            Self::Constant(c) => Self::Constant(-c),
            expr => Self::Neg {
                degree_multiple: expr.degree_multiple(),
                x: Rc::new(expr),
            },
        }
    }
}

impl<F: Field, T: Into<Self>> Mul<T> for SymbolicExpression<F> {
    type Output = Self;

    fn mul(self, rhs: T) -> Self {
        match (self, rhs.into()) {
            (Self::Constant(lhs), Self::Constant(rhs)) => Self::Constant(lhs * rhs),
            (lhs, rhs) => Self::Mul {
                degree_multiple: lhs.degree_multiple() + rhs.degree_multiple(),
                x: Rc::new(lhs),
                y: Rc::new(rhs),
            },
        }
    }
}

impl<F: Field, T> MulAssign<T> for SymbolicExpression<F>
where
    T: Into<Self>,
{
    fn mul_assign(&mut self, rhs: T) {
        *self = self.clone() * rhs.into();
    }
}

impl<F: Field, T: Into<Self>> Product<T> for SymbolicExpression<F> {
    fn product<I: Iterator<Item = T>>(iter: I) -> Self {
        iter.map(Into::into)
            .reduce(|x, y| x * y)
            .unwrap_or(Self::ONE)
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec;

    use p3_baby_bear::BabyBear;

    use super::*;
    use crate::Entry;

    #[test]
    fn test_symbolic_expression_degree_multiple() {
        let constant_expr = SymbolicExpression::<BabyBear>::Constant(BabyBear::new(5));
        assert_eq!(
            constant_expr.degree_multiple(),
            0,
            "Constant should have degree 0"
        );

        let variable_expr =
            SymbolicExpression::Variable(SymbolicVariable::new(Entry::Main { offset: 0 }, 1));
        assert_eq!(
            variable_expr.degree_multiple(),
            1,
            "Main variable should have degree 1"
        );

        let preprocessed_var = SymbolicExpression::Variable(SymbolicVariable::new(
            Entry::Preprocessed { offset: 0 },
            2,
        ));
        assert_eq!(
            preprocessed_var.degree_multiple(),
            1,
            "Preprocessed variable should have degree 1"
        );

        let permutation_var = SymbolicExpression::Variable(SymbolicVariable::<BabyBear>::new(
            Entry::Permutation { offset: 0 },
            3,
        ));
        assert_eq!(
            permutation_var.degree_multiple(),
            1,
            "Permutation variable should have degree 1"
        );

        let public_var =
            SymbolicExpression::Variable(SymbolicVariable::<BabyBear>::new(Entry::Public, 4));
        assert_eq!(
            public_var.degree_multiple(),
            0,
            "Public variable should have degree 0"
        );

        let challenge_var =
            SymbolicExpression::Variable(SymbolicVariable::<BabyBear>::new(Entry::Challenge, 5));
        assert_eq!(
            challenge_var.degree_multiple(),
            0,
            "Challenge variable should have degree 0"
        );

        let is_first_row = SymbolicExpression::<BabyBear>::IsFirstRow;
        assert_eq!(
            is_first_row.degree_multiple(),
            1,
            "IsFirstRow should have degree 1"
        );

        let is_last_row = SymbolicExpression::<BabyBear>::IsLastRow;
        assert_eq!(
            is_last_row.degree_multiple(),
            1,
            "IsLastRow should have degree 1"
        );

        let is_transition = SymbolicExpression::<BabyBear>::IsTransition;
        assert_eq!(
            is_transition.degree_multiple(),
            0,
            "IsTransition should have degree 0"
        );

        let add_expr = SymbolicExpression::<BabyBear>::Add {
            x: Rc::new(variable_expr.clone()),
            y: Rc::new(preprocessed_var.clone()),
            degree_multiple: 1,
        };
        assert_eq!(
            add_expr.degree_multiple(),
            1,
            "Addition should take max degree of inputs"
        );

        let sub_expr = SymbolicExpression::<BabyBear>::Sub {
            x: Rc::new(variable_expr.clone()),
            y: Rc::new(preprocessed_var.clone()),
            degree_multiple: 1,
        };
        assert_eq!(
            sub_expr.degree_multiple(),
            1,
            "Subtraction should take max degree of inputs"
        );

        let neg_expr = SymbolicExpression::<BabyBear>::Neg {
            x: Rc::new(variable_expr.clone()),
            degree_multiple: 1,
        };
        assert_eq!(
            neg_expr.degree_multiple(),
            1,
            "Negation should keep the degree"
        );

        let mul_expr = SymbolicExpression::<BabyBear>::Mul {
            x: Rc::new(variable_expr.clone()),
            y: Rc::new(preprocessed_var.clone()),
            degree_multiple: 2,
        };
        assert_eq!(
            mul_expr.degree_multiple(),
            2,
            "Multiplication should sum degrees"
        );
    }

    #[test]
    fn test_addition_of_constants() {
        let a = SymbolicExpression::Constant(BabyBear::new(3));
        let b = SymbolicExpression::Constant(BabyBear::new(4));
        let result = a + b;
        match result {
            SymbolicExpression::Constant(val) => assert_eq!(val, BabyBear::new(7)),
            _ => panic!("Addition of constants did not simplify correctly"),
        }
    }

    #[test]
    fn test_subtraction_of_constants() {
        let a = SymbolicExpression::Constant(BabyBear::new(10));
        let b = SymbolicExpression::Constant(BabyBear::new(4));
        let result = a - b;
        match result {
            SymbolicExpression::Constant(val) => assert_eq!(val, BabyBear::new(6)),
            _ => panic!("Subtraction of constants did not simplify correctly"),
        }
    }

    #[test]
    fn test_negation() {
        let a = SymbolicExpression::Constant(BabyBear::new(7));
        let result = -a;
        match result {
            SymbolicExpression::Constant(val) => {
                assert_eq!(val, BabyBear::NEG_ONE * BabyBear::new(7))
            }
            _ => panic!("Negation did not work correctly"),
        }
    }

    #[test]
    fn test_multiplication_of_constants() {
        let a = SymbolicExpression::Constant(BabyBear::new(3));
        let b = SymbolicExpression::Constant(BabyBear::new(5));
        let result = a * b;
        match result {
            SymbolicExpression::Constant(val) => assert_eq!(val, BabyBear::new(15)),
            _ => panic!("Multiplication of constants did not simplify correctly"),
        }
    }

    #[test]
    fn test_degree_multiple_for_addition() {
        let a = SymbolicExpression::Variable::<BabyBear>(SymbolicVariable::new(
            Entry::Main { offset: 0 },
            1,
        ));
        let b = SymbolicExpression::Variable::<BabyBear>(SymbolicVariable::new(
            Entry::Main { offset: 0 },
            2,
        ));
        let result = a.clone() + b.clone();
        match result {
            SymbolicExpression::Add {
                degree_multiple,
                x,
                y,
            } => {
                assert_eq!(degree_multiple, 1);
                assert!(
                    matches!(*x, SymbolicExpression::Variable(ref v) if v.index == 1 && matches!(v.entry, Entry::Main { offset: 0 }))
                );
                assert!(
                    matches!(*y, SymbolicExpression::Variable(ref v) if v.index == 2 && matches!(v.entry, Entry::Main { offset: 0 }))
                );
            }
            _ => panic!("Addition did not create an Add expression"),
        }
    }

    #[test]
    fn test_degree_multiple_for_multiplication() {
        let a = SymbolicExpression::Variable::<BabyBear>(SymbolicVariable::new(
            Entry::Main { offset: 0 },
            1,
        ));
        let b = SymbolicExpression::Variable::<BabyBear>(SymbolicVariable::new(
            Entry::Main { offset: 0 },
            2,
        ));
        let result = a.clone() * b.clone();

        match result {
            SymbolicExpression::Mul {
                degree_multiple,
                x,
                y,
            } => {
                assert_eq!(degree_multiple, 2, "Multiplication should sum degrees");

                assert!(
                    matches!(*x, SymbolicExpression::Variable(ref v)
                        if v.index == 1 && matches!(v.entry, Entry::Main { offset: 0 })
                    ),
                    "Left operand should match `a`"
                );

                assert!(
                    matches!(*y, SymbolicExpression::Variable(ref v)
                        if v.index == 2 && matches!(v.entry, Entry::Main { offset: 0 })
                    ),
                    "Right operand should match `b`"
                );
            }
            _ => panic!("Multiplication did not create a `Mul` expression"),
        }
    }

    #[test]
    fn test_sum_operator() {
        let expressions = vec![
            SymbolicExpression::Constant(BabyBear::new(2)),
            SymbolicExpression::Constant(BabyBear::new(3)),
            SymbolicExpression::Constant(BabyBear::new(5)),
        ];
        let result: SymbolicExpression<BabyBear> = expressions.into_iter().sum();
        match result {
            SymbolicExpression::Constant(val) => assert_eq!(val, BabyBear::new(10)),
            _ => panic!("Sum did not produce correct result"),
        }
    }

    #[test]
    fn test_product_operator() {
        let expressions = vec![
            SymbolicExpression::Constant(BabyBear::new(2)),
            SymbolicExpression::Constant(BabyBear::new(3)),
            SymbolicExpression::Constant(BabyBear::new(4)),
        ];
        let result: SymbolicExpression<BabyBear> = expressions.into_iter().product();
        match result {
            SymbolicExpression::Constant(val) => assert_eq!(val, BabyBear::new(24)),
            _ => panic!("Product did not produce correct result"),
        }
    }
}
