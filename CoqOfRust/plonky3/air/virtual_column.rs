use alloc::vec;
use alloc::vec::Vec;
use core::ops::Mul;

use p3_field::{Field, PrimeCharacteristicRing};

/// An affine function over columns in a PAIR.
#[derive(Clone, Debug)]
pub struct VirtualPairCol<F: Field> {
    column_weights: Vec<(PairCol, F)>,
    constant: F,
}

/// A column in a PAIR, i.e. either a preprocessed column or a main trace column.
#[derive(Clone, Copy, Debug)]
pub enum PairCol {
    Preprocessed(usize),
    Main(usize),
}

impl PairCol {
    pub const fn get<T: Copy>(&self, preprocessed: &[T], main: &[T]) -> T {
        match self {
            Self::Preprocessed(i) => preprocessed[*i],
            Self::Main(i) => main[*i],
        }
    }
}

impl<F: Field> VirtualPairCol<F> {
    pub const fn new(column_weights: Vec<(PairCol, F)>, constant: F) -> Self {
        Self {
            column_weights,
            constant,
        }
    }

    pub fn new_preprocessed(column_weights: Vec<(usize, F)>, constant: F) -> Self {
        Self::new(
            column_weights
                .into_iter()
                .map(|(i, w)| (PairCol::Preprocessed(i), w))
                .collect(),
            constant,
        )
    }

    pub fn new_main(column_weights: Vec<(usize, F)>, constant: F) -> Self {
        Self::new(
            column_weights
                .into_iter()
                .map(|(i, w)| (PairCol::Main(i), w))
                .collect(),
            constant,
        )
    }

    pub const ONE: Self = Self::constant(F::ONE);

    #[must_use]
    pub const fn constant(x: F) -> Self {
        Self {
            column_weights: vec![],
            constant: x,
        }
    }

    #[must_use]
    pub fn single(column: PairCol) -> Self {
        Self {
            column_weights: vec![(column, F::ONE)],
            constant: F::ZERO,
        }
    }

    #[must_use]
    pub fn single_preprocessed(column: usize) -> Self {
        Self::single(PairCol::Preprocessed(column))
    }

    #[must_use]
    pub fn single_main(column: usize) -> Self {
        Self::single(PairCol::Main(column))
    }

    #[must_use]
    pub fn sum_main(columns: Vec<usize>) -> Self {
        let column_weights = columns.into_iter().map(|col| (col, F::ONE)).collect();
        Self::new_main(column_weights, F::ZERO)
    }

    #[must_use]
    pub fn sum_preprocessed(columns: Vec<usize>) -> Self {
        let column_weights = columns.into_iter().map(|col| (col, F::ONE)).collect();
        Self::new_preprocessed(column_weights, F::ZERO)
    }

    /// `a - b`, where `a` and `b` are columns in the preprocessed trace.
    #[must_use]
    pub fn diff_preprocessed(a_col: usize, b_col: usize) -> Self {
        Self::new_preprocessed(vec![(a_col, F::ONE), (b_col, F::NEG_ONE)], F::ZERO)
    }

    /// `a - b`, where `a` and `b` are columns in the main trace.
    #[must_use]
    pub fn diff_main(a_col: usize, b_col: usize) -> Self {
        Self::new_main(vec![(a_col, F::ONE), (b_col, F::NEG_ONE)], F::ZERO)
    }

    pub fn apply<Expr, Var>(&self, preprocessed: &[Var], main: &[Var]) -> Expr
    where
        F: Into<Expr>,
        Expr: PrimeCharacteristicRing + Mul<F, Output = Expr>,
        Var: Into<Expr> + Copy,
    {
        self.column_weights
            .iter()
            .fold(self.constant.into(), |acc, &(col, w)| {
                acc + col.get(preprocessed, main).into() * w
            })
    }
}

#[cfg(test)]
mod tests {
    use p3_baby_bear::BabyBear;

    use super::*;

    type F = BabyBear;

    #[test]
    fn test_pair_col_get_main_and_preprocessed() {
        let pre = [F::from_u8(10), F::from_u8(20)];
        let main = [F::from_u8(30), F::from_u8(40)];

        // Preprocessed(1) should return 20
        assert_eq!(PairCol::Preprocessed(1).get(&pre, &main), F::from_u8(20));

        // Main(0) should return 30
        assert_eq!(PairCol::Main(0).get(&pre, &main), F::from_u8(30));
    }

    #[test]
    fn test_constant_only_virtual_pair_col() {
        let col = VirtualPairCol::<F>::constant(F::from_u8(7));

        // Apply to any input: result should always be the constant
        let pre = [F::ONE];
        let main = [F::ONE];
        let result = col.apply::<F, F>(&pre, &main);

        assert_eq!(result, F::from_u8(7));
    }

    #[test]
    fn test_single_main_column() {
        let col = VirtualPairCol::<F>::single_main(1); // column index 1

        let main = [F::from_u8(9), F::from_u8(5)];
        let pre = [F::ZERO]; // ignored

        let result = col.apply::<F, F>(&pre, &main);

        // Since we used single_main(1), this should equal main[1] = 5
        assert_eq!(result, F::from_u8(5));
    }

    #[test]
    fn test_single_preprocessed_column() {
        let col = VirtualPairCol::<F>::single_preprocessed(0);

        let pre = [F::from_u8(12)];
        let main = [];

        let result = col.apply::<F, F>(&pre, &main);

        assert_eq!(result, F::from_u8(12));
    }

    #[test]
    fn test_sum_main_columns() {
        // This adds up main[0] + main[2]
        let col = VirtualPairCol::<F>::sum_main(vec![0, 2]);

        let main = [
            F::TWO,
            F::from_u8(99), // ignored
            F::from_u8(5),
        ];
        let pre = [];

        let result = col.apply::<F, F>(&pre, &main);

        assert_eq!(result, F::from_u8(2) + F::from_u8(5));
    }

    #[test]
    fn test_sum_preprocessed_columns() {
        let col = VirtualPairCol::<F>::sum_preprocessed(vec![1, 2]);

        let pre = [
            F::from_u8(3), // ignored
            F::from_u8(4),
            F::from_u8(6),
        ];
        let main = [];

        let result = col.apply::<F, F>(&pre, &main);

        assert_eq!(result, F::from_u8(4) + F::from_u8(6));
    }

    #[test]
    fn test_diff_main_columns() {
        // Computes main[2] - main[0]
        let col = VirtualPairCol::<F>::diff_main(2, 0);

        let main = [
            F::from_u8(7),
            F::ZERO, // ignored
            F::from_u8(10),
        ];
        let pre = [];

        let result = col.apply::<F, F>(&pre, &main);

        assert_eq!(result, F::from_u8(10) - F::from_u8(7));
    }

    #[test]
    fn test_diff_preprocessed_columns() {
        // Computes pre[1] - pre[0]
        let col = VirtualPairCol::<F>::diff_preprocessed(1, 0);

        let pre = [F::from_u8(4), F::from_u8(15)];
        let main = [];

        let result = col.apply::<F, F>(&pre, &main);

        assert_eq!(result, F::from_u8(15) - F::from_u8(4));
    }

    #[test]
    fn test_combination_with_constant_and_weights() {
        // Computes: 3 * main[1] + 2 * pre[0] + constant (5)
        let col = VirtualPairCol {
            column_weights: vec![
                (PairCol::Main(1), F::from_u8(3)),
                (PairCol::Preprocessed(0), F::TWO),
            ],
            constant: F::from_u8(5),
        };

        let main = [F::ZERO, F::from_u8(4)];
        let pre = [F::from_u8(6)];

        let result = col.apply::<F, F>(&pre, &main);

        // result = 3*4 + 2*6 + 5
        assert_eq!(result, F::from_u8(29));
    }

    #[test]
    fn test_virtual_pair_col_one_is_identity() {
        // VirtualPairCol::ONE should always evaluate to 1 regardless of input
        let col = VirtualPairCol::<F>::ONE;
        let pre = [F::from_u8(99)];
        let main = [F::from_u8(42)];

        let result = col.apply::<F, F>(&pre, &main);

        assert_eq!(result, F::ONE);
    }
}
