use core::ops::{Add, Mul, Sub};

use p3_field::{Algebra, ExtensionField, Field, PrimeCharacteristicRing};
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;

/// An AIR (algebraic intermediate representation).
pub trait BaseAir<F>: Sync {
    /// The number of columns (a.k.a. registers) in this AIR.
    fn width(&self) -> usize;

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        None
    }
}

///  An AIR with 0 or more public values.
pub trait BaseAirWithPublicValues<F>: BaseAir<F> {
    fn num_public_values(&self) -> usize {
        0
    }
}

/// An AIR that works with a particular `AirBuilder`.
pub trait Air<AB: AirBuilder>: BaseAir<AB::F> {
    fn eval(&self, builder: &mut AB);
}

pub trait AirBuilder: Sized {
    type F: Field;

    type Expr: Algebra<Self::F> + Algebra<Self::Var>;

    type Var: Into<Self::Expr>
        + Copy
        + Send
        + Sync
        + Add<Self::F, Output = Self::Expr>
        + Add<Self::Var, Output = Self::Expr>
        + Add<Self::Expr, Output = Self::Expr>
        + Sub<Self::F, Output = Self::Expr>
        + Sub<Self::Var, Output = Self::Expr>
        + Sub<Self::Expr, Output = Self::Expr>
        + Mul<Self::F, Output = Self::Expr>
        + Mul<Self::Var, Output = Self::Expr>
        + Mul<Self::Expr, Output = Self::Expr>;

    type M: Matrix<Self::Var>;

    fn main(&self) -> Self::M;

    fn is_first_row(&self) -> Self::Expr;
    fn is_last_row(&self) -> Self::Expr;
    fn is_transition(&self) -> Self::Expr {
        self.is_transition_window(2)
    }
    fn is_transition_window(&self, size: usize) -> Self::Expr;

    /// Returns a sub-builder whose constraints are enforced only when `condition` is nonzero.
    fn when<I: Into<Self::Expr>>(&mut self, condition: I) -> FilteredAirBuilder<'_, Self> {
        FilteredAirBuilder {
            inner: self,
            condition: condition.into(),
        }
    }

    /// Returns a sub-builder whose constraints are enforced only when `x != y`.
    fn when_ne<I1: Into<Self::Expr>, I2: Into<Self::Expr>>(
        &mut self,
        x: I1,
        y: I2,
    ) -> FilteredAirBuilder<'_, Self> {
        self.when(x.into() - y.into())
    }

    /// Returns a sub-builder whose constraints are enforced only on the first row.
    fn when_first_row(&mut self) -> FilteredAirBuilder<'_, Self> {
        self.when(self.is_first_row())
    }

    /// Returns a sub-builder whose constraints are enforced only on the last row.
    fn when_last_row(&mut self) -> FilteredAirBuilder<'_, Self> {
        self.when(self.is_last_row())
    }

    /// Returns a sub-builder whose constraints are enforced on all rows except the last.
    fn when_transition(&mut self) -> FilteredAirBuilder<'_, Self> {
        self.when(self.is_transition())
    }

    /// Returns a sub-builder whose constraints are enforced on all rows except the last `size - 1`.
    fn when_transition_window(&mut self, size: usize) -> FilteredAirBuilder<'_, Self> {
        self.when(self.is_transition_window(size))
    }

    /// Assert that the given element is zero.
    ///
    /// Where possible, batching multiple assert_zero calls
    /// into a single assert_zeros call will improve performance.
    fn assert_zero<I: Into<Self::Expr>>(&mut self, x: I);

    /// Assert that every element of a given array is 0.
    ///
    /// This should be preferred over calling `assert_zero` multiple times.
    fn assert_zeros<const N: usize, I: Into<Self::Expr>>(&mut self, array: [I; N]) {
        for elem in array {
            self.assert_zero(elem);
        }
    }

    /// Assert that a given array consists of only boolean values.
    fn assert_bools<const N: usize, I: Into<Self::Expr>>(&mut self, array: [I; N]) {
        let zero_array = array.map(|x| x.into().bool_check());
        self.assert_zeros(zero_array);
    }

    /// Assert that `x` element is equal to `1`.
    fn assert_one<I: Into<Self::Expr>>(&mut self, x: I) {
        self.assert_zero(x.into() - Self::Expr::ONE);
    }

    /// Assert that the given elements are equal.
    fn assert_eq<I1: Into<Self::Expr>, I2: Into<Self::Expr>>(&mut self, x: I1, y: I2) {
        self.assert_zero(x.into() - y.into());
    }

    /// Assert that `x` is a boolean, i.e. either `0` or `1`.
    ///
    /// Where possible, batching multiple assert_bool calls
    /// into a single assert_bools call will improve performance.
    fn assert_bool<I: Into<Self::Expr>>(&mut self, x: I) {
        self.assert_zero(x.into().bool_check());
    }
}

pub trait AirBuilderWithPublicValues: AirBuilder {
    type PublicVar: Into<Self::Expr> + Copy;

    fn public_values(&self) -> &[Self::PublicVar];
}

pub trait PairBuilder: AirBuilder {
    fn preprocessed(&self) -> Self::M;
}

pub trait ExtensionBuilder: AirBuilder {
    type EF: ExtensionField<Self::F>;

    type ExprEF: Algebra<Self::Expr> + Algebra<Self::EF>;

    type VarEF: Into<Self::ExprEF> + Copy + Send + Sync;

    fn assert_zero_ext<I>(&mut self, x: I)
    where
        I: Into<Self::ExprEF>;

    fn assert_eq_ext<I1, I2>(&mut self, x: I1, y: I2)
    where
        I1: Into<Self::ExprEF>,
        I2: Into<Self::ExprEF>,
    {
        self.assert_zero_ext(x.into() - y.into());
    }

    fn assert_one_ext<I>(&mut self, x: I)
    where
        I: Into<Self::ExprEF>,
    {
        self.assert_eq_ext(x, Self::ExprEF::ONE)
    }
}

pub trait PermutationAirBuilder: ExtensionBuilder {
    type MP: Matrix<Self::VarEF>;

    type RandomVar: Into<Self::ExprEF> + Copy;

    fn permutation(&self) -> Self::MP;

    fn permutation_randomness(&self) -> &[Self::RandomVar];
}

#[derive(Debug)]
pub struct FilteredAirBuilder<'a, AB: AirBuilder> {
    pub inner: &'a mut AB,
    condition: AB::Expr,
}

impl<AB: AirBuilder> FilteredAirBuilder<'_, AB> {
    pub fn condition(&self) -> AB::Expr {
        self.condition.clone()
    }
}

impl<AB: AirBuilder> AirBuilder for FilteredAirBuilder<'_, AB> {
    type F = AB::F;
    type Expr = AB::Expr;
    type Var = AB::Var;
    type M = AB::M;

    fn main(&self) -> Self::M {
        self.inner.main()
    }

    fn is_first_row(&self) -> Self::Expr {
        self.inner.is_first_row()
    }

    fn is_last_row(&self) -> Self::Expr {
        self.inner.is_last_row()
    }

    fn is_transition_window(&self, size: usize) -> Self::Expr {
        self.inner.is_transition_window(size)
    }

    fn assert_zero<I: Into<Self::Expr>>(&mut self, x: I) {
        self.inner.assert_zero(self.condition() * x.into());
    }
}

impl<AB: ExtensionBuilder> ExtensionBuilder for FilteredAirBuilder<'_, AB> {
    type EF = AB::EF;
    type ExprEF = AB::ExprEF;
    type VarEF = AB::VarEF;

    fn assert_zero_ext<I>(&mut self, x: I)
    where
        I: Into<Self::ExprEF>,
    {
        self.inner.assert_zero_ext(x.into() * self.condition());
    }
}

impl<AB: PermutationAirBuilder> PermutationAirBuilder for FilteredAirBuilder<'_, AB> {
    type MP = AB::MP;

    type RandomVar = AB::RandomVar;

    fn permutation(&self) -> Self::MP {
        self.inner.permutation()
    }

    fn permutation_randomness(&self) -> &[Self::RandomVar] {
        self.inner.permutation_randomness()
    }
}
