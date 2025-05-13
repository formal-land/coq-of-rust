Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import plonky3.air.air.

(* pub trait AirBuilder: Sized { *)
Module AirBuilder.
(* 
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
*)
End AirBuilder.