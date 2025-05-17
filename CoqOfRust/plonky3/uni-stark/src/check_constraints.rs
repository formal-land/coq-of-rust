use alloc::vec::Vec;

use p3_air::{Air, AirBuilder, AirBuilderWithPublicValues};
use p3_field::Field;
use p3_matrix::Matrix;
use p3_matrix::dense::{RowMajorMatrix, RowMajorMatrixView};
use p3_matrix::stack::VerticalPair;
use tracing::instrument;

#[instrument(name = "check constraints", skip_all)]
pub(crate) fn check_constraints<F, A>(air: &A, main: &RowMajorMatrix<F>, public_values: &Vec<F>)
where
    F: Field,
    A: for<'a> Air<DebugConstraintBuilder<'a, F>>,
{
    let height = main.height();

    (0..height).for_each(|i| {
        let i_next = (i + 1) % height;

        let local = main.row_slice(i);
        let next = main.row_slice(i_next);
        let main = VerticalPair::new(
            RowMajorMatrixView::new_row(&*local),
            RowMajorMatrixView::new_row(&*next),
        );

        let mut builder = DebugConstraintBuilder {
            row_index: i,
            main,
            public_values,
            is_first_row: F::from_bool(i == 0),
            is_last_row: F::from_bool(i == height - 1),
            is_transition: F::from_bool(i != height - 1),
        };

        air.eval(&mut builder);
    });
}

/// An `AirBuilder` which asserts that each constraint is zero, allowing any failed constraints to
/// be detected early.
#[derive(Debug)]
pub struct DebugConstraintBuilder<'a, F: Field> {
    row_index: usize,
    main: VerticalPair<RowMajorMatrixView<'a, F>, RowMajorMatrixView<'a, F>>,
    public_values: &'a [F],
    is_first_row: F,
    is_last_row: F,
    is_transition: F,
}

impl<'a, F> AirBuilder for DebugConstraintBuilder<'a, F>
where
    F: Field,
{
    type F = F;
    type Expr = F;
    type Var = F;
    type M = VerticalPair<RowMajorMatrixView<'a, F>, RowMajorMatrixView<'a, F>>;

    fn main(&self) -> Self::M {
        self.main
    }

    fn is_first_row(&self) -> Self::Expr {
        self.is_first_row
    }

    fn is_last_row(&self) -> Self::Expr {
        self.is_last_row
    }

    /// # Panics
    /// This function panics if `size` is not `2`.
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
            F::ZERO,
            "constraints had nonzero value on row {}",
            self.row_index
        );
    }

    fn assert_eq<I1: Into<Self::Expr>, I2: Into<Self::Expr>>(&mut self, x: I1, y: I2) {
        let x = x.into();
        let y = y.into();
        assert_eq!(
            x, y,
            "values didn't match on row {}: {} != {}",
            self.row_index, x, y
        );
    }
}

impl<F: Field> AirBuilderWithPublicValues for DebugConstraintBuilder<'_, F> {
    type PublicVar = Self::F;

    fn public_values(&self) -> &[Self::F] {
        self.public_values
    }
}
