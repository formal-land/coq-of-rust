use p3_field::{add_scaled_slice_in_place, Field};
use p3_maybe_rayon::prelude::*;

use crate::dense::RowMajorMatrix;
use crate::sparse::CsrMatrix;
use crate::Matrix;

/// Compute `C = A * B`, where `A` in a CSR matrix and `B` is a dense matrix.
///
/// # Panics
/// Panics if dimensions of input matrices don't match.
pub fn mul_csr_dense<F, B>(a: &CsrMatrix<F>, b: &B) -> RowMajorMatrix<F>
where
    F: Field,
    B: Matrix<F> + Sync,
{
    assert_eq!(a.width(), b.height(), "A, B dimensions don't match");
    let c_width = b.width();

    let c_values = (0..a.height())
        .into_par_iter()
        .flat_map(|a_row_idx| {
            let mut c_row = F::zero_vec(c_width);
            for &(a_col_idx, a_val) in a.sparse_row(a_row_idx) {
                add_scaled_slice_in_place(&mut c_row, b.row(a_col_idx), a_val);
            }
            c_row
        })
        .collect();

    RowMajorMatrix::new(c_values, c_width)
}
