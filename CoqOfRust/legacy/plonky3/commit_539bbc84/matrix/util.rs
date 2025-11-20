use core::borrow::BorrowMut;

use p3_maybe_rayon::prelude::*;
use p3_util::{log2_strict_usize, reverse_bits_len};
use tracing::instrument;

use crate::dense::{DenseMatrix, DenseStorage, RowMajorMatrix};
use crate::Matrix;

#[instrument(level = "debug", skip_all)]
pub fn reverse_matrix_index_bits<'a, F, S>(mat: &mut DenseMatrix<F, S>)
where
    F: Clone + Send + Sync + 'a,
    S: DenseStorage<F> + BorrowMut<[F]>,
{
    let w = mat.width();
    let h = mat.height();
    let log_h = log2_strict_usize(h);
    let values = mat.values.borrow_mut().as_mut_ptr() as usize;

    (0..h).into_par_iter().for_each(|i| {
        let values = values as *mut F;
        let j = reverse_bits_len(i, log_h);
        if i < j {
            unsafe { swap_rows_raw(values, w, i, j) };
        }
    });
}

/// Assumes `i < j`.
pub fn swap_rows<F: Clone + Send + Sync>(mat: &mut RowMajorMatrix<F>, i: usize, j: usize) {
    let w = mat.width();
    let (upper, lower) = mat.values.split_at_mut(j * w);
    let row_i = &mut upper[i * w..(i + 1) * w];
    let row_j = &mut lower[..w];
    row_i.swap_with_slice(row_j);
}

/// Assumes `i < j`.
///
/// SAFETY: The caller must ensure `i < j < h`, where `h` is the height of the matrix.
pub(crate) unsafe fn swap_rows_raw<F>(mat: *mut F, w: usize, i: usize, j: usize) {
    let row_i = core::slice::from_raw_parts_mut(mat.add(i * w), w);
    let row_j = core::slice::from_raw_parts_mut(mat.add(j * w), w);
    row_i.swap_with_slice(row_j);
}
