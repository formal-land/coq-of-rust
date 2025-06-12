use p3_util::{log2_strict_usize, reverse_bits_len};

use crate::dense::{DenseMatrix, DenseStorage, RowMajorMatrix};
use crate::row_index_mapped::{RowIndexMap, RowIndexMappedView};
use crate::util::reverse_matrix_index_bits;
use crate::Matrix;

/// A matrix whose row indices are possibly bit-reversed, enabling easily switching
/// between orderings. Pretty much just either `RowMajorMatrix` or
/// `BitReversedMatrixView<RowMajorMatrix>`.
pub trait BitReversableMatrix<T: Send + Sync>: Matrix<T> {
    type BitRev: BitReversableMatrix<T>;
    fn bit_reverse_rows(self) -> Self::BitRev;
}

#[derive(Debug)]
pub struct BitReversalPerm {
    log_height: usize,
}

impl BitReversalPerm {
    /// Assumes the inner matrix height is a power of two; panics otherwise.
    pub fn new_view<T: Send + Sync, Inner: Matrix<T>>(
        inner: Inner,
    ) -> BitReversedMatrixView<Inner> {
        RowIndexMappedView {
            index_map: Self {
                log_height: log2_strict_usize(inner.height()),
            },
            inner,
        }
    }
}

impl RowIndexMap for BitReversalPerm {
    fn height(&self) -> usize {
        1 << self.log_height
    }
    fn map_row_index(&self, r: usize) -> usize {
        reverse_bits_len(r, self.log_height)
    }
    // This might not be more efficient than the lazy generic impl
    // if we have a nested view.
    fn to_row_major_matrix<T: Clone + Send + Sync, Inner: Matrix<T>>(
        &self,
        inner: Inner,
    ) -> RowMajorMatrix<T> {
        let mut inner = inner.to_row_major_matrix();
        reverse_matrix_index_bits(&mut inner);
        inner
    }
}

pub type BitReversedMatrixView<Inner> = RowIndexMappedView<BitReversalPerm, Inner>;

impl<T: Clone + Send + Sync, S: DenseStorage<T>> BitReversableMatrix<T>
    for BitReversedMatrixView<DenseMatrix<T, S>>
{
    type BitRev = DenseMatrix<T, S>;
    fn bit_reverse_rows(self) -> Self::BitRev {
        self.inner
    }
}

impl<T: Clone + Send + Sync, S: DenseStorage<T>> BitReversableMatrix<T> for DenseMatrix<T, S> {
    type BitRev = BitReversedMatrixView<DenseMatrix<T, S>>;
    fn bit_reverse_rows(self) -> Self::BitRev {
        BitReversalPerm::new_view(self)
    }
}
