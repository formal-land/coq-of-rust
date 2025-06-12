use core::ops::Deref;

use p3_field::PackedValue;

use crate::dense::RowMajorMatrix;
use crate::Matrix;

/// A RowIndexMap remaps row indices, and can change the height.
pub trait RowIndexMap: Send + Sync {
    fn height(&self) -> usize;
    fn map_row_index(&self, r: usize) -> usize;

    /// Permutations can optionally provide an optimized method to
    /// convert to dense form.
    fn to_row_major_matrix<T: Clone + Send + Sync, Inner: Matrix<T>>(
        &self,
        inner: Inner,
    ) -> RowMajorMatrix<T> {
        RowMajorMatrix::new(
            (0..self.height())
                .flat_map(|r| inner.row(self.map_row_index(r)))
                .collect(),
            inner.width(),
        )
    }
}

#[derive(Copy, Clone, Debug)]
pub struct RowIndexMappedView<IndexMap, Inner> {
    pub index_map: IndexMap,
    pub inner: Inner,
}

impl<T: Send + Sync, IndexMap: RowIndexMap, Inner: Matrix<T>> Matrix<T>
    for RowIndexMappedView<IndexMap, Inner>
{
    fn width(&self) -> usize {
        self.inner.width()
    }
    fn height(&self) -> usize {
        self.index_map.height()
    }

    fn get(&self, r: usize, c: usize) -> T {
        self.inner.get(self.index_map.map_row_index(r), c)
    }

    type Row<'a>
        = Inner::Row<'a>
    where
        Self: 'a;

    // Override these methods so we use the potentially optimized inner methods instead of defaults.

    fn row(&self, r: usize) -> Self::Row<'_> {
        self.inner.row(self.index_map.map_row_index(r))
    }

    fn row_slice(&self, r: usize) -> impl Deref<Target = [T]> {
        self.inner.row_slice(self.index_map.map_row_index(r))
    }

    fn to_row_major_matrix(self) -> RowMajorMatrix<T>
    where
        Self: Sized,
        T: Clone,
    {
        // Use Perm's optimized permutation routine, if it has one.
        self.index_map.to_row_major_matrix(self.inner)
    }

    fn horizontally_packed_row<'a, P>(
        &'a self,
        r: usize,
    ) -> (
        impl Iterator<Item = P> + Send + Sync,
        impl Iterator<Item = T> + Send + Sync,
    )
    where
        P: PackedValue<Value = T>,
        T: Clone + 'a,
    {
        self.inner
            .horizontally_packed_row(self.index_map.map_row_index(r))
    }

    fn padded_horizontally_packed_row<'a, P>(
        &'a self,
        r: usize,
    ) -> impl Iterator<Item = P> + Send + Sync
    where
        P: PackedValue<Value = T>,
        T: Clone + Default + 'a,
    {
        self.inner
            .padded_horizontally_packed_row(self.index_map.map_row_index(r))
    }
}
