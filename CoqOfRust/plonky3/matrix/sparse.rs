use alloc::vec;
use alloc::vec::Vec;
use core::iter;
use core::ops::Range;

use rand::Rng;
use rand::distr::{Distribution, StandardUniform};

use crate::Matrix;

/// A sparse matrix stored in the compressed sparse row format.
#[derive(Debug)]
pub struct CsrMatrix<T> {
    width: usize,

    /// A list of `(col, coefficient)` pairs.
    nonzero_values: Vec<(usize, T)>,

    /// Indices of `nonzero_values`. The `i`th index here indicates the first index belonging to the
    /// `i`th row.
    row_indices: Vec<usize>,
}

impl<T: Clone + Default + Send + Sync> CsrMatrix<T> {
    fn row_index_range(&self, r: usize) -> Range<usize> {
        debug_assert!(r < self.height());
        self.row_indices[r]..self.row_indices[r + 1]
    }

    #[must_use]
    pub fn sparse_row(&self, r: usize) -> &[(usize, T)] {
        &self.nonzero_values[self.row_index_range(r)]
    }

    pub fn sparse_row_mut(&mut self, r: usize) -> &mut [(usize, T)] {
        let range = self.row_index_range(r);
        &mut self.nonzero_values[range]
    }

    pub fn rand_fixed_row_weight<R: Rng>(
        rng: &mut R,
        rows: usize,
        cols: usize,
        row_weight: usize,
    ) -> Self
    where
        T: Default,
        StandardUniform: Distribution<T>,
    {
        let nonzero_values = iter::repeat_with(|| (rng.random_range(0..cols), rng.random()))
            .take(rows * row_weight)
            .collect();
        let row_indices = (0..=rows).map(|r| r * row_weight).collect();
        Self {
            width: cols,
            nonzero_values,
            row_indices,
        }
    }
}

impl<T: Clone + Default + Send + Sync> Matrix<T> for CsrMatrix<T> {
    fn width(&self) -> usize {
        self.width
    }

    fn height(&self) -> usize {
        self.row_indices.len() - 1
    }

    fn get(&self, r: usize, c: usize) -> T {
        self.sparse_row(r)
            .iter()
            .find(|(col, _)| *col == c)
            .map(|(_, val)| val.clone())
            .unwrap_or_default()
    }

    type Row<'a>
        = <Vec<T> as IntoIterator>::IntoIter
    where
        Self: 'a;

    fn row(&self, r: usize) -> Self::Row<'_> {
        let mut row = vec![T::default(); self.width()];
        for (c, v) in self.sparse_row(r) {
            row[*c] = v.clone();
        }
        row.into_iter()
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec;

    use rand::SeedableRng;
    use rand::rngs::SmallRng;

    use super::*;

    fn sample_csr() -> CsrMatrix<i32> {
        // 3x4 matrix:
        // [ 0, 5, 0, 0 ]
        // [ 1, 0, 0, 2 ]
        // [ 0, 0, 0, 0 ]
        CsrMatrix {
            width: 4,
            nonzero_values: vec![(1, 5), (0, 1), (3, 2)],
            row_indices: vec![0, 1, 3, 3], // row 0: 0..1, row 1: 1..3, row 2: 3..3 (empty)
        }
    }

    #[test]
    fn test_dimensions() {
        let matrix = sample_csr();
        assert_eq!(matrix.width(), 4);
        assert_eq!(matrix.height(), 3);
    }

    #[test]
    fn test_get_existing() {
        let matrix = sample_csr();
        assert_eq!(matrix.get(0, 1), 5);
        assert_eq!(matrix.get(1, 0), 1);
        assert_eq!(matrix.get(1, 3), 2);
    }

    #[test]
    fn test_get_default() {
        let matrix = sample_csr();
        assert_eq!(matrix.get(0, 0), 0); // not stored = default
        assert_eq!(matrix.get(2, 2), 0); // row 2 is empty
    }

    #[test]
    fn test_sparse_row_access() {
        let matrix = sample_csr();
        assert_eq!(matrix.sparse_row(0), &[(1, 5)]);
        assert_eq!(matrix.sparse_row(1), &[(0, 1), (3, 2)]);
        assert_eq!(matrix.sparse_row(2), &[]);
    }

    #[test]
    fn test_sparse_row_mutation() {
        let mut matrix = sample_csr();
        let row1 = matrix.sparse_row_mut(1);
        row1[0].1 = 99;
        row1[1].1 = 42;
        assert_eq!(matrix.get(1, 0), 99);
        assert_eq!(matrix.get(1, 3), 42);
    }

    #[test]
    fn test_row_iteration() {
        let matrix = sample_csr();
        let row0: Vec<_> = matrix.row(0).collect();
        let row1: Vec<_> = matrix.row(1).collect();
        let row2: Vec<_> = matrix.row(2).collect();

        assert_eq!(row0, vec![0, 5, 0, 0]);
        assert_eq!(row1, vec![1, 0, 0, 2]);
        assert_eq!(row2, vec![0, 0, 0, 0]);
    }

    #[test]
    fn test_rand_fixed_row_weight() {
        let mut rng = SmallRng::seed_from_u64(1);
        let rows = 5;
        let cols = 10;
        let weight = 3;

        let matrix = CsrMatrix::<u8>::rand_fixed_row_weight(&mut rng, rows, cols, weight);

        assert_eq!(matrix.height(), rows);
        assert_eq!(matrix.width(), cols);
        assert_eq!(matrix.nonzero_values.len(), rows * weight);
        assert_eq!(matrix.row_indices.len(), rows + 1);

        for r in 0..rows {
            let sparse = matrix.sparse_row(r);
            assert_eq!(sparse.len(), weight);
            for (col, _) in sparse {
                assert!(*col < cols);
            }
        }
    }

    #[test]
    #[should_panic]
    fn test_sparse_row_out_of_bounds_panics() {
        let matrix = sample_csr();
        let _ = matrix.sparse_row(10);
    }

    #[test]
    #[should_panic]
    fn test_sparse_row_mut_out_of_bounds_panics() {
        let mut matrix = sample_csr();
        let _ = matrix.sparse_row_mut(42);
    }

    #[test]
    fn test_empty_matrix() {
        let matrix = CsrMatrix::<i32> {
            width: 0,
            nonzero_values: vec![],
            row_indices: vec![0],
        };

        assert_eq!(matrix.width(), 0);
        assert_eq!(matrix.height(), 0);
    }

    #[test]
    fn test_single_row_single_entry() {
        let matrix = CsrMatrix {
            width: 3,
            nonzero_values: vec![(1, 7)],
            row_indices: vec![0, 1],
        };

        assert_eq!(matrix.get(0, 1), 7);
        assert_eq!(matrix.get(0, 0), 0);
        assert_eq!(matrix.get(0, 2), 0);

        let row: Vec<_> = matrix.row(0).collect();
        assert_eq!(row, vec![0, 7, 0]);
    }

    #[test]
    fn test_row_index_range_consistency() {
        let matrix = sample_csr();
        for r in 0..matrix.height() {
            let range = matrix.row_index_range(r);
            let sparse = &matrix.nonzero_values[range.clone()];
            assert_eq!(sparse, matrix.sparse_row(r));
        }
    }

    #[test]
    fn test_row_index_monotonicity() {
        let matrix = sample_csr();
        // Ensure row_indices is strictly increasing or equal
        for w in matrix.row_indices.windows(2) {
            assert!(w[0] <= w[1], "row_indices not non-decreasing");
        }
    }

    #[test]
    fn test_full_row_access_behavior() {
        let matrix = sample_csr();
        for r in 0..matrix.height() {
            let row_vec: Vec<_> = matrix.row(r).collect();
            for (c, val) in row_vec.iter().enumerate() {
                assert_eq!(matrix.get(r, c), *val);
            }
        }
    }
}
