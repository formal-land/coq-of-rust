use crate::Matrix;
use crate::row_index_mapped::{RowIndexMap, RowIndexMappedView};

/// A vertical row-mapping strategy that selects every `stride`-th row from an inner matrix,
/// starting at a fixed `offset`.
///
/// This enables vertical striding like selecting rows: `offset`, `offset + stride`, etc.
#[derive(Debug)]
pub struct VerticallyStridedRowIndexMap {
    /// The number of rows in the resulting view.
    height: usize,
    /// The step size between selected rows in the inner matrix.
    stride: usize,
    /// The offset to start the stride from.
    offset: usize,
}

pub type VerticallyStridedMatrixView<Inner> =
    RowIndexMappedView<VerticallyStridedRowIndexMap, Inner>;

impl VerticallyStridedRowIndexMap {
    /// Create a new vertically strided view over a matrix.
    ///
    /// This selects rows in the inner matrix starting from `offset`, and then every `stride` rows after.
    ///
    /// # Arguments
    /// - `inner`: The inner matrix to view.
    /// - `stride`: The number of rows between each selected row.
    /// - `offset`: The initial row to start from.
    pub fn new_view<T: Send + Sync, Inner: Matrix<T>>(
        inner: Inner,
        stride: usize,
        offset: usize,
    ) -> VerticallyStridedMatrixView<Inner> {
        let h = inner.height();
        let full_strides = h / stride;
        let remainder = h % stride;
        let final_stride = offset < remainder;
        let height = full_strides + final_stride as usize;
        RowIndexMappedView {
            index_map: Self {
                height,
                stride,
                offset,
            },
            inner,
        }
    }
}

impl RowIndexMap for VerticallyStridedRowIndexMap {
    fn height(&self) -> usize {
        self.height
    }

    fn map_row_index(&self, r: usize) -> usize {
        r * self.stride + self.offset
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec;

    use super::*;
    use crate::{Matrix, RowMajorMatrix};

    fn sample_matrix() -> RowMajorMatrix<i32> {
        // A 5x3 matrix:
        // [10, 11, 12]
        // [20, 21, 22]
        // [30, 31, 32]
        // [40, 41, 42]
        // [50, 51, 52]
        RowMajorMatrix::new(
            vec![10, 11, 12, 20, 21, 22, 30, 31, 32, 40, 41, 42, 50, 51, 52],
            3,
        )
    }

    #[test]
    fn test_vertically_strided_view_stride_1_offset_0() {
        let matrix = sample_matrix();
        let view = VerticallyStridedRowIndexMap::new_view(matrix, 1, 0);

        assert_eq!(view.height(), 5);
        assert_eq!(view.width(), 3);

        assert_eq!(view.get(0, 0), 10);
        assert_eq!(view.get(1, 1), 21);
        assert_eq!(view.get(4, 2), 52);
    }

    #[test]
    fn test_vertically_strided_view_stride_2_offset_0() {
        let matrix = sample_matrix();
        let view = VerticallyStridedRowIndexMap::new_view(matrix, 2, 0);

        assert_eq!(view.height(), 3);
        assert_eq!(view.get(0, 0), 10); // row 0
        assert_eq!(view.get(1, 1), 31); // row 2
        assert_eq!(view.get(2, 2), 52); // row 4
    }

    #[test]
    fn test_vertically_strided_view_stride_2_offset_1() {
        let matrix = sample_matrix();
        let view = VerticallyStridedRowIndexMap::new_view(matrix, 2, 1);

        assert_eq!(view.height(), 2);
        assert_eq!(view.get(0, 0), 20); // row 1
        assert_eq!(view.get(1, 1), 41); // row 3
    }

    #[test]
    fn test_vertically_strided_view_stride_3_offset_0() {
        let matrix = sample_matrix();
        let view = VerticallyStridedRowIndexMap::new_view(matrix, 3, 0);

        assert_eq!(view.height(), 2);
        assert_eq!(view.get(0, 0), 10); // row 0
        assert_eq!(view.get(1, 1), 41); // row 3
    }

    #[test]
    fn test_vertically_strided_view_stride_3_offset_1() {
        let matrix = sample_matrix();
        let view = VerticallyStridedRowIndexMap::new_view(matrix, 3, 1);

        assert_eq!(view.height(), 2);
        assert_eq!(view.get(0, 0), 20); // row 1
        assert_eq!(view.get(1, 1), 51); // row 4
    }

    #[test]
    fn test_vertically_strided_view_stride_3_offset_2() {
        let matrix = sample_matrix();
        let view = VerticallyStridedRowIndexMap::new_view(matrix, 3, 2);

        assert_eq!(view.height(), 1);
        assert_eq!(view.get(0, 2), 32); // row 2
    }

    #[test]
    fn test_vertically_strided_view_stride_greater_than_height() {
        let matrix = sample_matrix();
        let view = VerticallyStridedRowIndexMap::new_view(matrix, 10, 0);

        assert_eq!(view.height(), 1);
        assert_eq!(view.get(0, 0), 10); // row 0
    }

    #[test]
    fn test_vertically_strided_view_stride_greater_than_height_with_valid_offset() {
        let matrix = sample_matrix(); // height = 5
        let view = VerticallyStridedRowIndexMap::new_view(matrix, 10, 4);

        // offset == 4 < height == 5 → view selects row 4
        assert_eq!(view.height(), 1);
        assert_eq!(view.get(0, 2), 52); // row 4
    }

    #[test]
    #[should_panic]
    fn test_vertically_strided_view_stride_greater_than_height_with_offset_beyond_height() {
        let matrix = sample_matrix(); // height = 5
        let view = VerticallyStridedRowIndexMap::new_view(matrix, 10, 6);

        // offset == 6 > height == 5 → no valid row
        assert_eq!(view.height(), 0);

        // Should panic when trying to access row 0
        let _ = view.get(0, 0);
    }
}
