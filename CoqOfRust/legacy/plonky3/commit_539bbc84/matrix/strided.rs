use crate::row_index_mapped::{RowIndexMap, RowIndexMappedView};
use crate::Matrix;

#[derive(Debug)]
pub struct VerticallyStridedRowIndexMap {
    // Store our height
    height: usize,
    stride: usize,
    offset: usize,
}

pub type VerticallyStridedMatrixView<Inner> =
    RowIndexMappedView<VerticallyStridedRowIndexMap, Inner>;

impl VerticallyStridedRowIndexMap {
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
