use alloc::vec::Vec;

use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::row_index_mapped::{RowIndexMap, RowIndexMappedView};
use p3_util::{log2_strict_usize, reverse_bits_len};

#[inline]
pub(crate) const fn cfft_permute_index(index: usize, log_n: usize) -> usize {
    let (index, lsb) = (index >> 1, index & 1);
    reverse_bits_len(
        if lsb == 0 {
            index
        } else {
            (1 << log_n) - index - 1
        },
        log_n,
    )
}

pub(crate) fn cfft_permute_slice<T: Clone>(xs: &[T]) -> Vec<T> {
    let log_n = log2_strict_usize(xs.len());
    (0..xs.len())
        .map(|i| xs[cfft_permute_index(i, log_n)].clone())
        .collect()
}

pub(crate) fn cfft_permute_slice_chunked_in_place<T>(xs: &mut [T], chunk_size: usize) {
    assert_eq!(xs.len() % chunk_size, 0);
    let n_chunks = xs.len() / chunk_size;
    let log_n = log2_strict_usize(n_chunks);
    for i in 0..n_chunks {
        let j = cfft_permute_index(i, log_n);
        if i < j {
            // somehow this is slightly faster than the unsafe block below
            for k in 0..chunk_size {
                xs.swap(i * chunk_size + k, j * chunk_size + k);
            }
            /*
            unsafe {
                core::ptr::swap_nonoverlapping(
                    xs.as_mut_ptr().add(i * chunk_size),
                    xs.as_mut_ptr().add(j * chunk_size),
                    chunk_size,
                );
            }
            */
        }
    }
}

pub type CfftView<M> = RowIndexMappedView<CfftPerm, M>;

#[derive(Copy, Clone)]
pub struct CfftPerm {
    log_height: usize,
}

impl RowIndexMap for CfftPerm {
    fn height(&self) -> usize {
        1 << self.log_height
    }
    fn map_row_index(&self, r: usize) -> usize {
        cfft_permute_index(r, self.log_height)
    }
    fn to_row_major_matrix<T: Clone + Send + Sync, Inner: Matrix<T>>(
        &self,
        inner: Inner,
    ) -> RowMajorMatrix<T> {
        let mut inner = inner.to_row_major_matrix();
        cfft_permute_slice_chunked_in_place(&mut inner.values, inner.width);
        inner
    }
}

pub(crate) trait CfftPermutable<T: Send + Sync>: Matrix<T> + Sized {
    fn cfft_perm_rows(self) -> CfftView<Self>;
}

impl<T: Send + Sync, M: Matrix<T>> CfftPermutable<T> for M {
    fn cfft_perm_rows(self) -> CfftView<M> {
        RowIndexMappedView {
            index_map: CfftPerm {
                log_height: log2_strict_usize(self.height()),
            },
            inner: self,
        }
    }
}

#[cfg(test)]
mod tests {
    use itertools::Itertools;

    use super::*;

    #[test]
    fn ordering() {
        // reference ordering derived by hand
        assert_eq!(
            (0..8).map(|i| cfft_permute_index(i, 3)).collect_vec(),
            &[0, 7, 4, 3, 2, 5, 6, 1],
        );
        for log_n in 1..5 {
            let n = 1 << log_n;
            let sigma = |i| cfft_permute_index(i, log_n);
            for i in 0..n {
                // involution: σ(σ(i)) = i
                assert_eq!(sigma(sigma(i)), i);
            }
            // perm_slice same as perm_idx
            assert_eq!(
                cfft_permute_slice(&(0..n).collect_vec()),
                (0..n).map(sigma).collect_vec()
            );
        }
    }
}
