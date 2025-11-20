//! Matrix library.

#![no_std]

extern crate alloc;

use alloc::vec::Vec;
use core::fmt::{Debug, Display, Formatter};
use core::ops::Deref;

use itertools::{izip, Itertools};
use p3_field::{
    dot_product, ExtensionField, Field, FieldAlgebra, FieldExtensionAlgebra, PackedValue,
};
use p3_maybe_rayon::prelude::*;
use strided::{VerticallyStridedMatrixView, VerticallyStridedRowIndexMap};
use tracing::instrument;

use crate::dense::RowMajorMatrix;

pub mod bitrev;
pub mod dense;
pub mod extension;
pub mod horizontally_truncated;
pub mod mul;
pub mod row_index_mapped;
pub mod sparse;
pub mod stack;
pub mod strided;
pub mod util;

#[derive(Copy, Clone, PartialEq, Eq)]
pub struct Dimensions {
    pub width: usize,
    pub height: usize,
}

impl Debug for Dimensions {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}x{}", self.width, self.height)
    }
}

impl Display for Dimensions {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}x{}", self.width, self.height)
    }
}

pub trait Matrix<T: Send + Sync>: Send + Sync {
    fn width(&self) -> usize;
    fn height(&self) -> usize;

    fn dimensions(&self) -> Dimensions {
        Dimensions {
            width: self.width(),
            height: self.height(),
        }
    }

    fn get(&self, r: usize, c: usize) -> T {
        self.row(r).nth(c).unwrap()
    }

    type Row<'a>: Iterator<Item = T> + Send + Sync
    where
        Self: 'a;

    fn row(&self, r: usize) -> Self::Row<'_>;

    fn rows(&self) -> impl Iterator<Item = Self::Row<'_>> {
        (0..self.height()).map(move |r| self.row(r))
    }

    fn par_rows(&self) -> impl IndexedParallelIterator<Item = Self::Row<'_>> {
        (0..self.height()).into_par_iter().map(move |r| self.row(r))
    }

    // Opaque return type implicitly captures &'_ self
    fn row_slice(&self, r: usize) -> impl Deref<Target = [T]> {
        self.row(r).collect_vec()
    }

    fn first_row(&self) -> Self::Row<'_> {
        self.row(0)
    }

    fn last_row(&self) -> Self::Row<'_> {
        self.row(self.height() - 1)
    }

    fn to_row_major_matrix(self) -> RowMajorMatrix<T>
    where
        Self: Sized,
        T: Clone,
    {
        RowMajorMatrix::new(
            (0..self.height()).flat_map(|r| self.row(r)).collect(),
            self.width(),
        )
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
        let num_packed = self.width() / P::WIDTH;
        let packed = (0..num_packed).map(move |c| P::from_fn(|i| self.get(r, P::WIDTH * c + i)));
        let sfx = (num_packed * P::WIDTH..self.width()).map(move |c| self.get(r, c));
        (packed, sfx)
    }

    /// Zero padded.
    fn padded_horizontally_packed_row<'a, P>(
        &'a self,
        r: usize,
    ) -> impl Iterator<Item = P> + Send + Sync
    where
        P: PackedValue<Value = T>,
        T: Clone + Default + 'a,
    {
        let mut row_iter = self.row(r);
        let num_elems = self.width().div_ceil(P::WIDTH);
        // array::from_fn currently always calls in order, but it's not clear whether that's guaranteed.
        (0..num_elems).map(move |_| P::from_fn(|_| row_iter.next().unwrap_or_default()))
    }

    fn par_horizontally_packed_rows<'a, P>(
        &'a self,
    ) -> impl IndexedParallelIterator<
        Item = (
            impl Iterator<Item = P> + Send + Sync,
            impl Iterator<Item = T> + Send + Sync,
        ),
    >
    where
        P: PackedValue<Value = T>,
        T: Clone + 'a,
    {
        (0..self.height())
            .into_par_iter()
            .map(|r| self.horizontally_packed_row(r))
    }

    fn par_padded_horizontally_packed_rows<'a, P>(
        &'a self,
    ) -> impl IndexedParallelIterator<Item = impl Iterator<Item = P> + Send + Sync>
    where
        P: PackedValue<Value = T>,
        T: Clone + Default + 'a,
    {
        (0..self.height())
            .into_par_iter()
            .map(|r| self.padded_horizontally_packed_row(r))
    }

    /// Pack together a collection of adjacent rows from the matrix.
    ///
    /// Returns an iterator whose i'th element is packing of the i'th element of the
    /// rows r through r + P::WIDTH - 1. If we exceed the height of the matrix,
    /// wrap around and include initial rows.
    #[inline]
    fn vertically_packed_row<P>(&self, r: usize) -> impl Iterator<Item = P>
    where
        T: Copy,
        P: PackedValue<Value = T>,
    {
        let rows = (0..(P::WIDTH))
            .map(|c| self.row_slice((r + c) % self.height()))
            .collect_vec();
        (0..self.width()).map(move |c| P::from_fn(|i| rows[i][c]))
    }

    /// Pack together a collection of rows and "next" rows from the matrix.
    ///
    /// Returns a vector corresponding to 2 packed rows. The i'th element of the first
    /// row contains the packing of the i'th element of the rows r through r + P::WIDTH - 1.
    /// The i'th element of the second row contains the packing of the i'th element of the
    /// rows r + step through r + step + P::WIDTH - 1. If at some point we exceed the
    /// height of the matrix, wrap around and include initial rows.
    #[inline]
    fn vertically_packed_row_pair<P>(&self, r: usize, step: usize) -> Vec<P>
    where
        T: Copy,
        P: PackedValue<Value = T>,
    {
        // Whilst it would appear that this can be replaced by two calls to vertically_packed_row
        // tests seem to indicate that combining them in the same function is slightly faster.
        // It's probably allowing the compiler to make some optimizations on the fly.

        let rows = (0..P::WIDTH)
            .map(|c| self.row_slice((r + c) % self.height()))
            .collect_vec();

        let next_rows = (0..P::WIDTH)
            .map(|c| self.row_slice((r + c + step) % self.height()))
            .collect_vec();

        (0..self.width())
            .map(|c| P::from_fn(|i| rows[i][c]))
            .chain((0..self.width()).map(|c| P::from_fn(|i| next_rows[i][c])))
            .collect_vec()
    }

    fn vertically_strided(self, stride: usize, offset: usize) -> VerticallyStridedMatrixView<Self>
    where
        Self: Sized,
    {
        VerticallyStridedRowIndexMap::new_view(self, stride, offset)
    }

    /// Compute Mᵀv, aka premultiply this matrix by the given vector,
    /// aka scale each row by the corresponding entry in `v` and take the sum across rows.
    /// `v` can be a vector of extension elements.
    #[instrument(level = "debug", skip_all, fields(dims = %self.dimensions()))]
    fn columnwise_dot_product<EF>(&self, v: &[EF]) -> Vec<EF>
    where
        T: Field,
        EF: ExtensionField<T>,
    {
        let packed_width = self.width().div_ceil(T::Packing::WIDTH);

        let packed_result = self
            .par_padded_horizontally_packed_rows::<T::Packing>()
            .zip(v)
            .par_fold_reduce(
                || EF::ExtensionPacking::zero_vec(packed_width),
                |mut acc, (row, &scale)| {
                    let scale = EF::ExtensionPacking::from_base_fn(|i| {
                        T::Packing::from(scale.as_base_slice()[i])
                    });
                    izip!(&mut acc, row).for_each(|(l, r)| *l += scale * r);
                    acc
                },
                |mut acc_l, acc_r| {
                    izip!(&mut acc_l, acc_r).for_each(|(l, r)| *l += r);
                    acc_l
                },
            );

        packed_result
            .into_iter()
            .flat_map(|p| {
                (0..T::Packing::WIDTH)
                    .map(move |i| EF::from_base_fn(|j| p.as_base_slice()[j].as_slice()[i]))
            })
            .take(self.width())
            .collect()
    }

    /// Multiply this matrix by the vector of powers of `base`, which is an extension element.
    fn dot_ext_powers<EF>(&self, base: EF) -> impl IndexedParallelIterator<Item = EF>
    where
        T: Field,
        EF: ExtensionField<T>,
    {
        let powers_packed = base
            .ext_powers_packed()
            .take(self.width().next_multiple_of(T::Packing::WIDTH))
            .collect_vec();
        self.par_padded_horizontally_packed_rows::<T::Packing>()
            .map(move |row_packed| {
                let packed_sum_of_packed: EF::ExtensionPacking =
                    dot_product(powers_packed.iter().copied(), row_packed);
                let sum_of_packed: EF = EF::from_base_fn(|i| {
                    packed_sum_of_packed.as_base_slice()[i]
                        .as_slice()
                        .iter()
                        .copied()
                        .sum()
                });
                sum_of_packed
            })
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec::Vec;
    use alloc::{format, vec};

    use itertools::izip;
    use p3_baby_bear::BabyBear;
    use p3_field::extension::BinomialExtensionField;
    use p3_field::FieldAlgebra;
    use rand::thread_rng;

    use super::*;

    #[test]
    fn test_columnwise_dot_product() {
        type F = BabyBear;
        type EF = BinomialExtensionField<BabyBear, 4>;

        let m = RowMajorMatrix::<F>::rand(&mut thread_rng(), 1 << 8, 1 << 4);
        let v = RowMajorMatrix::<EF>::rand(&mut thread_rng(), 1 << 8, 1).values;

        let mut expected = vec![EF::ZERO; m.width()];
        for (row, &scale) in izip!(m.rows(), &v) {
            for (l, r) in izip!(&mut expected, row) {
                *l += scale * r;
            }
        }

        assert_eq!(m.columnwise_dot_product(&v), expected);
    }

    // Mock implementation for testing purposes
    struct MockMatrix {
        data: Vec<Vec<u32>>,
        width: usize,
        height: usize,
    }

    impl Matrix<u32> for MockMatrix {
        type Row<'a> = alloc::vec::IntoIter<u32>;

        fn width(&self) -> usize {
            self.width
        }

        fn height(&self) -> usize {
            self.height
        }

        fn row(&self, r: usize) -> Self::Row<'_> {
            self.data[r].clone().into_iter()
        }
    }

    #[test]
    fn test_dimensions() {
        let dims = Dimensions {
            width: 3,
            height: 5,
        };
        assert_eq!(dims.width, 3);
        assert_eq!(dims.height, 5);
        assert_eq!(format!("{:?}", dims), "3x5");
        assert_eq!(format!("{}", dims), "3x5");
    }

    #[test]
    fn test_mock_matrix_dimensions() {
        let matrix = MockMatrix {
            data: vec![vec![1, 2, 3], vec![4, 5, 6], vec![7, 8, 9]],
            width: 3,
            height: 3,
        };
        assert_eq!(matrix.width(), 3);
        assert_eq!(matrix.height(), 3);
        assert_eq!(
            matrix.dimensions(),
            Dimensions {
                width: 3,
                height: 3
            }
        );
    }

    #[test]
    fn test_first_row() {
        let matrix = MockMatrix {
            data: vec![vec![1, 2, 3], vec![4, 5, 6], vec![7, 8, 9]],
            width: 3,
            height: 3,
        };
        let mut first_row = matrix.first_row();
        assert_eq!(first_row.next(), Some(1));
        assert_eq!(first_row.next(), Some(2));
        assert_eq!(first_row.next(), Some(3));
    }

    #[test]
    fn test_last_row() {
        let matrix = MockMatrix {
            data: vec![vec![1, 2, 3], vec![4, 5, 6], vec![7, 8, 9]],
            width: 3,
            height: 3,
        };
        let mut last_row = matrix.last_row();
        assert_eq!(last_row.next(), Some(7));
        assert_eq!(last_row.next(), Some(8));
        assert_eq!(last_row.next(), Some(9));
    }

    #[test]
    fn test_row_slice() {
        let matrix = MockMatrix {
            data: vec![vec![1, 2, 3], vec![4, 5, 6], vec![7, 8, 9]],
            width: 3,
            height: 3,
        };
        let row_slice = matrix.row_slice(1);
        assert_eq!(row_slice.deref(), &[4, 5, 6]);
    }

    #[test]
    fn test_to_row_major_matrix() {
        let matrix = MockMatrix {
            data: vec![vec![1, 2], vec![3, 4]],
            width: 2,
            height: 2,
        };
        let row_major = matrix.to_row_major_matrix();
        assert_eq!(row_major.values, vec![1, 2, 3, 4]);
        assert_eq!(row_major.width, 2);
    }

    #[test]
    fn test_matrix_get() {
        let matrix = MockMatrix {
            data: vec![vec![1, 2, 3], vec![4, 5, 6], vec![7, 8, 9]],
            width: 3,
            height: 3,
        };
        assert_eq!(matrix.get(0, 0), 1);
        assert_eq!(matrix.get(1, 2), 6);
        assert_eq!(matrix.get(2, 1), 8);
    }

    #[test]
    fn test_matrix_row_iteration() {
        let matrix = MockMatrix {
            data: vec![vec![1, 2, 3], vec![4, 5, 6], vec![7, 8, 9]],
            width: 3,
            height: 3,
        };

        let mut row_iter = matrix.row(1);
        assert_eq!(row_iter.next(), Some(4));
        assert_eq!(row_iter.next(), Some(5));
        assert_eq!(row_iter.next(), Some(6));
        assert_eq!(row_iter.next(), None);
    }

    #[test]
    fn test_matrix_rows() {
        let matrix = MockMatrix {
            data: vec![vec![1, 2, 3], vec![4, 5, 6], vec![7, 8, 9]],
            width: 3,
            height: 3,
        };

        let all_rows: Vec<Vec<u32>> = matrix.rows().map(|row| row.collect()).collect();
        assert_eq!(all_rows, vec![vec![1, 2, 3], vec![4, 5, 6], vec![7, 8, 9]]);
    }
}
