use alloc::vec::Vec;
use core::iter;
use core::marker::PhantomData;
use core::ops::Deref;

use p3_field::{ExtensionField, Field};

use crate::Matrix;

/// Flattens a matrix of extension field elements to one of base field elements. The flattening is
/// done horizontally, resulting in a wider matrix.
#[derive(Debug)]
pub struct FlatMatrixView<F, EF, Inner>(Inner, PhantomData<(F, EF)>);

impl<F, EF, Inner> FlatMatrixView<F, EF, Inner> {
    pub const fn new(inner: Inner) -> Self {
        Self(inner, PhantomData)
    }
}

impl<F, EF, Inner> Deref for FlatMatrixView<F, EF, Inner> {
    type Target = Inner;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<F, EF, Inner> Matrix<F> for FlatMatrixView<F, EF, Inner>
where
    F: Field,
    EF: ExtensionField<F>,
    Inner: Matrix<EF>,
{
    fn width(&self) -> usize {
        self.0.width() * EF::DIMENSION
    }

    fn height(&self) -> usize {
        self.0.height()
    }

    type Row<'a>
        = FlatIter<F, Inner::Row<'a>>
    where
        Self: 'a;

    fn row(&self, r: usize) -> Self::Row<'_> {
        FlatIter {
            inner: self.0.row(r).peekable(),
            idx: 0,
            _phantom: PhantomData,
        }
    }

    fn row_slice(&self, r: usize) -> impl Deref<Target = [F]> {
        self.0
            .row_slice(r)
            .iter()
            .flat_map(|val| val.as_basis_coefficients_slice())
            .copied()
            .collect::<Vec<_>>()
    }
}

pub struct FlatIter<F, I: Iterator> {
    inner: iter::Peekable<I>,
    idx: usize,
    _phantom: PhantomData<F>,
}

impl<F, EF, I> Iterator for FlatIter<F, I>
where
    F: Field,
    EF: ExtensionField<F>,
    I: Iterator<Item = EF>,
{
    type Item = F;
    fn next(&mut self) -> Option<Self::Item> {
        if self.idx == EF::DIMENSION {
            self.idx = 0;
            self.inner.next();
        }
        let value = self.inner.peek()?.as_basis_coefficients_slice()[self.idx];
        self.idx += 1;
        Some(value)
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec;

    use p3_field::extension::Complex;
    use p3_field::{BasedVectorSpace, PrimeCharacteristicRing};
    use p3_mersenne_31::Mersenne31;

    use super::*;
    use crate::dense::RowMajorMatrix;
    type F = Mersenne31;
    type EF = Complex<Mersenne31>;

    #[test]
    fn flat_matrix() {
        let values = vec![
            EF::from_basis_coefficients_fn(|i| F::from_u8(i as u8 + 10)),
            EF::from_basis_coefficients_fn(|i| F::from_u8(i as u8 + 20)),
            EF::from_basis_coefficients_fn(|i| F::from_u8(i as u8 + 30)),
            EF::from_basis_coefficients_fn(|i| F::from_u8(i as u8 + 40)),
        ];
        let ext = RowMajorMatrix::<EF>::new(values, 2);
        let flat = FlatMatrixView::<F, EF, _>::new(ext);
        assert_eq!(&*flat.row_slice(0), &[10, 11, 20, 21].map(F::from_u8));
        assert_eq!(&*flat.row_slice(1), &[30, 31, 40, 41].map(F::from_u8));
    }
}
