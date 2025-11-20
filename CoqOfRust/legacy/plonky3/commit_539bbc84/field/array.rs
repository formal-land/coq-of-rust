use core::array;
use core::iter::{Product, Sum};
use core::ops::{Add, AddAssign, Div, Mul, MulAssign, Neg, Sub, SubAssign};

use crate::batch_inverse::batch_multiplicative_inverse_general;
use crate::{Field, FieldAlgebra, PackedValue};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(transparent)] // This needed to make `transmute`s safe.
pub struct FieldArray<F: Field, const N: usize>(pub [F; N]);

impl<F: Field, const N: usize> FieldArray<F, N> {
    pub(crate) fn inverse(&self) -> Self {
        let mut result = Self::default();
        batch_multiplicative_inverse_general(&self.0, &mut result.0, |x| x.inverse());
        result
    }
}

impl<F: Field, const N: usize> Default for FieldArray<F, N> {
    fn default() -> Self {
        Self::ZERO
    }
}

impl<F: Field, const N: usize> From<F> for FieldArray<F, N> {
    fn from(val: F) -> Self {
        [val; N].into()
    }
}

impl<F: Field, const N: usize> From<[F; N]> for FieldArray<F, N> {
    fn from(arr: [F; N]) -> Self {
        Self(arr)
    }
}

impl<F: Field, const N: usize> FieldAlgebra for FieldArray<F, N> {
    type F = F;

    const ZERO: Self = FieldArray([F::ZERO; N]);
    const ONE: Self = FieldArray([F::ONE; N]);
    const TWO: Self = FieldArray([F::TWO; N]);
    const NEG_ONE: Self = FieldArray([F::NEG_ONE; N]);

    #[inline]
    fn from_f(f: Self::F) -> Self {
        f.into()
    }

    fn from_canonical_u8(n: u8) -> Self {
        [F::from_canonical_u8(n); N].into()
    }

    fn from_canonical_u16(n: u16) -> Self {
        [F::from_canonical_u16(n); N].into()
    }

    fn from_canonical_u32(n: u32) -> Self {
        [F::from_canonical_u32(n); N].into()
    }

    fn from_canonical_u64(n: u64) -> Self {
        [F::from_canonical_u64(n); N].into()
    }

    fn from_canonical_usize(n: usize) -> Self {
        [F::from_canonical_usize(n); N].into()
    }

    fn from_wrapped_u32(n: u32) -> Self {
        [F::from_wrapped_u32(n); N].into()
    }

    fn from_wrapped_u64(n: u64) -> Self {
        [F::from_wrapped_u64(n); N].into()
    }
}

unsafe impl<F: Field, const N: usize> PackedValue for FieldArray<F, N> {
    type Value = F;

    const WIDTH: usize = N;

    fn from_slice(slice: &[Self::Value]) -> &Self {
        assert_eq!(slice.len(), Self::WIDTH);
        unsafe { &*slice.as_ptr().cast() }
    }

    fn from_slice_mut(slice: &mut [Self::Value]) -> &mut Self {
        assert_eq!(slice.len(), Self::WIDTH);
        unsafe { &mut *slice.as_mut_ptr().cast() }
    }

    fn from_fn<Fn>(f: Fn) -> Self
    where
        Fn: FnMut(usize) -> Self::Value,
    {
        Self(array::from_fn(f))
    }

    fn as_slice(&self) -> &[Self::Value] {
        &self.0
    }

    fn as_slice_mut(&mut self) -> &mut [Self::Value] {
        &mut self.0
    }
}

impl<F: Field, const N: usize> Add for FieldArray<F, N> {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        array::from_fn(|i| self.0[i] + rhs.0[i]).into()
    }
}

impl<F: Field, const N: usize> Add<F> for FieldArray<F, N> {
    type Output = Self;

    #[inline]
    fn add(self, rhs: F) -> Self::Output {
        self.0.map(|x| x + rhs).into()
    }
}

impl<F: Field, const N: usize> AddAssign for FieldArray<F, N> {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        self.0.iter_mut().zip(rhs.0).for_each(|(x, y)| *x += y);
    }
}

impl<F: Field, const N: usize> AddAssign<F> for FieldArray<F, N> {
    #[inline]
    fn add_assign(&mut self, rhs: F) {
        self.0.iter_mut().for_each(|x| *x += rhs);
    }
}

impl<F: Field, const N: usize> Sub for FieldArray<F, N> {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        array::from_fn(|i| self.0[i] - rhs.0[i]).into()
    }
}

impl<F: Field, const N: usize> Sub<F> for FieldArray<F, N> {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: F) -> Self::Output {
        self.0.map(|x| x - rhs).into()
    }
}

impl<F: Field, const N: usize> SubAssign for FieldArray<F, N> {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        self.0.iter_mut().zip(rhs.0).for_each(|(x, y)| *x -= y);
    }
}

impl<F: Field, const N: usize> SubAssign<F> for FieldArray<F, N> {
    #[inline]
    fn sub_assign(&mut self, rhs: F) {
        self.0.iter_mut().for_each(|x| *x -= rhs);
    }
}

impl<F: Field, const N: usize> Neg for FieldArray<F, N> {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self::Output {
        self.0.map(|x| -x).into()
    }
}

impl<F: Field, const N: usize> Mul for FieldArray<F, N> {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: Self) -> Self::Output {
        array::from_fn(|i| self.0[i] * rhs.0[i]).into()
    }
}

impl<F: Field, const N: usize> Mul<F> for FieldArray<F, N> {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: F) -> Self::Output {
        self.0.map(|x| x * rhs).into()
    }
}

impl<F: Field, const N: usize> MulAssign for FieldArray<F, N> {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        self.0.iter_mut().zip(rhs.0).for_each(|(x, y)| *x *= y);
    }
}

impl<F: Field, const N: usize> MulAssign<F> for FieldArray<F, N> {
    #[inline]
    fn mul_assign(&mut self, rhs: F) {
        self.0.iter_mut().for_each(|x| *x *= rhs);
    }
}

impl<F: Field, const N: usize> Div<F> for FieldArray<F, N> {
    type Output = Self;

    #[allow(clippy::suspicious_arithmetic_impl)]
    #[inline]
    fn div(self, rhs: F) -> Self::Output {
        let rhs_inv = rhs.inverse();
        self * rhs_inv
    }
}

impl<F: Field, const N: usize> Sum for FieldArray<F, N> {
    #[inline]
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|lhs, rhs| lhs + rhs).unwrap_or(Self::ZERO)
    }
}

impl<F: Field, const N: usize> Product for FieldArray<F, N> {
    #[inline]
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|lhs, rhs| lhs * rhs).unwrap_or(Self::ONE)
    }
}
