use alloc::vec::Vec;
use core::array;
use core::fmt::Debug;
use core::iter::{Product, Sum};
use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use itertools::Itertools;
use p3_util::{flatten_to_base, reconstitute_from_base};
use serde::{Deserialize, Serialize};

use super::{BinomialExtensionField, binomial_mul, cubic_square, vector_add, vector_sub};
use crate::extension::BinomiallyExtendable;
use crate::{
    Algebra, BasedVectorSpace, Field, PackedField, PackedFieldExtension, PackedValue, Powers,
    PrimeCharacteristicRing, field_to_array,
};

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Serialize, Deserialize, PartialOrd, Ord)]
#[repr(transparent)] // Needed to make various casts safe.
pub struct PackedBinomialExtensionField<F: Field, PF: PackedField<Scalar = F>, const D: usize> {
    #[serde(
        with = "p3_util::array_serialization",
        bound(serialize = "PF: Serialize", deserialize = "PF: Deserialize<'de>")
    )]
    pub(crate) value: [PF; D],
}

impl<F: Field, PF: PackedField<Scalar = F>, const D: usize> PackedBinomialExtensionField<F, PF, D> {
    const fn new(value: [PF; D]) -> Self {
        Self { value }
    }
}

impl<F: Field, PF: PackedField<Scalar = F>, const D: usize> Default
    for PackedBinomialExtensionField<F, PF, D>
{
    #[inline]
    fn default() -> Self {
        Self {
            value: array::from_fn(|_| PF::ZERO),
        }
    }
}

impl<F: Field, PF: PackedField<Scalar = F>, const D: usize> From<BinomialExtensionField<F, D>>
    for PackedBinomialExtensionField<F, PF, D>
{
    #[inline]
    fn from(x: BinomialExtensionField<F, D>) -> Self {
        Self {
            value: x.value.map(Into::into),
        }
    }
}

impl<F: Field, PF: PackedField<Scalar = F>, const D: usize> From<PF>
    for PackedBinomialExtensionField<F, PF, D>
{
    #[inline]
    fn from(x: PF) -> Self {
        Self {
            value: field_to_array(x),
        }
    }
}

impl<F: BinomiallyExtendable<D>, PF: PackedField<Scalar = F>, const D: usize>
    Algebra<BinomialExtensionField<F, D>> for PackedBinomialExtensionField<F, PF, D>
{
}

impl<F: BinomiallyExtendable<D>, PF: PackedField<Scalar = F>, const D: usize> Algebra<PF>
    for PackedBinomialExtensionField<F, PF, D>
{
}

impl<F, PF, const D: usize> PrimeCharacteristicRing for PackedBinomialExtensionField<F, PF, D>
where
    F: BinomiallyExtendable<D>,
    PF: PackedField<Scalar = F>,
{
    type PrimeSubfield = PF::PrimeSubfield;

    const ZERO: Self = Self {
        value: [PF::ZERO; D],
    };

    const ONE: Self = Self {
        value: field_to_array(PF::ONE),
    };

    const TWO: Self = Self {
        value: field_to_array(PF::TWO),
    };

    const NEG_ONE: Self = Self {
        value: field_to_array(PF::NEG_ONE),
    };

    #[inline]
    fn from_prime_subfield(val: Self::PrimeSubfield) -> Self {
        PF::from_prime_subfield(val).into()
    }

    #[inline]
    fn from_bool(b: bool) -> Self {
        PF::from_bool(b).into()
    }

    #[inline(always)]
    fn square(&self) -> Self {
        match D {
            2 => {
                let a = self.value;
                let mut res = Self::default();
                res.value[0] = a[0].square() + a[1].square() * F::W;
                res.value[1] = a[0] * a[1].double();
                res
            }
            3 => {
                let mut res = Self::default();
                cubic_square(&self.value, &mut res.value);
                res
            }
            _ => *self * *self,
        }
    }

    #[inline]
    fn zero_vec(len: usize) -> Vec<Self> {
        // SAFETY: this is a repr(transparent) wrapper around an array.
        unsafe { reconstitute_from_base(PF::zero_vec(len * D)) }
    }
}

impl<F, PF, const D: usize> BasedVectorSpace<PF> for PackedBinomialExtensionField<F, PF, D>
where
    F: BinomiallyExtendable<D>,
    PF: PackedField<Scalar = F>,
{
    const DIMENSION: usize = D;

    #[inline]
    fn as_basis_coefficients_slice(&self) -> &[PF] {
        &self.value
    }

    #[inline]
    fn from_basis_coefficients_fn<Fn: FnMut(usize) -> PF>(f: Fn) -> Self {
        Self {
            value: array::from_fn(f),
        }
    }

    #[inline]
    fn from_basis_coefficients_iter<I: ExactSizeIterator<Item = PF>>(mut iter: I) -> Option<Self> {
        (iter.len() == D).then(|| Self::new(array::from_fn(|_| iter.next().unwrap()))) // The unwrap is safe as we just checked the length of iter.
    }

    #[inline]
    fn flatten_to_base(vec: Vec<Self>) -> Vec<PF> {
        unsafe {
            // Safety:
            // As `Self` is a `repr(transparent)`, it is stored identically in memory to `[PF; D]`
            flatten_to_base::<PF, Self>(vec)
        }
    }

    #[inline]
    fn reconstitute_from_base(vec: Vec<PF>) -> Vec<Self> {
        unsafe {
            // Safety:
            // As `Self` is a `repr(transparent)`, it is stored identically in memory to `[PF; D]`
            reconstitute_from_base::<PF, Self>(vec)
        }
    }
}

impl<F, const D: usize> PackedFieldExtension<F, BinomialExtensionField<F, D>>
    for PackedBinomialExtensionField<F, F::Packing, D>
where
    F: BinomiallyExtendable<D>,
{
    #[inline]
    fn from_ext_slice(ext_slice: &[BinomialExtensionField<F, D>]) -> Self {
        let width = F::Packing::WIDTH;
        assert_eq!(ext_slice.len(), width);

        let res = array::from_fn(|i| F::Packing::from_fn(|j| ext_slice[j].value[i]));
        Self::new(res)
    }

    #[inline]
    fn to_ext_iter(
        iter: impl IntoIterator<Item = Self>,
    ) -> impl Iterator<Item = BinomialExtensionField<F, D>> {
        let width = F::Packing::WIDTH;
        iter.into_iter().flat_map(move |x| {
            (0..width).map(move |i| {
                let values = array::from_fn(|j| x.value[j].as_slice()[i]);
                BinomialExtensionField::new(values)
            })
        })
    }

    #[inline]
    fn packed_ext_powers(base: BinomialExtensionField<F, D>) -> crate::Powers<Self> {
        let width = F::Packing::WIDTH;
        let powers = base.powers().take(width + 1).collect_vec();
        // Transpose first WIDTH powers
        let current = Self::from_ext_slice(&powers[..width]);

        // Broadcast self^WIDTH
        let multiplier = powers[width].into();

        Powers {
            base: multiplier,
            current,
        }
    }
}

impl<F, PF, const D: usize> Neg for PackedBinomialExtensionField<F, PF, D>
where
    F: BinomiallyExtendable<D>,
    PF: PackedField<Scalar = F>,
{
    type Output = Self;

    #[inline]
    fn neg(self) -> Self {
        Self {
            value: self.value.map(PF::neg),
        }
    }
}

impl<F, PF, const D: usize> Add for PackedBinomialExtensionField<F, PF, D>
where
    F: BinomiallyExtendable<D>,
    PF: PackedField<Scalar = F>,
{
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self {
        let value = vector_add(&self.value, &rhs.value);
        Self { value }
    }
}

impl<F, PF, const D: usize> Add<BinomialExtensionField<F, D>>
    for PackedBinomialExtensionField<F, PF, D>
where
    F: BinomiallyExtendable<D>,
    PF: PackedField<Scalar = F>,
{
    type Output = Self;

    #[inline]
    fn add(self, rhs: BinomialExtensionField<F, D>) -> Self {
        let value = vector_add(&self.value, &rhs.value);
        Self { value }
    }
}

impl<F, PF, const D: usize> Add<PF> for PackedBinomialExtensionField<F, PF, D>
where
    F: BinomiallyExtendable<D>,
    PF: PackedField<Scalar = F>,
{
    type Output = Self;

    #[inline]
    fn add(mut self, rhs: PF) -> Self {
        self.value[0] += rhs;
        self
    }
}

impl<F, PF, const D: usize> AddAssign for PackedBinomialExtensionField<F, PF, D>
where
    F: BinomiallyExtendable<D>,
    PF: PackedField<Scalar = F>,
{
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        for i in 0..D {
            self.value[i] += rhs.value[i];
        }
    }
}

impl<F, PF, const D: usize> AddAssign<BinomialExtensionField<F, D>>
    for PackedBinomialExtensionField<F, PF, D>
where
    F: BinomiallyExtendable<D>,
    PF: PackedField<Scalar = F>,
{
    #[inline]
    fn add_assign(&mut self, rhs: BinomialExtensionField<F, D>) {
        for i in 0..D {
            self.value[i] += rhs.value[i];
        }
    }
}

impl<F, PF, const D: usize> AddAssign<PF> for PackedBinomialExtensionField<F, PF, D>
where
    F: BinomiallyExtendable<D>,
    PF: PackedField<Scalar = F>,
{
    #[inline]
    fn add_assign(&mut self, rhs: PF) {
        self.value[0] += rhs;
    }
}

impl<F, PF, const D: usize> Sum for PackedBinomialExtensionField<F, PF, D>
where
    F: BinomiallyExtendable<D>,
    PF: PackedField<Scalar = F>,
{
    #[inline]
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|acc, x| acc + x).unwrap_or(Self::ZERO)
    }
}

impl<F, PF, const D: usize> Sub for PackedBinomialExtensionField<F, PF, D>
where
    F: BinomiallyExtendable<D>,
    PF: PackedField<Scalar = F>,
{
    type Output = Self;

    #[inline]
    fn sub(self, rhs: Self) -> Self {
        let value = vector_sub(&self.value, &rhs.value);
        Self { value }
    }
}

impl<F, PF, const D: usize> Sub<BinomialExtensionField<F, D>>
    for PackedBinomialExtensionField<F, PF, D>
where
    F: BinomiallyExtendable<D>,
    PF: PackedField<Scalar = F>,
{
    type Output = Self;

    #[inline]
    fn sub(self, rhs: BinomialExtensionField<F, D>) -> Self {
        let value = vector_sub(&self.value, &rhs.value);
        Self { value }
    }
}

impl<F, PF, const D: usize> Sub<PF> for PackedBinomialExtensionField<F, PF, D>
where
    F: BinomiallyExtendable<D>,
    PF: PackedField<Scalar = F>,
{
    type Output = Self;

    #[inline]
    fn sub(self, rhs: PF) -> Self {
        let mut res = self.value;
        res[0] -= rhs;
        Self { value: res }
    }
}

impl<F, PF, const D: usize> SubAssign for PackedBinomialExtensionField<F, PF, D>
where
    F: BinomiallyExtendable<D>,
    PF: PackedField<Scalar = F>,
{
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl<F, PF, const D: usize> SubAssign<BinomialExtensionField<F, D>>
    for PackedBinomialExtensionField<F, PF, D>
where
    F: BinomiallyExtendable<D>,
    PF: PackedField<Scalar = F>,
{
    #[inline]
    fn sub_assign(&mut self, rhs: BinomialExtensionField<F, D>) {
        *self = *self - rhs;
    }
}

impl<F, PF, const D: usize> SubAssign<PF> for PackedBinomialExtensionField<F, PF, D>
where
    F: BinomiallyExtendable<D>,
    PF: PackedField<Scalar = F>,
{
    #[inline]
    fn sub_assign(&mut self, rhs: PF) {
        *self = *self - rhs;
    }
}

impl<F, PF, const D: usize> Mul for PackedBinomialExtensionField<F, PF, D>
where
    F: BinomiallyExtendable<D>,
    PF: PackedField<Scalar = F>,
{
    type Output = Self;

    #[inline]
    fn mul(self, rhs: Self) -> Self {
        let a = self.value;
        let b = rhs.value;
        let mut res = Self::default();
        let w = F::W;

        binomial_mul(&a, &b, &mut res.value, w);

        res
    }
}

impl<F, PF, const D: usize> Mul<BinomialExtensionField<F, D>>
    for PackedBinomialExtensionField<F, PF, D>
where
    F: BinomiallyExtendable<D>,
    PF: PackedField<Scalar = F>,
{
    type Output = Self;

    #[inline]
    fn mul(self, rhs: BinomialExtensionField<F, D>) -> Self {
        let a = self.value;
        let b = rhs.value;
        let mut res = Self::default();
        let w = F::W;

        binomial_mul(&a, &b, &mut res.value, w);

        res
    }
}

impl<F, PF, const D: usize> Mul<PF> for PackedBinomialExtensionField<F, PF, D>
where
    F: BinomiallyExtendable<D>,
    PF: PackedField<Scalar = F>,
{
    type Output = Self;

    #[inline]
    fn mul(self, rhs: PF) -> Self {
        Self {
            value: self.value.map(|x| x * rhs),
        }
    }
}

impl<F, PF, const D: usize> Product for PackedBinomialExtensionField<F, PF, D>
where
    F: BinomiallyExtendable<D>,
    PF: PackedField<Scalar = F>,
{
    #[inline]
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|acc, x| acc * x).unwrap_or(Self::ZERO)
    }
}

impl<F, PF, const D: usize> MulAssign for PackedBinomialExtensionField<F, PF, D>
where
    F: BinomiallyExtendable<D>,
    PF: PackedField<Scalar = F>,
{
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl<F, PF, const D: usize> MulAssign<BinomialExtensionField<F, D>>
    for PackedBinomialExtensionField<F, PF, D>
where
    F: BinomiallyExtendable<D>,
    PF: PackedField<Scalar = F>,
{
    #[inline]
    fn mul_assign(&mut self, rhs: BinomialExtensionField<F, D>) {
        *self = *self * rhs;
    }
}

impl<F, PF, const D: usize> MulAssign<PF> for PackedBinomialExtensionField<F, PF, D>
where
    F: BinomiallyExtendable<D>,
    PF: PackedField<Scalar = F>,
{
    #[inline]
    fn mul_assign(&mut self, rhs: PF) {
        *self = *self * rhs;
    }
}
