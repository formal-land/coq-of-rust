use alloc::format;
use alloc::string::ToString;
use alloc::vec::Vec;
use core::array;
use core::fmt::{self, Debug, Display, Formatter};
use core::iter::{Product, Sum};
use core::marker::PhantomData;
use core::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use itertools::Itertools;
use num_bigint::BigUint;
use p3_util::{flatten_to_base, reconstitute_from_base};
use rand::distr::StandardUniform;
use rand::prelude::Distribution;
use serde::{Deserialize, Serialize};

use super::{HasFrobenius, HasTwoAdicBinomialExtension, PackedBinomialExtensionField};
use crate::extension::BinomiallyExtendable;
use crate::field::Field;
use crate::{
    Algebra, BasedVectorSpace, ExtensionField, Packable, PrimeCharacteristicRing, TwoAdicField,
    field_to_array,
};

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Serialize, Deserialize, PartialOrd, Ord)]
#[repr(transparent)] // Needed to make various casts safe.
pub struct BinomialExtensionField<F, const D: usize, A = F> {
    #[serde(
        with = "p3_util::array_serialization",
        bound(serialize = "A: Serialize", deserialize = "A: Deserialize<'de>")
    )]
    pub(crate) value: [A; D],
    _phantom: PhantomData<F>,
}

impl<F, A, const D: usize> BinomialExtensionField<F, D, A> {
    pub(crate) const fn new(value: [A; D]) -> Self {
        Self {
            value,
            _phantom: PhantomData,
        }
    }
}

impl<F: Field, A: Algebra<F>, const D: usize> Default for BinomialExtensionField<F, D, A> {
    fn default() -> Self {
        Self::new(array::from_fn(|_| A::ZERO))
    }
}

impl<F: Field, A: Algebra<F>, const D: usize> From<A> for BinomialExtensionField<F, D, A> {
    fn from(x: A) -> Self {
        Self::new(field_to_array(x))
    }
}

impl<F: BinomiallyExtendable<D>, const D: usize> Packable for BinomialExtensionField<F, D> {}

impl<F: BinomiallyExtendable<D>, A: Algebra<F>, const D: usize> BasedVectorSpace<A>
    for BinomialExtensionField<F, D, A>
{
    const DIMENSION: usize = D;

    #[inline]
    fn as_basis_coefficients_slice(&self) -> &[A] {
        &self.value
    }

    #[inline]
    fn from_basis_coefficients_fn<Fn: FnMut(usize) -> A>(f: Fn) -> Self {
        Self::new(array::from_fn(f))
    }

    #[inline]
    fn from_basis_coefficients_iter<I: ExactSizeIterator<Item = A>>(mut iter: I) -> Option<Self> {
        (iter.len() == D).then(|| Self::new(array::from_fn(|_| iter.next().unwrap()))) // The unwrap is safe as we just checked the length of iter.
    }

    #[inline]
    fn flatten_to_base(vec: Vec<Self>) -> Vec<A> {
        unsafe {
            // Safety:
            // As `Self` is a `repr(transparent)`, it is stored identically in memory to `[A; D]`
            flatten_to_base::<A, Self>(vec)
        }
    }

    #[inline]
    fn reconstitute_from_base(vec: Vec<A>) -> Vec<Self> {
        unsafe {
            // Safety:
            // As `Self` is a `repr(transparent)`, it is stored identically in memory to `[A; D]`
            reconstitute_from_base::<A, Self>(vec)
        }
    }
}

impl<F: BinomiallyExtendable<D>, const D: usize> ExtensionField<F>
    for BinomialExtensionField<F, D>
{
    type ExtensionPacking = PackedBinomialExtensionField<F, F::Packing, D>;

    #[inline]
    fn is_in_basefield(&self) -> bool {
        self.value[1..].iter().all(F::is_zero)
    }

    #[inline]
    fn as_base(&self) -> Option<F> {
        <Self as ExtensionField<F>>::is_in_basefield(self).then(|| self.value[0])
    }
}

impl<F: BinomiallyExtendable<D>, const D: usize> HasFrobenius<F> for BinomialExtensionField<F, D> {
    /// FrobeniusField automorphisms: x -> x^n, where n is the order of BaseField.
    #[inline]
    fn frobenius(&self) -> Self {
        self.repeated_frobenius(1)
    }

    /// Repeated Frobenius automorphisms: x -> x^(n^count).
    ///
    /// Follows precomputation suggestion in Section 11.3.3 of the
    /// Handbook of Elliptic and Hyperelliptic Curve Cryptography.
    #[inline]
    fn repeated_frobenius(&self, count: usize) -> Self {
        if count == 0 {
            return *self;
        } else if count >= D {
            // x |-> x^(n^D) is the identity, so x^(n^count) ==
            // x^(n^(count % D))
            return self.repeated_frobenius(count % D);
        }

        // z0 = DTH_ROOT^count = W^(k * count) where k = floor((n-1)/D)
        let z0 = F::DTH_ROOT.exp_u64(count as u64);

        let mut res = Self::ZERO;
        for (i, z) in z0.powers().take(D).enumerate() {
            res.value[i] = self.value[i] * z;
        }

        res
    }

    /// Algorithm 11.3.4 in Handbook of Elliptic and Hyperelliptic Curve Cryptography.
    #[inline]
    fn frobenius_inv(&self) -> Self {
        // Writing 'a' for self, we need to compute a^(r-1):
        // r = n^D-1/n-1 = n^(D-1)+n^(D-2)+...+n
        let mut f = Self::ONE;
        for _ in 1..D {
            f = (f * *self).frobenius();
        }

        // g = a^r is in the base field, so only compute that
        // coefficient rather than the full product.
        let a = self.value;
        let b = f.value;
        let mut g = F::ZERO;
        for i in 1..D {
            g += a[i] * b[D - i];
        }
        g *= F::W;
        g += a[0] * b[0];
        debug_assert_eq!(Self::from(g), *self * f);

        f * g.inverse()
    }
}

impl<F, A, const D: usize> PrimeCharacteristicRing for BinomialExtensionField<F, D, A>
where
    F: BinomiallyExtendable<D>,
    A: Algebra<F>,
{
    type PrimeSubfield = <A as PrimeCharacteristicRing>::PrimeSubfield;

    const ZERO: Self = Self::new([A::ZERO; D]);

    const ONE: Self = Self::new(field_to_array(A::ONE));

    const TWO: Self = Self::new(field_to_array(A::TWO));

    const NEG_ONE: Self = Self::new(field_to_array(A::NEG_ONE));

    #[inline]
    fn from_prime_subfield(f: Self::PrimeSubfield) -> Self {
        <A as PrimeCharacteristicRing>::from_prime_subfield(f).into()
    }

    #[inline(always)]
    fn square(&self) -> Self {
        match D {
            2 => {
                let a = self.value.clone();
                let mut res = Self::default();
                res.value[0] = a[0].square() + a[1].square() * F::W;
                res.value[1] = a[0].clone() * a[1].double();
                res
            }
            3 => {
                let mut res = Self::default();
                cubic_square(&self.value, &mut res.value);
                res
            }
            _ => <Self as Mul<Self>>::mul(self.clone(), self.clone()),
        }
    }

    #[inline]
    fn mul_2exp_u64(&self, exp: u64) -> Self {
        Self::new(self.value.clone().map(|x| x.mul_2exp_u64(exp)))
    }

    #[inline]
    fn zero_vec(len: usize) -> Vec<Self> {
        // SAFETY: this is a repr(transparent) wrapper around an array.
        unsafe { reconstitute_from_base(F::zero_vec(len * D)) }
    }
}

impl<F: BinomiallyExtendable<D>, const D: usize> Algebra<F> for BinomialExtensionField<F, D> {}

impl<F: BinomiallyExtendable<D>, const D: usize> Field for BinomialExtensionField<F, D> {
    type Packing = Self;

    const GENERATOR: Self = Self::new(F::EXT_GENERATOR);

    fn try_inverse(&self) -> Option<Self> {
        if self.is_zero() {
            return None;
        }

        let mut res = Self::default();

        match D {
            2 => quadratic_inv(&self.value, &mut res.value, F::W),
            3 => cubic_inv(&self.value, &mut res.value, F::W),
            _ => res = self.frobenius_inv(),
        }

        Some(res)
    }

    #[inline]
    fn halve(&self) -> Self {
        Self::new(self.value.map(|x| x.halve()))
    }

    #[inline]
    fn div_2exp_u64(&self, exp: u64) -> Self {
        Self::new(self.value.map(|x| x.div_2exp_u64(exp)))
    }

    #[inline]
    fn order() -> BigUint {
        F::order().pow(D as u32)
    }
}

impl<F, const D: usize> Display for BinomialExtensionField<F, D>
where
    F: BinomiallyExtendable<D>,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if self.is_zero() {
            write!(f, "0")
        } else {
            let str = self
                .value
                .iter()
                .enumerate()
                .filter(|(_, x)| !x.is_zero())
                .map(|(i, x)| match (i, x.is_one()) {
                    (0, _) => format!("{x}"),
                    (1, true) => "X".to_string(),
                    (1, false) => format!("{x} X"),
                    (_, true) => format!("X^{i}"),
                    (_, false) => format!("{x} X^{i}"),
                })
                .join(" + ");
            write!(f, "{}", str)
        }
    }
}

impl<F, A, const D: usize> Neg for BinomialExtensionField<F, D, A>
where
    F: BinomiallyExtendable<D>,
    A: Algebra<F>,
{
    type Output = Self;

    #[inline]
    fn neg(self) -> Self {
        Self::new(self.value.map(A::neg))
    }
}

impl<F, A, const D: usize> Add for BinomialExtensionField<F, D, A>
where
    F: BinomiallyExtendable<D>,
    A: Algebra<F>,
{
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self {
        let value = vector_add(&self.value, &rhs.value);
        Self::new(value)
    }
}

impl<F, A, const D: usize> Add<A> for BinomialExtensionField<F, D, A>
where
    F: BinomiallyExtendable<D>,
    A: Algebra<F>,
{
    type Output = Self;

    #[inline]
    fn add(mut self, rhs: A) -> Self {
        self.value[0] += rhs;
        self
    }
}

impl<F, A, const D: usize> AddAssign for BinomialExtensionField<F, D, A>
where
    F: BinomiallyExtendable<D>,
    A: Algebra<F>,
{
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        for i in 0..D {
            self.value[i] += rhs.value[i].clone();
        }
    }
}

impl<F, A, const D: usize> AddAssign<A> for BinomialExtensionField<F, D, A>
where
    F: BinomiallyExtendable<D>,
    A: Algebra<F>,
{
    #[inline]
    fn add_assign(&mut self, rhs: A) {
        self.value[0] += rhs;
    }
}

impl<F, A, const D: usize> Sum for BinomialExtensionField<F, D, A>
where
    F: BinomiallyExtendable<D>,
    A: Algebra<F>,
{
    #[inline]
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|acc, x| acc + x).unwrap_or(Self::ZERO)
    }
}

impl<F, A, const D: usize> Sub for BinomialExtensionField<F, D, A>
where
    F: BinomiallyExtendable<D>,
    A: Algebra<F>,
{
    type Output = Self;

    #[inline]
    fn sub(self, rhs: Self) -> Self {
        let value = vector_sub(&self.value, &rhs.value);
        Self::new(value)
    }
}

impl<F, A, const D: usize> Sub<A> for BinomialExtensionField<F, D, A>
where
    F: BinomiallyExtendable<D>,
    A: Algebra<F>,
{
    type Output = Self;

    #[inline]
    fn sub(self, rhs: A) -> Self {
        let mut res = self.value;
        res[0] -= rhs;
        Self::new(res)
    }
}

impl<F, A, const D: usize> SubAssign for BinomialExtensionField<F, D, A>
where
    F: BinomiallyExtendable<D>,
    A: Algebra<F>,
{
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        for i in 0..D {
            self.value[i] -= rhs.value[i].clone();
        }
    }
}

impl<F, A, const D: usize> SubAssign<A> for BinomialExtensionField<F, D, A>
where
    F: BinomiallyExtendable<D>,
    A: Algebra<F>,
{
    #[inline]
    fn sub_assign(&mut self, rhs: A) {
        self.value[0] -= rhs;
    }
}

impl<F, A, const D: usize> Mul for BinomialExtensionField<F, D, A>
where
    F: BinomiallyExtendable<D>,
    A: Algebra<F>,
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

impl<F, A, const D: usize> Mul<A> for BinomialExtensionField<F, D, A>
where
    F: BinomiallyExtendable<D>,
    A: Algebra<F>,
{
    type Output = Self;

    #[inline]
    fn mul(self, rhs: A) -> Self {
        Self::new(self.value.map(|x| x * rhs.clone()))
    }
}

impl<F, A, const D: usize> MulAssign for BinomialExtensionField<F, D, A>
where
    F: BinomiallyExtendable<D>,
    A: Algebra<F>,
{
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = self.clone() * rhs;
    }
}

impl<F, A, const D: usize> MulAssign<A> for BinomialExtensionField<F, D, A>
where
    F: BinomiallyExtendable<D>,
    A: Algebra<F>,
{
    #[inline]
    fn mul_assign(&mut self, rhs: A) {
        *self = self.clone() * rhs;
    }
}

impl<F, A, const D: usize> Product for BinomialExtensionField<F, D, A>
where
    F: BinomiallyExtendable<D>,
    A: Algebra<F>,
{
    #[inline]
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.reduce(|acc, x| acc * x).unwrap_or(Self::ONE)
    }
}

impl<F, const D: usize> Div for BinomialExtensionField<F, D>
where
    F: BinomiallyExtendable<D>,
{
    type Output = Self;

    #[allow(clippy::suspicious_arithmetic_impl)]
    #[inline]
    fn div(self, rhs: Self) -> Self::Output {
        self * rhs.inverse()
    }
}

impl<F, const D: usize> DivAssign for BinomialExtensionField<F, D>
where
    F: BinomiallyExtendable<D>,
{
    #[inline]
    fn div_assign(&mut self, rhs: Self) {
        *self = *self / rhs;
    }
}

impl<F: BinomiallyExtendable<D>, const D: usize> Distribution<BinomialExtensionField<F, D>>
    for StandardUniform
where
    Self: Distribution<F>,
{
    #[inline]
    fn sample<R: rand::Rng + ?Sized>(&self, rng: &mut R) -> BinomialExtensionField<F, D> {
        BinomialExtensionField::new(array::from_fn(|_| self.sample(rng)))
    }
}

impl<F: Field + HasTwoAdicBinomialExtension<D>, const D: usize> TwoAdicField
    for BinomialExtensionField<F, D>
{
    const TWO_ADICITY: usize = F::EXT_TWO_ADICITY;

    #[inline]
    fn two_adic_generator(bits: usize) -> Self {
        Self::new(F::ext_two_adic_generator(bits))
    }
}

/// Add two vectors element wise.
#[inline]
pub(crate) fn vector_add<
    R: PrimeCharacteristicRing + Add<R2, Output = R>,
    R2: Clone,
    const D: usize,
>(
    a: &[R; D],
    b: &[R2; D],
) -> [R; D] {
    array::from_fn(|i| a[i].clone() + b[i].clone())
}

/// Subtract two vectors element wise.
#[inline]
pub(crate) fn vector_sub<
    R: PrimeCharacteristicRing + Sub<R2, Output = R>,
    R2: Clone,
    const D: usize,
>(
    a: &[R; D],
    b: &[R2; D],
) -> [R; D] {
    array::from_fn(|i| a[i].clone() - b[i].clone())
}

/// Multiply two vectors representing elements in a binomial extension.
#[inline]
pub(super) fn binomial_mul<
    F: Field,
    R: Algebra<F> + Mul<R2, Output = R>,
    R2: Add<Output = R2> + Clone,
    const D: usize,
>(
    a: &[R; D],
    b: &[R2; D],
    res: &mut [R; D],
    w: F,
) {
    match D {
        2 => {
            res[0] = a[0].clone() * b[0].clone() + a[1].clone() * w * b[1].clone();
            res[1] = a[0].clone() * b[1].clone() + a[1].clone() * b[0].clone();
        }
        3 => cubic_mul(a, b, res, w),
        _ =>
        {
            #[allow(clippy::needless_range_loop)]
            for i in 0..D {
                for j in 0..D {
                    if i + j >= D {
                        res[i + j - D] += a[i].clone() * w * b[j].clone();
                    } else {
                        res[i + j] += a[i].clone() * b[j].clone();
                    }
                }
            }
        }
    }
}

///Section 11.3.6b in Handbook of Elliptic and Hyperelliptic Curve Cryptography.
#[inline]
fn quadratic_inv<F: Field, const D: usize>(a: &[F; D], res: &mut [F; D], w: F) {
    assert_eq!(D, 2);
    let scalar = (a[0].square() - w * a[1].square()).inverse();
    res[0] = a[0] * scalar;
    res[1] = -a[1] * scalar;
}

/// Section 11.3.6b in Handbook of Elliptic and Hyperelliptic Curve Cryptography.
#[inline]
fn cubic_inv<F: Field, const D: usize>(a: &[F; D], res: &mut [F; D], w: F) {
    assert_eq!(D, 3);
    let a0_square = a[0].square();
    let a1_square = a[1].square();
    let a2_w = w * a[2];
    let a0_a1 = a[0] * a[1];

    // scalar = (a0^3+wa1^3+w^2a2^3-3wa0a1a2)^-1
    let scalar = (a0_square * a[0] + w * a[1] * a1_square + a2_w.square() * a[2]
        - (F::ONE + F::TWO) * a2_w * a0_a1)
        .inverse();

    //scalar*[a0^2-wa1a2, wa2^2-a0a1, a1^2-a0a2]
    res[0] = scalar * (a0_square - a[1] * a2_w);
    res[1] = scalar * (a2_w * a[2] - a0_a1);
    res[2] = scalar * (a1_square - a[0] * a[2]);
}

/// karatsuba multiplication for cubic extension field
#[inline]
pub(crate) fn cubic_mul<
    F: Field,
    R: Algebra<F> + Mul<R2, Output = R>,
    R2: Add<Output = R2> + Clone,
    const D: usize,
>(
    a: &[R; D],
    b: &[R2; D],
    res: &mut [R; D],
    w: F,
) {
    assert_eq!(D, 3);

    let a0_b0 = a[0].clone() * b[0].clone();
    let a1_b1 = a[1].clone() * b[1].clone();
    let a2_b2 = a[2].clone() * b[2].clone();

    res[0] = a0_b0.clone()
        + ((a[1].clone() + a[2].clone()) * (b[1].clone() + b[2].clone())
            - a1_b1.clone()
            - a2_b2.clone())
            * w;
    res[1] = (a[0].clone() + a[1].clone()) * (b[0].clone() + b[1].clone())
        - a0_b0.clone()
        - a1_b1.clone()
        + a2_b2.clone() * w;
    res[2] = (a[0].clone() + a[2].clone()) * (b[0].clone() + b[2].clone()) - a0_b0 - a2_b2 + a1_b1;
}

/// Section 11.3.6a in Handbook of Elliptic and Hyperelliptic Curve Cryptography.
#[inline]
pub(crate) fn cubic_square<F: BinomiallyExtendable<D>, A: Algebra<F>, const D: usize>(
    a: &[A; D],
    res: &mut [A; D],
) {
    assert_eq!(D, 3);

    let w_a2 = a[2].clone() * F::W;

    res[0] = a[0].square() + (a[1].clone() * w_a2.clone()).double();
    res[1] = w_a2 * a[2].clone() + (a[0].clone() * a[1].clone()).double();
    res[2] = a[1].square() + (a[0].clone() * a[2].clone()).double();
}
