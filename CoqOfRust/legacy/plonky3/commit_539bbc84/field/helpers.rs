use alloc::vec;
use alloc::vec::Vec;
use core::iter::Sum;
use core::mem::{ManuallyDrop, MaybeUninit};
use core::ops::Mul;

use num_bigint::BigUint;
use p3_maybe_rayon::prelude::{IntoParallelRefMutIterator, ParallelIterator};

use crate::field::Field;
use crate::{FieldAlgebra, PackedValue, PrimeField, PrimeField32, TwoAdicField};

/// Computes `Z_H(x)`, where `Z_H` is the zerofier of a multiplicative subgroup of order `2^log_n`.
pub fn two_adic_subgroup_zerofier<F: TwoAdicField>(log_n: usize, x: F) -> F {
    x.exp_power_of_2(log_n) - F::ONE
}

/// Computes `Z_{sH}(x)`, where `Z_{sH}` is the zerofier of the given coset of a multiplicative
/// subgroup of order `2^log_n`.
pub fn two_adic_coset_zerofier<F: TwoAdicField>(log_n: usize, shift: F, x: F) -> F {
    x.exp_power_of_2(log_n) - shift.exp_power_of_2(log_n)
}

/// Computes a multiplicative subgroup whose order is known in advance.
pub fn cyclic_subgroup_known_order<F: Field>(
    generator: F,
    order: usize,
) -> impl Iterator<Item = F> + Clone {
    generator.powers().take(order)
}

/// Computes a coset of a multiplicative subgroup whose order is known in advance.
pub fn cyclic_subgroup_coset_known_order<F: Field>(
    generator: F,
    shift: F,
    order: usize,
) -> impl Iterator<Item = F> + Clone {
    generator.shifted_powers(shift).take(order)
}

#[must_use]
pub fn add_vecs<F: Field>(v: Vec<F>, w: Vec<F>) -> Vec<F> {
    assert_eq!(v.len(), w.len());
    v.into_iter().zip(w).map(|(x, y)| x + y).collect()
}

pub fn sum_vecs<F: Field, I: Iterator<Item = Vec<F>>>(iter: I) -> Vec<F> {
    iter.reduce(|v, w| add_vecs(v, w))
        .expect("sum_vecs: empty iterator")
}

pub fn scale_vec<F: Field>(s: F, vec: Vec<F>) -> Vec<F> {
    vec.into_iter().map(|x| s * x).collect()
}

pub fn scale_slice_in_place<F: Field>(s: F, slice: &mut [F]) {
    let (packed, sfx) = F::Packing::pack_slice_with_suffix_mut(slice);
    let packed_s: F::Packing = s.into();
    packed.par_iter_mut().for_each(|x| *x *= packed_s);
    sfx.iter_mut().for_each(|x| *x *= s);
}

/// `x += y * s`, where `s` is a scalar.
pub fn add_scaled_slice_in_place<F, Y>(x: &mut [F], y: Y, s: F)
where
    F: Field,
    Y: Iterator<Item = F>,
{
    // TODO: Use PackedField
    x.iter_mut().zip(y).for_each(|(x_i, y_i)| *x_i += y_i * s);
}

// The ideas for the following work around come from the construe crate along with
// the playground example linked in the following comment:
// https://github.com/rust-lang/rust/issues/115403#issuecomment-1701000117

// The goal is to want to make field_to_array a const function in order
// to allow us to convert FA constants to BinomialExtensionField<FA, D> constants.
//
// The natural approach would be:
// fn field_to_array<FA: FieldAlgebra, const D: usize>(x: FA) -> [FA; D]
//      let mut arr: [FA; D] = [FA::ZERO; D];
//      arr[0] = x
//      arr
//
// Unfortunately this doesn't compile as FA does not implement Copy and so instead
// implements Drop which cannot be run in constant contexts. Clearly nothing should
// actually be dropped by the above function but the compiler is unable to determine this.
// There is a rust issue for this: https://github.com/rust-lang/rust/issues/73255
// but it seems unlikely to be stabilized anytime soon.
//
// The natural workaround for this is to use MaybeUninit and set each element of the list
// separately. This mostly works but we end up with an array of the form [MaybeUninit<T>; N]
// and there is not currently a way in the standard library to convert this to [T; N].
// There is a method on nightly: array_assume_init so this function should be reworked after
// that has stabilized (More details in Rust issue: https://github.com/rust-lang/rust/issues/96097).
//
// Annoyingly, both transmute and transmute_copy fail here. The first because it cannot handle
// const generics and the second due to interior mutability and the unability to use &mut in const
// functions.
//
// The solution is to implement the map [MaybeUninit<T>; D]) -> MaybeUninit<[T; D]>
// using Union types and ManuallyDrop to essentially do a manual transmute.

union HackyWorkAround<T, const D: usize> {
    complete: ManuallyDrop<MaybeUninit<[T; D]>>,
    elements: ManuallyDrop<[MaybeUninit<T>; D]>,
}

impl<T, const D: usize> HackyWorkAround<T, D> {
    const fn transpose(arr: [MaybeUninit<T>; D]) -> MaybeUninit<[T; D]> {
        // This is safe as [MaybeUninit<T>; D]> and MaybeUninit<[T; D]> are
        // the same type regardless of T. Both are an array or size equal to [T; D]
        // with some data potentially not initialized.
        let transpose = Self {
            elements: ManuallyDrop::new(arr),
        };
        unsafe { ManuallyDrop::into_inner(transpose.complete) }
    }
}

/// Extend a field `FA` element `x` to an array of length `D`
/// by filling zeros.
#[inline]
pub const fn field_to_array<FA: FieldAlgebra, const D: usize>(x: FA) -> [FA; D] {
    let mut arr: [MaybeUninit<FA>; D] = unsafe { MaybeUninit::uninit().assume_init() };

    arr[0] = MaybeUninit::new(x);
    let mut acc = 1;
    loop {
        if acc == D {
            break;
        }
        arr[acc] = MaybeUninit::new(FA::ZERO);
        acc += 1;
    }
    // If the code has reached this point every element of arr is correctly initialized.
    // Hence we are safe to reinterpret the array as [FA; D].

    unsafe { HackyWorkAround::transpose(arr).assume_init() }
}

/// Naive polynomial multiplication.
pub fn naive_poly_mul<FA: FieldAlgebra>(a: &[FA], b: &[FA]) -> Vec<FA> {
    // Grade school algorithm
    let mut product = vec![FA::ZERO; a.len() + b.len() - 1];
    for (i, c1) in a.iter().enumerate() {
        for (j, c2) in b.iter().enumerate() {
            product[i + j] += c1.clone() * c2.clone();
        }
    }
    product
}

/// Expand a product of binomials (x - roots[0])(x - roots[1]).. into polynomial coefficients.
pub fn binomial_expand<FA: FieldAlgebra>(roots: &[FA]) -> Vec<FA> {
    let mut coeffs = vec![FA::ZERO; roots.len() + 1];
    coeffs[0] = FA::ONE;
    for (i, x) in roots.iter().enumerate() {
        for j in (1..i + 2).rev() {
            coeffs[j] = coeffs[j - 1].clone() - x.clone() * coeffs[j].clone();
        }
        coeffs[0] *= -x.clone();
    }
    coeffs
}

pub fn eval_poly<FA: FieldAlgebra>(poly: &[FA], x: FA) -> FA {
    let mut acc = FA::ZERO;
    for coeff in poly.iter().rev() {
        acc *= x.clone();
        acc += coeff.clone();
    }
    acc
}

/// Given an element x from a 32 bit field F_P compute x/2.
#[inline]
pub fn halve_u32<const P: u32>(input: u32) -> u32 {
    let shift = (P + 1) >> 1;
    let shr = input >> 1;
    let lo_bit = input & 1;
    let shr_corr = shr + shift;
    if lo_bit == 0 {
        shr
    } else {
        shr_corr
    }
}

/// Given an element x from a 64 bit field F_P compute x/2.
#[inline]
pub fn halve_u64<const P: u64>(input: u64) -> u64 {
    let shift = (P + 1) >> 1;
    let shr = input >> 1;
    let lo_bit = input & 1;
    let shr_corr = shr + shift;
    if lo_bit == 0 {
        shr
    } else {
        shr_corr
    }
}

/// Given a slice of SF elements, reduce them to a TF element using a 2^32-base decomposition.
pub fn reduce_32<SF: PrimeField32, TF: PrimeField>(vals: &[SF]) -> TF {
    let po2 = TF::from_canonical_u64(1u64 << 32);
    let mut result = TF::ZERO;
    for val in vals.iter().rev() {
        result = result * po2 + TF::from_canonical_u32(val.as_canonical_u32());
    }
    result
}

/// Given an SF element, split it to a vector of TF elements using a 2^64-base decomposition.
///
/// We use a 2^64-base decomposition for a field of size ~2^32 because then the bias will be
/// at most ~1/2^32 for each element after the reduction.
pub fn split_32<SF: PrimeField, TF: PrimeField32>(val: SF, n: usize) -> Vec<TF> {
    let po2 = BigUint::from(1u128 << 64);
    let mut val = val.as_canonical_biguint();
    let mut result = Vec::new();
    for _ in 0..n {
        let mask: BigUint = po2.clone() - BigUint::from(1u128);
        let digit: BigUint = val.clone() & mask;
        let digit_u64s = digit.to_u64_digits();
        if !digit_u64s.is_empty() {
            result.push(TF::from_wrapped_u64(digit_u64s[0]));
        } else {
            result.push(TF::ZERO)
        }
        val /= po2.clone();
    }
    result
}

/// Maximally generic dot product.
pub fn dot_product<S, LI, RI>(li: LI, ri: RI) -> S
where
    LI: Iterator,
    RI: Iterator,
    LI::Item: Mul<RI::Item>,
    S: Sum<<LI::Item as Mul<RI::Item>>::Output>,
{
    li.zip(ri).map(|(l, r)| l * r).sum()
}
