use alloc::vec;
use alloc::vec::Vec;
use core::fmt::{Debug, Display};
use core::hash::Hash;
use core::iter::{Product, Sum};
use core::ops::{Add, AddAssign, Div, Mul, MulAssign, Neg, Sub, SubAssign};
use core::slice;

use num_bigint::BigUint;
use serde::Serialize;
use serde::de::DeserializeOwned;

use crate::exponentiation::bits_u64;
use crate::integers::{QuotientMap, from_integer_types};
use crate::packed::PackedField;
use crate::{Packable, PackedFieldExtension};

/// A commutative ring, `R`, with prime characteristic, `p`.
///
/// This permits elements like:
/// - A single finite field element.
/// - A symbolic expression which would evaluate to a field element.
/// - An array of finite field elements.
/// - A polynomial with coefficients in a finite field.
///
/// ### Mathematical Description
///
/// Mathematically, a commutative ring is a set of objects which supports an addition-like
/// like operation, `+`, and a multiplication-like operation `*`.
///
/// Let `x, y, z` denote arbitrary elements of the set.
///
/// Then, an operation is addition-like if it satisfies the following properties:
/// - Commutativity => `x + y = y + x`
/// - Associativity => `x + (y + z) = (x + y) + z`
/// - Unit => There exists an identity element `ZERO` satisfying `x + ZERO = x`.
/// - Inverses => For every `x` there exists a unique inverse `(-x)` satisfying `x + (-x) = ZERO`
///
/// Similarly, an operation is multiplication-like if it satisfies the following properties:
/// - Commutativity => `x * y = y * x`
/// - Associativity => `x * (y * z) = (x * y) * z`
/// - Unit => There exists an identity element `ONE` satisfying `x * ONE = x`.
/// - Distributivity => The two operations `+` and `*` must together satisfy `x * (y + z) = (x * y) + (x * z)`
///
/// Unlike in the addition case, we do not require inverses to exist with respect to `*`.
///
/// The simplest examples of commutative rings are the integers (`ℤ`), and the integers mod `N` (`ℤ/N`).
///
/// The characteristic of a ring is the smallest positive integer `r` such that `0 = r . 1 = 1 + 1 + ... + 1 (r times)`.
/// For example, the characteristic of the modulo ring `ℤ/N` is `N`.
///
/// Rings with prime characteristic are particularly special due to their close relationship with finite fields.
pub trait PrimeCharacteristicRing:
    Sized
    + Default
    + Clone
    + Add<Output = Self>
    + AddAssign
    + Sub<Output = Self>
    + SubAssign
    + Neg<Output = Self>
    + Mul<Output = Self>
    + MulAssign
    + Sum
    + Product
    + Debug
{
    /// The field `ℤ/p` where the characteristic of this ring is p.
    type PrimeSubfield: PrimeField;

    /// The additive identity of the ring.
    ///
    /// For every element `a` in the ring we require the following properties:
    ///
    /// `a + ZERO = ZERO + a = a,`
    ///
    /// `a + (-a) = (-a) + a = ZERO.`
    const ZERO: Self;

    /// The multiplicative identity of the ring.
    ///
    /// For every element `a` in the ring we require the following property:
    ///
    /// `a*ONE = ONE*a = a.`
    const ONE: Self;

    /// The element in the ring given by `ONE + ONE`.
    ///
    /// This is provided as a convenience as `TWO` occurs regularly in
    /// the proving system. This also is slightly faster than computing
    /// it via addition. Note that multiplication by `TWO` is discouraged.
    /// Instead of `a * TWO` use `a.double()` which will be faster.
    ///
    /// If the field has characteristic 2 this is equal to ZERO.
    const TWO: Self;

    /// The element in the ring given by `-ONE`.
    ///
    /// This is provided as a convenience as `NEG_ONE` occurs regularly in
    /// the proving system. This also is slightly faster than computing
    /// it via negation. Note that where possible `NEG_ONE` should be absorbed
    /// into mathematical operations. For example `a - b` will be faster
    /// than `a + NEG_ONE * b` and similarly `(-b)` is faster than `NEG_ONE * b`.
    ///
    /// If the field has characteristic 2 this is equal to ONE.
    const NEG_ONE: Self;

    /// Embed an element of the prime field `ℤ/p` into the ring `R`.
    ///
    /// Given any element `[r] ∈ ℤ/p`, represented by an integer `r` between `0` and `p - 1`
    /// `from_prime_subfield([r])` will be equal to:
    ///
    /// `Self::ONE + ... + Self::ONE (r times)`
    fn from_prime_subfield(f: Self::PrimeSubfield) -> Self;

    /// Return `Self::ONE` if `b` is `true` and `Self::ZERO` if `b` is `false`.
    #[must_use]
    #[inline(always)]
    fn from_bool(b: bool) -> Self {
        // Some rings might reimplement this to avoid the branch.
        if b { Self::ONE } else { Self::ZERO }
    }

    from_integer_types!(
        u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize
    );

    /// The elementary function `double(a) = 2*a`.
    ///
    /// This function should be preferred over calling `a + a` or `TWO * a` as a faster implementation may be available for some rings.
    /// If the field has characteristic 2 then this returns 0.
    #[must_use]
    #[inline(always)]
    fn double(&self) -> Self {
        self.clone() + self.clone()
    }

    /// The elementary function `square(a) = a^2`.
    ///
    /// This function should be preferred over calling `a * a`, as a faster implementation may be available for some rings.
    #[must_use]
    #[inline(always)]
    fn square(&self) -> Self {
        self.clone() * self.clone()
    }

    /// The elementary function `cube(a) = a^3`.
    ///
    /// This function should be preferred over calling `a * a * a`, as a faster implementation may be available for some rings.
    #[must_use]
    #[inline(always)]
    fn cube(&self) -> Self {
        self.square() * self.clone()
    }

    /// Computes the arithmetic generalization of boolean `xor`.
    ///
    /// For boolean inputs, `x ^ y = x + y - 2 xy`.
    #[must_use]
    #[inline(always)]
    fn xor(&self, y: &Self) -> Self {
        self.clone() + y.clone() - self.clone() * y.clone().double()
    }

    /// Computes the arithmetic generalization of a triple `xor`.
    ///
    /// For boolean inputs `x ^ y ^ z = x + y + z - 2(xy + xz + yz) + 4xyz`.
    #[must_use]
    #[inline(always)]
    fn xor3(&self, y: &Self, z: &Self) -> Self {
        self.xor(y).xor(z)
    }

    /// Computes the arithmetic generalization of `andnot`.
    ///
    /// For boolean inputs `(!x) & y = (1 - x)y`.
    #[must_use]
    #[inline(always)]
    fn andn(&self, y: &Self) -> Self {
        (Self::ONE - self.clone()) * y.clone()
    }

    /// The vanishing polynomial for boolean values: `x * (1 - x)`.
    ///
    /// This is a polynomial of degree `2` that evaluates to `0` if the input is `0` or `1`.
    /// If our space is a field, then this will be nonzero on all other inputs.
    #[must_use]
    #[inline(always)]
    fn bool_check(&self) -> Self {
        // We use `x * (1 - x)` instead of `x * (x - 1)` as this lets us delegate to the `andn` function.
        self.andn(self)
    }

    /// Exponentiation by a `u64` power.
    ///
    /// This uses the standard square and multiply approach.
    /// For specific powers regularly used and known in advance,
    /// this will be slower than custom addition chain exponentiation.
    #[must_use]
    #[inline]
    fn exp_u64(&self, power: u64) -> Self {
        let mut current = self.clone();
        let mut product = Self::ONE;

        for j in 0..bits_u64(power) {
            if (power >> j) & 1 != 0 {
                product *= current.clone();
            }
            current = current.square();
        }
        product
    }

    /// Exponentiation by a small constant power.
    ///
    /// For a collection of small values we implement custom multiplication chain circuits which can be faster than the
    /// simpler square and multiply approach.
    ///
    /// For large values this defaults back to `self.exp_u64`.
    #[must_use]
    #[inline(always)]
    fn exp_const_u64<const POWER: u64>(&self) -> Self {
        match POWER {
            0 => Self::ONE,
            1 => self.clone(),
            2 => self.square(),
            3 => self.cube(),
            4 => self.square().square(),
            5 => self.square().square() * self.clone(),
            6 => self.square().cube(),
            7 => {
                let x2 = self.square();
                let x3 = x2.clone() * self.clone();
                let x4 = x2.square();
                x3 * x4
            }
            _ => self.exp_u64(POWER),
        }
    }

    /// The elementary function `exp_power_of_2(a, power_log) = a^{2^power_log}`.
    ///
    /// Computed via repeated squaring.
    #[must_use]
    #[inline]
    fn exp_power_of_2(&self, power_log: usize) -> Self {
        let mut res = self.clone();
        for _ in 0..power_log {
            res = res.square();
        }
        res
    }

    /// The elementary function `mul_2exp_u64(a, exp) = a * 2^{exp}`.
    ///
    /// Here `2^{exp}` is computed using the square and multiply approach.
    #[must_use]
    #[inline]
    fn mul_2exp_u64(&self, exp: u64) -> Self {
        self.clone() * Self::TWO.exp_u64(exp)
    }

    /// Construct an iterator which returns powers of `self`: `self^0, self^1, self^2, ...`.
    #[must_use]
    #[inline]
    fn powers(&self) -> Powers<Self> {
        self.shifted_powers(Self::ONE)
    }

    /// Construct an iterator which returns powers of `self` shifted by `start`: `start, start*self^1, start*self^2, ...`.
    #[must_use]
    #[inline]
    fn shifted_powers(&self, start: Self) -> Powers<Self> {
        Powers {
            base: self.clone(),
            current: start,
        }
    }

    /// Compute the dot product of two vectors.
    #[must_use]
    #[inline]
    fn dot_product<const N: usize>(u: &[Self; N], v: &[Self; N]) -> Self {
        u.iter().zip(v).map(|(x, y)| x.clone() * y.clone()).sum()
    }

    /// Compute the sum of a slice of elements whose length is a compile time constant.
    ///
    /// The rust compiler doesn't realize that add is associative
    /// so we help it out and minimize the dependency chains by hand.
    /// Thus while this function has the same throughput as `input.iter().sum()`,
    /// it will usually have much lower latency.
    ///
    /// # Panics
    ///
    /// May panic if the length of the input slice is not equal to `N`.
    #[must_use]
    #[inline]
    fn sum_array<const N: usize>(input: &[Self]) -> Self {
        // It looks a little strange but using a const parameter and an assert_eq! instead of
        // using input.len() leads to a significant performance improvement.
        // We could make this input &[Self; N] but that would require sticking .try_into().unwrap() everywhere.
        // Checking godbolt, the compiler seems to unroll everything anyway.
        assert_eq!(N, input.len());

        // For `N <= 8` we implement a tree sum structure and for `N > 8` we break the input into
        // chunks of `8`, perform a tree sum on each chunk and sum the results. The parameter `8`
        // was determined experimentally by testing the speed of the poseidon2 internal layer computations.
        // This is a useful benchmark as we have a mix of summations of size 15, 23 with other work in between.
        // I only tested this on `AVX2` though so there might be a better value for other architectures.
        match N {
            0 => Self::ZERO,
            1 => input[0].clone(),
            2 => input[0].clone() + input[1].clone(),
            3 => input[0].clone() + input[1].clone() + input[2].clone(),
            4 => (input[0].clone() + input[1].clone()) + (input[2].clone() + input[3].clone()),
            5 => Self::sum_array::<4>(&input[..4]) + Self::sum_array::<1>(&input[4..]),
            6 => Self::sum_array::<4>(&input[..4]) + Self::sum_array::<2>(&input[4..]),
            7 => Self::sum_array::<4>(&input[..4]) + Self::sum_array::<3>(&input[4..]),
            8 => Self::sum_array::<4>(&input[..4]) + Self::sum_array::<4>(&input[4..]),
            _ => {
                // We know that N > 8 here so this saves an add over the usual
                // initialisation of acc to Self::ZERO.
                let mut acc = Self::sum_array::<8>(&input[..8]);
                for i in (16..=N).step_by(8) {
                    acc += Self::sum_array::<8>(&input[(i - 8)..i])
                }
                // This would be much cleaner if we could use const generic expressions but
                // this will do for now.
                match N & 7 {
                    0 => acc,
                    1 => acc + Self::sum_array::<1>(&input[(8 * (N / 8))..]),
                    2 => acc + Self::sum_array::<2>(&input[(8 * (N / 8))..]),
                    3 => acc + Self::sum_array::<3>(&input[(8 * (N / 8))..]),
                    4 => acc + Self::sum_array::<4>(&input[(8 * (N / 8))..]),
                    5 => acc + Self::sum_array::<5>(&input[(8 * (N / 8))..]),
                    6 => acc + Self::sum_array::<6>(&input[(8 * (N / 8))..]),
                    7 => acc + Self::sum_array::<7>(&input[(8 * (N / 8))..]),
                    _ => unreachable!(),
                }
            }
        }
    }

    /// Allocates a vector of zero elements of length `len`. Many operating systems zero pages
    /// before assigning them to a userspace process. In that case, our process should not need to
    /// write zeros, which would be redundant. However, the compiler may not always recognize this.
    ///
    /// In particular, `vec![Self::ZERO; len]` appears to result in redundant userspace zeroing.
    /// This is the default implementation, but implementors may wish to provide their own
    /// implementation which transmutes something like `vec![0u32; len]`.
    #[must_use]
    #[inline]
    fn zero_vec(len: usize) -> Vec<Self> {
        vec![Self::ZERO; len]
    }
}

/// A vector space `V` over `F` with a fixed basis. Fixing the basis allows elements of `V` to be
/// converted to and from `DIMENSION` many elements of `F` which are interpreted as basis coefficients.
///
/// We usually expect `F` to be a field but do not enforce this and so allow it to be just a ring.
/// This lets every ring implement `BasedVectorSpace<Self>` and is useful in a couple of other cases.
///
/// ## Safety
/// We make no guarantees about consistency of the choice of basis across different versions of Plonky3.
/// If this choice of basis changes, the behaviour of `BasedVectorSpace` will also change. Due to this,
/// we recommend avoiding using this trait unless absolutely necessary.
///
/// ### Mathematical Description
/// Given a vector space, `A` over `F`, a basis is a set of elements `B = {b_0, ..., b_{n-1}}`
/// in `A` such that, given any element `a`, we can find a unique set of `n` elements of `F`,
/// `f_0, ..., f_{n - 1}` satisfying `a = f_0 b_0 + ... + f_{n - 1} b_{n - 1}`. Thus the choice
/// of `B` gives rise to a natural linear map between the vector space `A` and the canonical
/// `n` dimensional vector space `F^n`.
///
/// This allows us to map between elements of `A` and arrays of `n` elements of `F`.
/// Clearly this map depends entirely on the choice of basis `B` which may change
/// across versions of Plonky3.
///
/// The situation is slightly more complicated in cases where `F` is not a field but boils down
/// to an identical description once we enforce that `A` is a free module over `F`.
pub trait BasedVectorSpace<F: PrimeCharacteristicRing>: Sized {
    /// The dimension of the vector space, i.e. the number of elements in
    /// its basis.
    const DIMENSION: usize;

    /// Fixes a basis for the algebra `A` and uses this to
    /// map an element of `A` to a slice of `DIMENSION` `F` elements.
    ///
    /// # Safety
    ///
    /// The value produced by this function fundamentally depends
    /// on the choice of basis. Care must be taken
    /// to ensure portability if these values might ever be passed to
    /// (or rederived within) another compilation environment where a
    /// different basis might have been used.
    #[must_use]
    fn as_basis_coefficients_slice(&self) -> &[F];

    /// Fixes a basis for the algebra `A` and uses this to
    /// map `DIMENSION` `F` elements to an element of `A`.
    ///
    /// # Safety
    ///
    /// The value produced by this function fundamentally depends
    /// on the choice of basis. Care must be taken
    /// to ensure portability if these values might ever be passed to
    /// (or rederived within) another compilation environment where a
    /// different basis might have been used.
    ///
    /// Returns `None` if the length of the slice is different to `DIMENSION`.
    #[must_use]
    #[inline]
    fn from_basis_coefficients_slice(slice: &[F]) -> Option<Self> {
        Self::from_basis_coefficients_iter(slice.iter().cloned())
    }

    /// Fixes a basis for the algebra `A` and uses this to
    /// map `DIMENSION` `F` elements to an element of `A`. Similar
    /// to `core:array::from_fn`, the `DIMENSION` `F` elements are
    /// given by `Fn(0), ..., Fn(DIMENSION - 1)` called in that order.
    ///
    /// # Safety
    ///
    /// The value produced by this function fundamentally depends
    /// on the choice of basis. Care must be taken
    /// to ensure portability if these values might ever be passed to
    /// (or rederived within) another compilation environment where a
    /// different basis might have been used.
    #[must_use]
    fn from_basis_coefficients_fn<Fn: FnMut(usize) -> F>(f: Fn) -> Self;

    /// Fixes a basis for the algebra `A` and uses this to
    /// map `DIMENSION` `F` elements to an element of `A`.
    ///
    /// # Safety
    ///
    /// The value produced by this function fundamentally depends
    /// on the choice of basis. Care must be taken
    /// to ensure portability if these values might ever be passed to
    /// (or rederived within) another compilation environment where a
    /// different basis might have been used.
    ///
    /// Returns `None` if the length of the iterator is different to `DIMENSION`.
    #[must_use]
    fn from_basis_coefficients_iter<I: ExactSizeIterator<Item = F>>(iter: I) -> Option<Self>;

    /// Given a basis for the Algebra `A`, return the i'th basis element.
    ///
    /// # Safety
    ///
    /// The value produced by this function fundamentally depends
    /// on the choice of basis. Care must be taken
    /// to ensure portability if these values might ever be passed to
    /// (or rederived within) another compilation environment where a
    /// different basis might have been used.
    ///
    /// Returns `None` if `i` is greater than or equal to `DIMENSION`.
    #[must_use]
    #[inline]
    fn ith_basis_element(i: usize) -> Option<Self> {
        (i < Self::DIMENSION).then(|| Self::from_basis_coefficients_fn(|j| F::from_bool(i == j)))
    }

    /// Convert from a vector of `Self` to a vector of `F` by flattening the basis coefficients.
    ///
    /// Depending on the `BasedVectorSpace` this may be essentially a no-op and should certainly
    /// be reimplemented in those cases.
    ///
    /// # Safety
    ///
    /// The value produced by this function fundamentally depends
    /// on the choice of basis. Care must be taken
    /// to ensure portability if these values might ever be passed to
    /// (or rederived within) another compilation environment where a
    /// different basis might have been used.
    #[must_use]
    #[inline]
    fn flatten_to_base(vec: Vec<Self>) -> Vec<F> {
        vec.into_iter()
            .flat_map(|x| x.as_basis_coefficients_slice().to_vec())
            .collect()
    }

    /// Convert from a vector of `F` to a vector of `Self` by combining the basis coefficients.
    ///
    /// Depending on the `BasedVectorSpace` this may be essentially a no-op and should certainly
    /// be reimplemented in those cases.
    ///
    /// # Panics
    /// This will panic if the length of `vec` is not a multiple of `Self::DIMENSION`.
    ///
    /// # Safety
    ///
    /// The value produced by this function fundamentally depends
    /// on the choice of basis. Care must be taken
    /// to ensure portability if these values might ever be passed to
    /// (or rederived within) another compilation environment where a
    /// different basis might have been used.
    #[must_use]
    #[inline]
    fn reconstitute_from_base(vec: Vec<F>) -> Vec<Self> {
        assert_eq!(vec.len() % Self::DIMENSION, 0);

        vec.chunks_exact(Self::DIMENSION)
            .flat_map(|chunk| Self::from_basis_coefficients_slice(chunk))
            .collect()
    }
}

impl<F: PrimeCharacteristicRing> BasedVectorSpace<F> for F {
    const DIMENSION: usize = 1;

    #[inline]
    fn as_basis_coefficients_slice(&self) -> &[F] {
        slice::from_ref(self)
    }

    #[inline]
    fn from_basis_coefficients_fn<Fn: FnMut(usize) -> F>(mut f: Fn) -> Self {
        f(0)
    }

    #[inline]
    fn from_basis_coefficients_iter<I: ExactSizeIterator<Item = F>>(mut iter: I) -> Option<Self> {
        (iter.len() == 1).then(|| iter.next().unwrap()) // Unwrap will not panic as we know the length is 1.
    }

    #[must_use]
    #[inline]
    fn flatten_to_base(vec: Vec<Self>) -> Vec<F> {
        vec
    }

    #[must_use]
    #[inline]
    fn reconstitute_from_base(vec: Vec<F>) -> Vec<Self> {
        vec
    }
}

/// A ring implements `InjectiveMonomial<N>` if the algebraic function
/// `f(x) = x^N` is an injective map on elements of the ring.
///
/// We do not enforce that this map be invertible as there are useful
/// cases such as polynomials or symbolic expressions where no inverse exists.
///
/// However, if the ring is a field with order `q` or an array of such field elements,
/// then `f(x) = x^N` will be injective if and only if it is invertible and so in
/// such cases this monomial acts as a permutation. Moreover, this will occur
/// exactly when `N` and `q - 1` are relatively prime i.e. `gcd(N, q - 1) = 1`.
pub trait InjectiveMonomial<const N: u64>: PrimeCharacteristicRing {
    /// Compute `x -> x^n` for a given `n > 1` such that this
    /// map is injective.
    #[must_use]
    #[inline]
    fn injective_exp_n(&self) -> Self {
        self.exp_const_u64::<N>()
    }
}

/// A ring implements `PermutationMonomial<N>` if the algebraic function
/// `f(x) = x^N` is invertible and thus acts as a permutation on elements of the ring.
///
/// In all cases we care about, this means that we can find another integer `K` such
/// that `x = x^{NK}` for all elements of our ring.
pub trait PermutationMonomial<const N: u64>: InjectiveMonomial<N> {
    /// Compute `x -> x^K` for a given `K > 1` such that
    /// `x^{NK} = x` for all elements `x`.
    #[must_use]
    fn injective_exp_root_n(&self) -> Self;
}

/// A ring `R` implements `Algebra<F>` if there is an injective homomorphism
///  from `F` into `R`; in particular only `F::ZERO` maps to `R::ZERO`.
///
/// For the most part, we will usually expect `F` to be a field but there
/// are a few cases where it is handy to allow it to just be a ring. In
/// particular, every ring naturally implements `Algebra<Self>`.
///
/// ### Mathematical Description
///
/// Let `x` and `y` denote arbitrary elements of `F`. Then
/// we require that our map `from` has the properties:
/// - Preserves Identity: `from(F::ONE) = R::ONE`
/// - Commutes with Addition: `from(x + y) = from(x) + from(y)`
/// - Commutes with Multiplication: `from(x * y) = from(x) * from(y)`
///
/// Such maps are known as ring homomorphisms and are injective if the
/// only element which maps to `R::ZERO` is `F::ZERO`.
///
/// The existence of this map makes `R` into an `F`-module and hence an `F`-algebra.
/// If, additionally, `R` is a field, then this makes `R` a field extension of `F`.
pub trait Algebra<F>:
    PrimeCharacteristicRing
    + From<F>
    + Add<F, Output = Self>
    + AddAssign<F>
    + Sub<F, Output = Self>
    + SubAssign<F>
    + Mul<F, Output = Self>
    + MulAssign<F>
{
}

// Every ring is an algebra over itself.
impl<R: PrimeCharacteristicRing> Algebra<R> for R {}

/// A field `F`. This permits both modular fields `ℤ/p` along with their field extensions.
///
/// A ring is a field if every element `x` has a unique multiplicative inverse `x^{-1}`
/// which satisfies `x * x^{-1} = F::ONE`.
pub trait Field:
    Algebra<Self>
    + Packable
    + 'static
    + Copy
    + Div<Self, Output = Self>
    + Eq
    + Hash
    + Send
    + Sync
    + Display
    + Serialize
    + DeserializeOwned
{
    type Packing: PackedField<Scalar = Self>;

    /// A generator of this field's multiplicative group.
    const GENERATOR: Self;

    /// Check if the given field element is equal to the unique additive identity (ZERO).
    #[must_use]
    #[inline]
    fn is_zero(&self) -> bool {
        *self == Self::ZERO
    }

    /// Check if the given field element is equal to the unique multiplicative identity (ONE).
    #[must_use]
    #[inline]
    fn is_one(&self) -> bool {
        *self == Self::ONE
    }

    /// The multiplicative inverse of this field element, if it exists.
    ///
    /// NOTE: The inverse of `0` is undefined and will return `None`.
    #[must_use]
    fn try_inverse(&self) -> Option<Self>;

    /// The multiplicative inverse of this field element.
    ///
    /// # Panics
    /// The function will panic if the field element is `0`.
    /// Use try_inverse if you want to handle this case.
    #[must_use]
    fn inverse(&self) -> Self {
        self.try_inverse().expect("Tried to invert zero")
    }

    /// The elementary function `halve(a) = a/2`.
    ///
    /// # Panics
    /// The function will panic if the field has characteristic 2.
    #[must_use]
    fn halve(&self) -> Self {
        // This should be overwritten by most field implementations.
        let half = Self::from_prime_subfield(
            Self::PrimeSubfield::TWO
                .try_inverse()
                .expect("Cannot divide by 2 in fields with characteristic 2"),
        );
        *self * half
    }

    /// Divide by a given power of two. `div_2exp_u64(a, exp) = a/2^exp`
    ///
    /// # Panics
    /// The function will panic if the field has characteristic 2.
    #[must_use]
    #[inline]
    fn div_2exp_u64(&self, exp: u64) -> Self {
        // This should be overwritten by most field implementations.
        *self
            * Self::from_prime_subfield(
                Self::PrimeSubfield::TWO
                    .try_inverse()
                    .expect("Cannot divide by 2 in fields with characteristic 2")
                    .exp_u64(exp),
            )
    }

    /// The number of elements in the field.
    ///
    /// This will either be prime if the field is a PrimeField or a power of a
    /// prime if the field is an extension field.
    #[must_use]
    fn order() -> BigUint;

    /// The number of bits required to define an element of this field.
    ///
    /// Usually due to storage and practical reasons the memory size of
    /// a field element will be a little larger than bits().
    #[must_use]
    #[inline]
    fn bits() -> usize {
        Self::order().bits() as usize
    }
}

/// A field isomorphic to `ℤ/p` for some prime `p`.
///
/// There is a natural map from `ℤ` to `ℤ/p` which sends an integer `r` to its conjugacy class `[r]`.
/// Canonically, each conjugacy class `[r]` can be represented by the unique integer `s` in `[0, p - 1)`
/// satisfying `s = r mod p`. This however is often not the most convenient computational representation
/// and so internal representations of field elements might differ from this and may change over time.
pub trait PrimeField:
    Field
    + Ord
    + QuotientMap<u8>
    + QuotientMap<u16>
    + QuotientMap<u32>
    + QuotientMap<u64>
    + QuotientMap<u128>
    + QuotientMap<usize>
    + QuotientMap<i8>
    + QuotientMap<i16>
    + QuotientMap<i32>
    + QuotientMap<i64>
    + QuotientMap<i128>
    + QuotientMap<isize>
{
    /// Return the representative of `value` in canonical form
    /// which lies in the range `0 <= x < self.order()`.
    #[must_use]
    fn as_canonical_biguint(&self) -> BigUint;
}

/// A prime field `ℤ/p` with order, `p < 2^64`.
pub trait PrimeField64: PrimeField {
    const ORDER_U64: u64;

    /// Return the representative of `value` in canonical form
    /// which lies in the range `0 <= x < ORDER_U64`.
    #[must_use]
    fn as_canonical_u64(&self) -> u64;

    /// Convert a field element to a `u64` such that any two field elements
    /// are converted to the same `u64` if and only if they represent the same value.
    ///
    /// This will be the fastest way to convert a field element to a `u64` and
    /// is intended for use in hashing. It will also be consistent across different targets.
    #[must_use]
    #[inline(always)]
    fn to_unique_u64(&self) -> u64 {
        // A simple default which is optimal for some fields.
        self.as_canonical_u64()
    }
}

/// A prime field `ℤ/p` with order `p < 2^32`.
pub trait PrimeField32: PrimeField64 {
    const ORDER_U32: u32;

    /// Return the representative of `value` in canonical form
    /// which lies in the range `0 <= x < ORDER_U64`.
    #[must_use]
    fn as_canonical_u32(&self) -> u32;

    /// Convert a field element to a `u32` such that any two field elements
    /// are converted to the same `u32` if and only if they represent the same value.
    ///
    /// This will be the fastest way to convert a field element to a `u32` and
    /// is intended for use in hashing. It will also be consistent across different targets.
    #[must_use]
    #[inline(always)]
    fn to_unique_u32(&self) -> u32 {
        // A simple default which is optimal for some fields.
        self.as_canonical_u32()
    }
}

/// A field `EF` which is also an algebra over a field `F`.
///
/// This provides a couple of convenience methods on top of the
/// standard methods provided by `Field`, `Algebra<F>` and `BasedVectorSpace<F>`.
///
/// It also provides a type which handles packed vectors of extension field elements.
pub trait ExtensionField<Base: Field>: Field + Algebra<Base> + BasedVectorSpace<Base> {
    type ExtensionPacking: PackedFieldExtension<Base, Self> + 'static + Copy + Send + Sync;

    /// Determine if the given element lies in the base field.
    #[must_use]
    fn is_in_basefield(&self) -> bool;

    /// If the element lies in the base field project it down.
    /// Otherwise return None.
    #[must_use]
    fn as_base(&self) -> Option<Base>;
}

// Every field is trivially a one dimensional extension over itself.
impl<F: Field> ExtensionField<F> for F {
    type ExtensionPacking = F::Packing;

    #[inline]
    fn is_in_basefield(&self) -> bool {
        true
    }

    #[inline]
    fn as_base(&self) -> Option<F> {
        Some(*self)
    }
}

/// A field which supplies information like the two-adicity of its multiplicative group, and methods
/// for obtaining two-adic generators.
pub trait TwoAdicField: Field {
    /// The number of factors of two in this field's multiplicative group.
    const TWO_ADICITY: usize;

    /// Returns a generator of the multiplicative group of order `2^bits`.
    /// Assumes `bits <= TWO_ADICITY`, otherwise the result is undefined.
    #[must_use]
    fn two_adic_generator(bits: usize) -> Self;
}

/// An iterator which returns the powers of a base element `b` shifted by current `c`: `c, c * b, c * b^2, ...`.
#[derive(Clone, Debug)]
pub struct Powers<F> {
    pub base: F,
    pub current: F,
}

impl<R: PrimeCharacteristicRing> Iterator for Powers<R> {
    type Item = R;

    fn next(&mut self) -> Option<R> {
        let result = self.current.clone();
        self.current *= self.base.clone();
        Some(result)
    }
}
