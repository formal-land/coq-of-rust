use core::fmt::Debug;
use core::hash::Hash;

use p3_field::{Field, PrimeCharacteristicRing};

use crate::MontyField31;

/// MontyParameters contains the prime P along with constants needed to convert elements into and out of MONTY form.
/// The MONTY constant is assumed to be a power of 2.
pub trait MontyParameters:
    Copy + Clone + Default + Debug + Eq + PartialEq + Sync + Send + Hash + 'static
{
    // A 31-bit prime.
    const PRIME: u32;

    // The log_2 of our MONTY constant.
    const MONTY_BITS: u32;

    // We define MONTY_MU = PRIME^-1 (mod 2^MONTY_BITS). This is different from the usual convention
    // (MONTY_MU = -PRIME^-1 (mod 2^MONTY_BITS)) but it avoids a carry.
    const MONTY_MU: u32;

    const MONTY_MASK: u32 = ((1u64 << Self::MONTY_BITS) - 1) as u32;
}

/// PackedMontyParameters contains constants needed for MONTY operations for packings of Monty31 fields.
#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
pub trait PackedMontyParameters: crate::MontyParametersNeon + MontyParameters {}
#[cfg(all(
    target_arch = "x86_64",
    target_feature = "avx2",
    not(all(feature = "nightly-features", target_feature = "avx512f"))
))]
/// PackedMontyParameters contains constants needed for MONTY operations for packings of Monty31 fields.
pub trait PackedMontyParameters: crate::MontyParametersAVX2 + MontyParameters {}
#[cfg(all(
    feature = "nightly-features",
    target_arch = "x86_64",
    target_feature = "avx512f"
))]
/// PackedMontyParameters contains constants needed for MONTY operations for packings of Monty31 fields.
pub trait PackedMontyParameters: crate::MontyParametersAVX512 + MontyParameters {}
#[cfg(not(any(
    all(target_arch = "aarch64", target_feature = "neon"),
    all(
        target_arch = "x86_64",
        target_feature = "avx2",
        not(all(feature = "nightly-features", target_feature = "avx512f"))
    ),
    all(
        feature = "nightly-features",
        target_arch = "x86_64",
        target_feature = "avx512f"
    ),
)))]
/// PackedMontyParameters contains constants needed for MONTY operations for packings of Monty31 fields.
pub trait PackedMontyParameters: MontyParameters {}

/// BarrettParameters contains constants needed for the Barrett reduction used in the MDS code.
pub trait BarrettParameters: MontyParameters {
    const N: usize = 40; // beta = 2^N, fixing N = 40 here
    const PRIME_I128: i128 = Self::PRIME as i128;
    const PSEUDO_INV: i64 = (((1_i128) << (2 * Self::N)) / Self::PRIME_I128) as i64; // I = 2^80 / P => I < 2**50
    const MASK: i64 = !((1 << 10) - 1); // Lets us 0 out the bottom 10 digits of an i64.
}

/// FieldParameters contains constants and methods needed to imply PrimeCharacteristicRing, Field and PrimeField32 for MontyField31.
pub trait FieldParameters: PackedMontyParameters + Sized {
    // Simple field constants.
    const MONTY_ZERO: MontyField31<Self> = MontyField31::new(0);
    const MONTY_ONE: MontyField31<Self> = MontyField31::new(1);
    const MONTY_TWO: MontyField31<Self> = MontyField31::new(2);
    const MONTY_NEG_ONE: MontyField31<Self> = MontyField31::new(Self::PRIME - 1);

    // A generator of the fields multiplicative group. Needs to be given in Monty Form.
    const MONTY_GEN: MontyField31<Self>;

    const HALF_P_PLUS_1: u32 = (Self::PRIME + 1) >> 1;

    fn try_inverse<F: Field>(p1: F) -> Option<F>;
}

/// An integer `D` such that `gcd(D, p - 1) = 1`.
pub trait RelativelyPrimePower<const D: u64> {
    /// Compute `x -> x^{1/D}` using the modular inverse
    /// of `D mod p - 1`.
    fn exp_root_d<R: PrimeCharacteristicRing>(val: R) -> R;
}

/// TwoAdicData contains constants needed to imply TwoAdicField for Monty31 fields.
pub trait TwoAdicData: MontyParameters {
    /// Largest n such that 2^n divides p - 1.
    const TWO_ADICITY: usize;

    /// The odd constant r such that p = r * 2^n + 1
    const ODD_FACTOR: i32 = (Self::PRIME >> Self::TWO_ADICITY) as i32;

    /// ArrayLike should usually be `&'static [MontyField31]`.
    type ArrayLike: AsRef<[MontyField31<Self>]> + Sized;

    /// A list of generators of 2-adic subgroups.
    /// The i'th element must be a 2^i root of unity and the i'th element squared must be the i-1'th element.
    const TWO_ADIC_GENERATORS: Self::ArrayLike;

    /// Precomputation of the first 3 8th-roots of unity.
    ///
    /// Must agree with the 8th-root in TWO_ADIC_GENERATORS, i.e.
    /// ROOTS_8[1] == TWO_ADIC_GENERATORS[3]
    const ROOTS_8: Self::ArrayLike;

    /// Precomputation of the inverses of ROOTS_8.
    const INV_ROOTS_8: Self::ArrayLike;

    /// Precomputation of the first 7 16th-roots of unity.
    ///
    /// Must agree with the 16th-root in TWO_ADIC_GENERATORS, i.e.
    /// ROOTS_16[1] == TWO_ADIC_GENERATORS[4]
    const ROOTS_16: Self::ArrayLike;

    /// Precomputation of the inverses of ROOTS_16.
    const INV_ROOTS_16: Self::ArrayLike;
}

/// TODO: This should be deleted long term once we have improved our API for defining extension fields.
/// This allows us to implement Binomial Extensions over Monty31 fields.
pub trait BinomialExtensionData<const DEG: usize>: MontyParameters + Sized {
    /// W is a value such that (x^DEG - W) is irreducible.
    const W: MontyField31<Self>;

    /// DTH_ROOT = W^((p - 1)/DEG)
    const DTH_ROOT: MontyField31<Self>;

    /// A generator of the extension fields multiplicative group.
    const EXT_GENERATOR: [MontyField31<Self>; DEG];

    const EXT_TWO_ADICITY: usize;

    /// ArrayLike should usually be [MontyField31; EXT_TWO_ADICITY - TWO_ADICITY].
    type ArrayLike: AsRef<[[MontyField31<Self>; DEG]]> + Sized;

    /// A list of generators of 2-adic subgroups not contained in the base field.
    const TWO_ADIC_EXTENSION_GENERATORS: Self::ArrayLike;
}
