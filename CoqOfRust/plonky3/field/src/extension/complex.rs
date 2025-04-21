use super::{BinomialExtensionField, BinomiallyExtendable, HasTwoAdicBinomialExtension};
use crate::{Algebra, Field, PrimeCharacteristicRing};

pub type Complex<F> = BinomialExtensionField<F, 2>;

/// A field for which `p = 3 (mod 4)`. Equivalently, `-1` is not a square,
/// so the complex extension can be defined `F[i] = F[X]/(X^2+1)`.
pub trait ComplexExtendable: Field {
    /// The two-adicity of `p+1`, the order of the circle group.
    const CIRCLE_TWO_ADICITY: usize;

    const COMPLEX_GENERATOR: Complex<Self>;

    fn circle_two_adic_generator(bits: usize) -> Complex<Self>;
}

impl<F: ComplexExtendable> BinomiallyExtendable<2> for F {
    const W: Self = F::NEG_ONE;

    // since `p = 3 (mod 4)`, `(p-1)/2` is always odd,
    // so `(-1)^((p-1)/2) = -1`
    const DTH_ROOT: Self = F::NEG_ONE;

    const EXT_GENERATOR: [Self; 2] = F::COMPLEX_GENERATOR.value;
}

/// Convenience methods for complex extensions
impl<R: PrimeCharacteristicRing> Complex<R> {
    #[inline(always)]
    pub const fn new_complex(real: R, imag: R) -> Self {
        Self::new([real, imag])
    }

    #[inline(always)]
    pub const fn new_real(real: R) -> Self {
        Self::new_complex(real, R::ZERO)
    }

    #[inline(always)]
    pub const fn new_imag(imag: R) -> Self {
        Self::new_complex(R::ZERO, imag)
    }

    #[inline(always)]
    pub fn real(&self) -> R {
        self.value[0].clone()
    }

    #[inline(always)]
    pub fn imag(&self) -> R {
        self.value[1].clone()
    }

    #[inline(always)]
    pub fn conjugate(&self) -> Self {
        Self::new_complex(self.real(), self.imag().neg())
    }

    #[inline]
    pub fn norm(&self) -> R {
        self.real().square() + self.imag().square()
    }

    #[inline(always)]
    pub fn to_array(&self) -> [R; 2] {
        self.value.clone()
    }

    // Sometimes we want to rotate over an extension that's not necessarily ComplexExtendable,
    // but still on the circle.
    pub fn rotate<Ext: Algebra<R>>(&self, rhs: &Complex<Ext>) -> Complex<Ext> {
        Complex::<Ext>::new_complex(
            rhs.real() * self.real() - rhs.imag() * self.imag(),
            rhs.imag() * self.real() + rhs.real() * self.imag(),
        )
    }
}

/// The complex extension of this field has a binomial extension.
///
/// This exists if the polynomial ring `F[i][X]` has an irreducible polynomial `X^d-W`
/// allowing us to define the binomial extension field `F[i][X]/(X^d-W)`.
pub trait HasComplexBinomialExtension<const D: usize>: ComplexExtendable {
    const W: Complex<Self>;

    // DTH_ROOT = W^((n - 1)/D).
    // n is the order of base field.
    // Only works when exists k such that n = kD + 1.
    const DTH_ROOT: Complex<Self>;

    const EXT_GENERATOR: [Complex<Self>; D];
}

impl<F, const D: usize> BinomiallyExtendable<D> for Complex<F>
where
    F: HasComplexBinomialExtension<D>,
{
    const W: Self = <F as HasComplexBinomialExtension<D>>::W;

    const DTH_ROOT: Self = <F as HasComplexBinomialExtension<D>>::DTH_ROOT;

    const EXT_GENERATOR: [Self; D] = F::EXT_GENERATOR;
}

/// The complex extension of this field has a two-adic binomial extension.
pub trait HasTwoAdicComplexBinomialExtension<const D: usize>:
    HasComplexBinomialExtension<D>
{
    const COMPLEX_EXT_TWO_ADICITY: usize;

    fn complex_ext_two_adic_generator(bits: usize) -> [Complex<Self>; D];
}

impl<F, const D: usize> HasTwoAdicBinomialExtension<D> for Complex<F>
where
    F: HasTwoAdicComplexBinomialExtension<D>,
{
    const EXT_TWO_ADICITY: usize = F::COMPLEX_EXT_TWO_ADICITY;

    #[inline(always)]
    fn ext_two_adic_generator(bits: usize) -> [Self; D] {
        F::complex_ext_two_adic_generator(bits)
    }
}
