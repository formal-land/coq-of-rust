//! Copied from starkware-libs/stwo under Apache-2.0 license.
use std::{
    iter::Sum,
    ops::{Add, Deref, Mul, Neg, Sub},
};

use p3_field::Field;

#[derive(Debug, Clone)]
pub struct UnivariatePolynomial<F> {
    coeffs: Vec<F>,
}

impl<F: Field> UnivariatePolynomial<F> {
    /// Creates a new univariate polynomial from a vector of coefficients.
    pub fn from_coeffs(coeffs: Vec<F>) -> Self {
        let mut polynomial = Self { coeffs };
        polynomial.trim_leading_zeroes();
        polynomial
    }

    pub fn zero() -> Self {
        Self { coeffs: vec![] }
    }

    fn one() -> Self {
        Self {
            coeffs: vec![F::ONE],
        }
    }

    fn is_zero(&self) -> bool {
        self.coeffs.iter().all(F::is_zero)
    }

    pub fn evaluate(&self, x: F) -> F {
        self.coeffs
            .iter()
            .rfold(F::ZERO, |acc, coeff| acc * x + *coeff)
    }

    pub fn degree(&self) -> usize {
        self.coeffs.iter().rposition(|&v| !v.is_zero()).unwrap_or(0)
    }

    /// Interpolates `points` via Lagrange interpolation.
    ///
    /// # Panics
    ///
    /// Panics if `points` contains duplicate x-coordinates.
    pub fn from_interpolation(points: &[(F, F)]) -> Self {
        let mut coeffs = Self::zero();

        for (i, &(xi, yi)) in points.iter().enumerate() {
            let mut num = UnivariatePolynomial::one();
            let mut denom = F::ONE;

            for (j, &(xj, _)) in points.iter().enumerate() {
                if i != j {
                    num = num * (Self::identity() - xj.into());
                    denom *= xi - xj;
                }
            }

            let selector = num * denom.inverse();
            coeffs = coeffs + selector * yi;
        }

        coeffs.trim_leading_zeroes();
        coeffs
    }

    fn identity() -> Self {
        Self {
            coeffs: vec![F::ZERO, F::ONE],
        }
    }

    fn trim_leading_zeroes(&mut self) {
        if let Some(non_zero_idx) = self.coeffs.iter().rposition(|&coeff| !coeff.is_zero()) {
            self.coeffs.truncate(non_zero_idx + 1);
        } else {
            self.coeffs.clear();
        }
    }

    pub fn into_coeffs(self) -> Vec<F> {
        self.coeffs
    }
}

impl<F: Field> Default for UnivariatePolynomial<F> {
    fn default() -> Self {
        Self::zero()
    }
}

impl<F: Field> From<F> for UnivariatePolynomial<F> {
    fn from(value: F) -> Self {
        Self::from_coeffs(vec![value])
    }
}

impl<F: Field> Mul<F> for UnivariatePolynomial<F> {
    type Output = Self;

    fn mul(mut self, rhs: F) -> Self {
        for coeff in &mut self.coeffs {
            *coeff *= rhs;
        }
        self
    }
}

impl<F: Field> Mul for UnivariatePolynomial<F> {
    type Output = Self;

    fn mul(mut self, mut rhs: Self) -> Self {
        if self.is_zero() || rhs.is_zero() {
            return Self::zero();
        }

        self.trim_leading_zeroes();
        rhs.trim_leading_zeroes();

        let mut res = vec![F::ZERO; self.coeffs.len() + rhs.coeffs.len() - 1];

        for (i, coeff_a) in self.coeffs.into_iter().enumerate() {
            for (j, coeff_b) in rhs.coeffs.iter().enumerate() {
                res[i + j] += coeff_a * *coeff_b;
            }
        }

        Self::from_coeffs(res)
    }
}

impl<F: Field> Add for UnivariatePolynomial<F> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        let n = self.coeffs.len().max(rhs.coeffs.len());
        let mut coeffs = Vec::with_capacity(n);

        for i in 0..n {
            let a = self.coeffs.get(i).copied().unwrap_or(F::ZERO);
            let b = rhs.coeffs.get(i).copied().unwrap_or(F::ZERO);
            coeffs.push(a + b);
        }

        Self { coeffs }
    }
}

impl<F: Field> Sub for UnivariatePolynomial<F> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self {
        self + (-rhs)
    }
}

impl<F: Field> Neg for UnivariatePolynomial<F> {
    type Output = Self;

    fn neg(self) -> Self {
        Self {
            coeffs: self.coeffs.into_iter().map(|v| -v).collect(),
        }
    }
}

impl<F: Field> Deref for UnivariatePolynomial<F> {
    type Target = [F];

    fn deref(&self) -> &Self::Target {
        &self.coeffs
    }
}

/// Evaluates a polynomial represented by coefficients in a slice at a given point `x`.
pub fn evaluate_on_slice<F: Field>(coeffs: &[F], x: F) -> F {
    coeffs.iter().rfold(F::ZERO, |acc, &coeff| acc * x + coeff)
}

/// Returns `v_0 + alpha * v_1 + ... + alpha^(n-1) * v_{n-1}`.
pub fn random_linear_combination<F: Field>(v: &[F], alpha: F) -> F {
    evaluate_on_slice(v, alpha)
}

/// Projective fraction.
#[derive(Debug, Clone, Copy)]
pub struct Fraction<T> {
    pub numerator: T,
    pub denominator: T,
}

impl<T> Fraction<T> {
    pub const fn new(numerator: T, denominator: T) -> Self {
        Self {
            numerator,
            denominator,
        }
    }
}

impl<T: Clone + Add<Output = T> + Mul<Output = T>> Add for Fraction<T> {
    type Output = Fraction<T>;

    fn add(self, rhs: Self) -> Fraction<T> {
        Fraction {
            numerator: rhs.denominator.clone() * self.numerator.clone()
                + self.denominator.clone() * rhs.numerator.clone(),
            denominator: self.denominator * rhs.denominator,
        }
    }
}

impl<F: Field> Fraction<F> {
    const ZERO: Self = Self::new(F::ZERO, F::ONE);

    pub fn is_zero(&self) -> bool {
        self.numerator.is_zero() && !self.denominator.is_zero()
    }
}

impl<F: Field> Sum for Fraction<F> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::ZERO, |a, b| a + b)
    }
}

#[cfg(test)]
mod tests {
    use std::iter::zip;

    use itertools::Itertools;
    use p3_baby_bear::BabyBear;
    use p3_field::FieldAlgebra;

    use super::*;

    macro_rules! bbvec {
        [$($x:expr),*] => {
            vec![$(BabyBear::from_canonical_u32($x)),*]
        }
    }

    #[test]
    fn test_interpolate() {
        let xs = bbvec![5, 1, 3, 9];
        let ys = bbvec![1, 2, 3, 4];
        let points = zip(&xs, &ys).map(|(x, y)| (*x, *y)).collect_vec();

        let poly = UnivariatePolynomial::from_interpolation(&points);

        for (x, y) in zip(xs, ys) {
            assert_eq!(poly.evaluate(x), y, "mismatch for x={x}");
        }
    }

    #[test]
    fn test_eval() {
        let coeffs = bbvec![9, 2, 3];
        let x = BabyBear::from_canonical_u32(7);

        let eval = UnivariatePolynomial::from_coeffs(coeffs.clone()).evaluate(x);

        assert_eq!(eval, coeffs[0] + coeffs[1] * x + coeffs[2] * x.square());
    }

    #[test]
    fn test_fractional_addition() {
        let a = Fraction::new(BabyBear::ONE, BabyBear::from_canonical_u32(3));
        let b = Fraction::new(BabyBear::TWO, BabyBear::from_canonical_u32(6));

        let Fraction {
            numerator,
            denominator,
        } = a + b;

        assert_eq!(
            numerator / denominator,
            BabyBear::TWO / BabyBear::from_canonical_u32(3)
        );
    }

    #[test]
    fn test_degree() {
        // Case 1: Zero polynomial (expect degree 0 for a polynomial with no terms)
        let poly_zero = UnivariatePolynomial::<BabyBear>::from_coeffs(vec![]);
        assert_eq!(
            poly_zero.degree(),
            0,
            "Zero polynomial should have degree 0"
        );

        // Case 2: Polynomial with only a constant term (degree should be 0)
        let poly_constant = UnivariatePolynomial::from_coeffs(bbvec![5]);
        assert_eq!(
            poly_constant.degree(),
            0,
            "Constant polynomial should have degree 0"
        );

        // Case 3: Linear polynomial (degree 1, e.g., 3x + 5)
        let poly_linear = UnivariatePolynomial::from_coeffs(bbvec![5, 3]);
        assert_eq!(
            poly_linear.degree(),
            1,
            "Linear polynomial should have degree 1"
        );

        // Case 4: Quadratic polynomial with trailing zeros (degree should ignore trailing zeros)
        let poly_quadratic = UnivariatePolynomial::from_coeffs(bbvec![2, 0, 4, 0, 0]);
        assert_eq!(
            poly_quadratic.degree(),
            2,
            "Quadratic polynomial with trailing zeros should have degree 2"
        );

        // Case 5: High-degree polynomial without trailing zeros
        let poly_high_degree = UnivariatePolynomial::from_coeffs(bbvec![1, 0, 0, 0, 5]);
        assert_eq!(
            poly_high_degree.degree(),
            4,
            "Polynomial of degree 4 should have degree 4"
        );
    }
}
