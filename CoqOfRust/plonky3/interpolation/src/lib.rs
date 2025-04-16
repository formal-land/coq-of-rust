//! Tools for Lagrange interpolation.

#![no_std]

extern crate alloc;

use alloc::vec::Vec;

use p3_field::{
    ExtensionField, TwoAdicField, batch_multiplicative_inverse, scale_vec,
    two_adic_coset_vanishing_polynomial,
};
use p3_matrix::Matrix;
use p3_maybe_rayon::prelude::*;
use p3_util::log2_strict_usize;

/// Given evaluations of a batch of polynomials over the canonical power-of-two subgroup, evaluate
/// the polynomials at `point`.
///
/// This assumes the point is not in the subgroup, otherwise the behavior is undefined.
pub fn interpolate_subgroup<F, EF, Mat>(subgroup_evals: &Mat, point: EF) -> Vec<EF>
where
    F: TwoAdicField,
    EF: ExtensionField<F> + TwoAdicField,
    Mat: Matrix<F>,
{
    interpolate_coset(subgroup_evals, F::ONE, point, None)
}

/// Given evaluations of a batch of polynomials over the given coset of the canonical power-of-two
/// subgroup, evaluate the polynomials at `point`.
///
/// This assumes the point is not in the coset, otherwise the behavior is undefined.
/// If available, reuse denominator diffs that is `1 / (x_i-z)` to avoid batch inversion.
pub fn interpolate_coset<F, EF, Mat>(
    coset_evals: &Mat,
    shift: F,
    point: EF,
    diff_invs: Option<&[EF]>,
) -> Vec<EF>
where
    F: TwoAdicField,
    EF: ExtensionField<F> + TwoAdicField,
    Mat: Matrix<F>,
{
    // Slight variation of this approach: https://hackmd.io/@vbuterin/barycentric_evaluation

    let height = coset_evals.height();
    let log_height = log2_strict_usize(height);

    let g = F::two_adic_generator(log_height).powers().take(height);
    let col_scale: Vec<_> = if let Some(diff_invs) = diff_invs {
        g.zip(diff_invs)
            .map(|(sg, &diff_inv)| diff_inv * sg)
            .collect()
    } else {
        let subgroup = g.collect::<Vec<_>>();
        let diffs: Vec<EF> = subgroup
            .par_iter()
            .map(|&subgroup_i| point - subgroup_i * shift)
            .collect();
        let diff_invs = batch_multiplicative_inverse(&diffs);
        subgroup
            .par_iter()
            .zip(diff_invs)
            .map(|(&sg, diff_inv)| diff_inv * sg)
            .collect()
    };
    let sum = coset_evals.columnwise_dot_product(&col_scale);

    let vanishing_polynomial =
        two_adic_coset_vanishing_polynomial::<EF>(log_height, shift.into(), point);

    // In principle, height could be bigger than the characteristic of F.
    let denominator = shift
        .exp_u64(height as u64 - 1)
        .mul_2exp_u64(log_height as u64);
    scale_vec(vanishing_polynomial * denominator.inverse(), sum)
}

#[cfg(test)]
mod tests {
    use alloc::vec;
    use alloc::vec::Vec;

    use p3_baby_bear::BabyBear;
    use p3_field::{Field, PrimeCharacteristicRing, batch_multiplicative_inverse};
    use p3_matrix::dense::RowMajorMatrix;
    use p3_util::log2_strict_usize;

    use crate::{interpolate_coset, interpolate_subgroup};

    #[test]
    fn test_interpolate_subgroup() {
        // x^2 + 2 x + 3
        type F = BabyBear;
        let evals = [
            6, 886605102, 1443543107, 708307799, 2, 556938009, 569722818, 1874680944,
        ]
        .map(F::from_u32);
        let evals_mat = RowMajorMatrix::new(evals.to_vec(), 1);
        let point = F::from_u16(100);
        let result = interpolate_subgroup(&evals_mat, point);
        assert_eq!(result, vec![F::from_u16(10203)]);
    }

    #[test]
    fn test_interpolate_coset() {
        // x^2 + 2 x + 3
        type F = BabyBear;
        let shift = F::GENERATOR;
        let evals = [
            1026, 129027310, 457985035, 994890337, 902, 1988942953, 1555278970, 913671254,
        ]
        .map(F::from_u32);
        let evals_mat = RowMajorMatrix::new(evals.to_vec(), 1);
        let point = F::from_u16(100);
        let result = interpolate_coset(&evals_mat, shift, point, None);
        assert_eq!(result, vec![F::from_u16(10203)]);

        use p3_field::TwoAdicField;
        let n = evals.len();
        let k = log2_strict_usize(n);

        let denom: Vec<_> = F::two_adic_generator(k)
            .shifted_powers(shift)
            .take(n)
            .map(|w| point - w)
            .collect();

        let denom = batch_multiplicative_inverse(&denom);
        let result = interpolate_coset(&evals_mat, shift, point, Some(&denom));
        assert_eq!(result, vec![F::from_u16(10203)]);
    }
}
