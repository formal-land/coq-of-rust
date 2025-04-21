use alloc::vec::Vec;

use itertools::{Itertools, izip};
use p3_field::extension::ComplexExtendable;
use p3_field::{ExtensionField, PackedFieldExtension, batch_multiplicative_inverse, dot_product};
use p3_matrix::Matrix;
use p3_maybe_rayon::prelude::*;
use p3_util::log2_strict_usize;
use tracing::instrument;

use crate::domain::CircleDomain;
use crate::point::Point;
use crate::{CircleEvaluations, cfft_permute_slice};

/// Compute numerator and denominator of the "vanishing part" of the DEEP quotient
/// Section 6, Remark 21 of Circle Starks (page 30 of first edition PDF)
/// Re(1/v_gamma) + alpha^L Im(1/v_gamma)
/// (Other "part" is \bar g - \bar v_gamma)
pub(crate) fn deep_quotient_vanishing_part<F: ComplexExtendable, EF: ExtensionField<F>>(
    x: Point<F>,
    zeta: Point<EF>,
    alpha_pow_width: EF,
) -> (EF, EF) {
    let (re_v_zeta, im_v_zeta) = x.v_p(zeta);
    (
        re_v_zeta - alpha_pow_width * im_v_zeta,
        re_v_zeta.square() + im_v_zeta.square(),
    )
}

pub(crate) fn deep_quotient_reduce_row<F: ComplexExtendable, EF: ExtensionField<F>>(
    alpha: EF,
    x: Point<F>,
    zeta: Point<EF>,
    ps_at_x: &[F],
    ps_at_zeta: &[EF],
) -> EF {
    let (vp_num, vp_denom) =
        deep_quotient_vanishing_part(x, zeta, alpha.exp_u64(ps_at_x.len() as u64));
    (vp_num / vp_denom)
        * dot_product::<EF, _, _>(
            alpha.powers(),
            izip!(ps_at_x, ps_at_zeta).map(|(&p_at_x, &p_at_zeta)| -p_at_zeta + p_at_x),
        )
}

impl<F: ComplexExtendable, M: Matrix<F>> CircleEvaluations<F, M> {
    /// Same as `deep_quotient_reduce_row`, but reduces a whole matrix into a column, taking advantage of batch inverses.
    #[instrument(skip_all, fields(dims = %self.values.dimensions()))]
    pub(crate) fn deep_quotient_reduce<EF: ExtensionField<F>>(
        &self,
        alpha: EF,
        zeta: Point<EF>,
        ps_at_zeta: &[EF],
    ) -> Vec<EF> {
        let alpha_pow_width = alpha.exp_u64(self.values.width() as u64);
        let points = cfft_permute_slice(&self.domain.points().collect_vec());
        let (vp_nums, vp_denoms): (Vec<_>, Vec<_>) = points
            .into_iter()
            .map(|x| deep_quotient_vanishing_part(x, zeta, alpha_pow_width))
            .unzip();
        let vp_denom_invs = batch_multiplicative_inverse(&vp_denoms);

        // TODO: packed_alpha_powers and alpha_powers should be passed into deep_quotient_reduce instead of being recomputed every time.
        let packed_alpha_powers =
            EF::ExtensionPacking::packed_ext_powers_capped(alpha, self.values.width())
                .collect_vec();
        let alpha_powers =
            EF::ExtensionPacking::to_ext_iter(packed_alpha_powers.iter().copied()).collect_vec();

        let alpha_reduced_ps_at_zeta: EF =
            dot_product(alpha_powers.iter().copied(), ps_at_zeta.iter().copied());

        self.values
            .rowwise_packed_dot_product::<EF>(&packed_alpha_powers)
            .zip(vp_nums.into_par_iter())
            .zip(vp_denom_invs.into_par_iter())
            .map(|((reduced_ps_at_x, vp_num), vp_denom_inv)| {
                vp_num * vp_denom_inv * (reduced_ps_at_x - alpha_reduced_ps_at_zeta)
            })
            .collect()
    }
}

/// Given evaluations over lde_domain, extract the multiple of the vanishing poly of orig_domain
/// See Section 4.3, Lemma 6: < v_n, f > = 0 for any f in FFT space
/// So, we find the "error" (a scalar multiple of v_n) and remove it
/// |lde_domain| > |orig_domain|
#[instrument(skip_all, fields(bits = log2_strict_usize(lde.len())))]
pub fn extract_lambda<F: ComplexExtendable, EF: ExtensionField<F>>(
    lde: &mut [EF],
    log_blowup: usize,
) -> EF {
    let log_lde_size = log2_strict_usize(lde.len());
    // let num_cosets = 1 << (log_lde_size - orig_domain.log_n);

    // v_n is constant on cosets of the same size as orig_domain, so we only have
    // as many unique values as we have cosets.
    let v_d_init = CircleDomain::<F>::standard(log_lde_size)
        .points()
        .take(1 << log_blowup)
        .map(|p| p.v_n(log_lde_size - log_blowup))
        .collect_vec();

    // The unique values are repeated over the rest of the domain like
    // 0 1 2 .. n-1 n n n-1 .. 1 0 0 1 ..
    let v_d = v_d_init
        .iter()
        .chain(v_d_init.iter().rev())
        .cycle()
        .copied();

    // < v_d, v_d >
    // This formula was determined experimentally...
    let v_d_2 = F::TWO.exp_u64(log_lde_size as u64 - 1);

    let v_d = v_d.take(lde.len()).collect_vec();
    let v_d = cfft_permute_slice(&v_d);

    let lambda =
        dot_product::<EF, _, _>(lde.iter().copied(), v_d.iter().copied()) * v_d_2.inverse();

    for (y, v_x) in izip!(lde, v_d) {
        *y -= lambda * v_x;
    }

    lambda
}

#[cfg(test)]
mod tests {
    use alloc::vec;

    use p3_field::PrimeCharacteristicRing;
    use p3_field::extension::BinomialExtensionField;
    use p3_matrix::dense::RowMajorMatrix;
    use p3_mersenne_31::Mersenne31;
    use rand::rngs::SmallRng;
    use rand::{Rng, SeedableRng};

    use super::*;

    type F = Mersenne31;
    type EF = BinomialExtensionField<F, 3>;

    #[test]
    fn reduce_row_same_as_reduce_matrix() {
        let mut rng = SmallRng::seed_from_u64(1);
        let domain = CircleDomain::standard(5);
        let evals = CircleEvaluations::from_cfft_order(
            domain,
            RowMajorMatrix::<F>::rand(&mut rng, 1 << domain.log_n, 1 << 3),
        );

        let alpha: EF = rng.random();
        let zeta: Point<EF> = Point::from_projective_line(rng.random());
        let ps_at_zeta = evals.evaluate_at_point(zeta);

        let mat_reduced = evals.deep_quotient_reduce(alpha, zeta, &ps_at_zeta);
        let row_reduced = evals
            .to_natural_order()
            .rows()
            .zip(domain.points())
            .map(|(ps_at_x, x)| {
                deep_quotient_reduce_row(alpha, x, zeta, &ps_at_x.collect_vec(), &ps_at_zeta)
            })
            .collect_vec();
        assert_eq!(cfft_permute_slice(&mat_reduced), row_reduced);
    }

    #[test]
    fn reduce_evaluations_low_degree() {
        let mut rng = SmallRng::seed_from_u64(1);
        let log_n = 5;
        let log_blowup = 1;
        let evals = CircleEvaluations::from_cfft_order(
            CircleDomain::standard(log_n),
            RowMajorMatrix::<F>::rand(&mut rng, 1 << log_n, 1 << 3),
        );
        let lde = evals
            .clone()
            .extrapolate(CircleDomain::standard(log_n + log_blowup));
        assert!(lde.dim() <= (1 << log_n));

        let alpha: EF = rng.random();
        let zeta: Point<EF> = Point::from_projective_line(rng.random());

        let ps_at_zeta = evals.evaluate_at_point(zeta);
        let reduced0 = CircleEvaluations::<F>::from_cfft_order(
            CircleDomain::standard(log_n + log_blowup),
            RowMajorMatrix::new_col(lde.deep_quotient_reduce(alpha, zeta, &ps_at_zeta))
                .flatten_to_base(),
        );
        assert!(reduced0.dim() <= (1 << log_n) + 1);

        let not_ps_at_zeta = evals.evaluate_at_point(zeta.double());
        let reduced1 = CircleEvaluations::<F>::from_cfft_order(
            CircleDomain::standard(log_n + log_blowup),
            RowMajorMatrix::new_col(lde.deep_quotient_reduce(alpha, zeta, &not_ps_at_zeta))
                .flatten_to_base(),
        );
        assert!(reduced1.dim() > (1 << log_n) + 1);
    }

    #[test]
    fn reduce_multiple_evaluations() {
        let mut rng = SmallRng::seed_from_u64(1);
        let domain = CircleDomain::standard(5);
        let lde_domain = CircleDomain::standard(8);

        let alpha: EF = rng.random();
        let zeta: Point<EF> = Point::from_projective_line(rng.random());

        let mut alpha_offset = EF::ONE;
        let mut ros = vec![EF::ZERO; 1 << lde_domain.log_n];

        for _ in 0..4 {
            let evals = CircleEvaluations::from_cfft_order(
                domain,
                RowMajorMatrix::<F>::rand(&mut rng, 1 << domain.log_n, 1 << 3),
            );
            let ps_at_zeta = evals.evaluate_at_point(zeta);
            let lde = evals.extrapolate(lde_domain);
            assert!(lde.dim() <= (1 << domain.log_n) + 1);
            let mat_ros = lde.deep_quotient_reduce(alpha, zeta, &ps_at_zeta);
            for (ro, mat_ro) in izip!(&mut ros, mat_ros) {
                *ro += alpha_offset * mat_ro;
            }
            alpha_offset *= alpha.exp_u64(2 * lde.values.width() as u64);
        }

        let ros = CircleEvaluations::from_cfft_order(
            lde_domain,
            RowMajorMatrix::new_col(ros).flatten_to_base(),
        );
        assert!(ros.dim() <= (1 << domain.log_n) + 1);
    }

    #[test]
    fn test_extract_lambda() {
        let mut rng = SmallRng::seed_from_u64(1);
        let log_n = 5;
        for log_blowup in [1, 2, 3] {
            let mut coeffs = RowMajorMatrix::<F>::rand(&mut rng, (1 << log_n) + 1, 1);
            coeffs.pad_to_height(1 << (log_n + log_blowup), F::ZERO);

            let domain = CircleDomain::standard(log_n + log_blowup);
            let mut lde = CircleEvaluations::evaluate(domain, coeffs.clone()).values;

            let lambda = extract_lambda(&mut lde.values, log_blowup);
            assert_eq!(lambda, coeffs.get(1 << log_n, 0));

            let coeffs2 =
                CircleEvaluations::from_cfft_order(domain, RowMajorMatrix::new_col(lde.values))
                    .interpolate()
                    .values;
            assert_eq!(&coeffs2[..(1 << log_n)], &coeffs.values[..(1 << log_n)]);
            assert_eq!(lambda, coeffs.values[1 << log_n]);
            assert_eq!(coeffs2[1 << log_n], F::ZERO);
            assert_eq!(
                &coeffs2[(1 << log_n) + 1..],
                &coeffs.values[(1 << log_n) + 1..]
            );
        }
    }
}
