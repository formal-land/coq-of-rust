use alloc::vec;
use alloc::vec::Vec;

use itertools::{Itertools, iterate, izip};
use p3_commit::PolynomialSpace;
use p3_dft::{Butterfly, DifButterfly, DitButterfly, divide_by_height};
use p3_field::extension::ComplexExtendable;
use p3_field::{ExtensionField, Field, batch_multiplicative_inverse};
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use p3_maybe_rayon::prelude::*;
use p3_util::{log2_ceil_usize, log2_strict_usize, reverse_slice_index_bits};
use tracing::{debug_span, instrument};

use crate::domain::CircleDomain;
use crate::point::{Point, compute_lagrange_den_batched};
use crate::{CfftPermutable, CfftView, cfft_permute_index, cfft_permute_slice};

#[derive(Clone)]
pub struct CircleEvaluations<F, M = RowMajorMatrix<F>> {
    pub(crate) domain: CircleDomain<F>,
    pub(crate) values: M,
}

impl<F: Copy + Send + Sync, M: Matrix<F>> CircleEvaluations<F, M> {
    pub(crate) fn from_cfft_order(domain: CircleDomain<F>, values: M) -> Self {
        assert_eq!(1 << domain.log_n, values.height());
        Self { domain, values }
    }
    pub fn from_natural_order(
        domain: CircleDomain<F>,
        values: M,
    ) -> CircleEvaluations<F, CfftView<M>> {
        CircleEvaluations::from_cfft_order(domain, values.cfft_perm_rows())
    }
    pub fn to_cfft_order(self) -> M {
        self.values
    }
    pub fn to_natural_order(self) -> CfftView<M> {
        self.values.cfft_perm_rows()
    }
}

impl<F: ComplexExtendable, M: Matrix<F>> CircleEvaluations<F, M> {
    #[instrument(skip_all, fields(dims = %self.values.dimensions()))]
    pub fn interpolate(self) -> RowMajorMatrix<F> {
        let Self { domain, values } = self;
        let mut values = debug_span!("to_rmm").in_scope(|| values.to_row_major_matrix());

        let mut twiddles = debug_span!("twiddles").in_scope(|| {
            compute_twiddles(domain)
                .into_iter()
                .map(|ts| {
                    batch_multiplicative_inverse(&ts)
                        .into_iter()
                        .map(|t| DifButterfly(t))
                        .collect_vec()
                })
                .peekable()
        });

        assert_eq!(twiddles.len(), domain.log_n);

        let par_twiddles = twiddles
            .peeking_take_while(|ts| ts.len() >= desired_num_jobs())
            .collect_vec();
        if let Some(min_blks) = par_twiddles.last().map(|ts| ts.len()) {
            let max_blk_sz = values.height() / min_blks;
            debug_span!("par_layers", log_min_blks = log2_strict_usize(min_blks)).in_scope(|| {
                values
                    .par_row_chunks_exact_mut(max_blk_sz)
                    .enumerate()
                    .for_each(|(chunk_i, submat)| {
                        for ts in &par_twiddles {
                            let twiddle_chunk_sz = ts.len() / min_blks;
                            let twiddle_chunk = &ts
                                [(twiddle_chunk_sz * chunk_i)..(twiddle_chunk_sz * (chunk_i + 1))];
                            serial_layer(submat.values, twiddle_chunk);
                        }
                    });
            });
        }

        for ts in twiddles {
            par_within_blk_layer(&mut values.values, &ts);
        }

        // TODO: omit this?
        divide_by_height(&mut values);
        values
    }

    #[instrument(skip_all, fields(dims = %self.values.dimensions()))]
    pub fn extrapolate(
        self,
        target_domain: CircleDomain<F>,
    ) -> CircleEvaluations<F, RowMajorMatrix<F>> {
        assert!(target_domain.log_n >= self.domain.log_n);
        CircleEvaluations::evaluate(target_domain, self.interpolate())
    }

    pub fn evaluate_at_point<EF: ExtensionField<F>>(&self, point: Point<EF>) -> Vec<EF> {
        // Compute z_H
        let lagrange_num = self.domain.vanishing_poly(point);

        // Permute the domain to get it into the right format.
        let permuted_points = cfft_permute_slice(&self.domain.points().collect_vec());

        // Compute the lagrange denominators. This is batched as it lets us make use of batched_multiplicative_inverse.
        let lagrange_den = compute_lagrange_den_batched(&permuted_points, point, self.domain.log_n);

        // The columnwise_dot_product here consumes about 5% of the runtime for example prove_poseidon2_m31_keccak.
        // Definitely something worth optimising further.
        self.values
            .columnwise_dot_product(&lagrange_den)
            .into_iter()
            .map(|x| x * lagrange_num)
            .collect_vec()
    }

    #[cfg(test)]
    pub(crate) fn dim(&self) -> usize
    where
        M: Clone,
    {
        let coeffs = self.clone().interpolate();
        for (i, mut row) in coeffs.rows().enumerate() {
            if row.all(|x| x.is_zero()) {
                return i;
            }
        }
        coeffs.height()
    }
}

impl<F: ComplexExtendable> CircleEvaluations<F, RowMajorMatrix<F>> {
    #[instrument(skip_all, fields(dims = %coeffs.dimensions()))]
    pub fn evaluate(domain: CircleDomain<F>, mut coeffs: RowMajorMatrix<F>) -> Self {
        let log_n = log2_strict_usize(coeffs.height());
        assert!(log_n <= domain.log_n);

        if log_n < domain.log_n {
            // We could simply pad coeffs like this:
            // coeffs.pad_to_height(target_domain.size(), F::ZERO);
            // But the first `added_bits` layers will simply fill out the zeros
            // with the lower order values. (In `DitButterfly`, `x_2` is 0, so
            // both `x_1` and `x_2` are set to `x_1`).
            // So instead we directly repeat the coeffs and skip the initial layers.
            debug_span!("extend coeffs").in_scope(|| {
                coeffs.values.reserve(domain.size() * coeffs.width());
                for _ in log_n..domain.log_n {
                    coeffs.values.extend_from_within(..);
                }
            });
        }
        assert_eq!(coeffs.height(), 1 << domain.log_n);

        let mut twiddles = debug_span!("twiddles").in_scope(|| {
            compute_twiddles(domain)
                .into_iter()
                .map(|ts| ts.into_iter().map(|t| DitButterfly(t)).collect_vec())
                .rev()
                .skip(domain.log_n - log_n)
                .peekable()
        });

        for ts in twiddles.peeking_take_while(|ts| ts.len() < desired_num_jobs()) {
            par_within_blk_layer(&mut coeffs.values, &ts);
        }

        let par_twiddles = twiddles.collect_vec();
        if let Some(min_blks) = par_twiddles.first().map(|ts| ts.len()) {
            let max_blk_sz = coeffs.height() / min_blks;
            debug_span!("par_layers", log_min_blks = log2_strict_usize(min_blks)).in_scope(|| {
                coeffs
                    .par_row_chunks_exact_mut(max_blk_sz)
                    .enumerate()
                    .for_each(|(chunk_i, submat)| {
                        for ts in &par_twiddles {
                            let twiddle_chunk_sz = ts.len() / min_blks;
                            let twiddle_chunk = &ts
                                [(twiddle_chunk_sz * chunk_i)..(twiddle_chunk_sz * (chunk_i + 1))];
                            serial_layer(submat.values, twiddle_chunk);
                        }
                    });
            });
        }

        Self::from_cfft_order(domain, coeffs)
    }
}

#[inline]
fn serial_layer<F: Field, B: Butterfly<F>>(values: &mut [F], twiddles: &[B]) {
    let blk_sz = values.len() / twiddles.len();
    for (&t, blk) in izip!(twiddles, values.chunks_exact_mut(blk_sz)) {
        let (lo, hi) = blk.split_at_mut(blk_sz / 2);
        t.apply_to_rows(lo, hi);
    }
}

#[inline]
#[instrument(level = "debug", skip_all, fields(log_blks = log2_strict_usize(twiddles.len())))]
fn par_within_blk_layer<F: Field, B: Butterfly<F>>(values: &mut [F], twiddles: &[B]) {
    let blk_sz = values.len() / twiddles.len();
    for (&t, blk) in izip!(twiddles, values.chunks_exact_mut(blk_sz)) {
        let (lo, hi) = blk.split_at_mut(blk_sz / 2);
        let job_sz = core::cmp::max(1, lo.len() >> log2_ceil_usize(desired_num_jobs()));
        lo.par_chunks_mut(job_sz)
            .zip(hi.par_chunks_mut(job_sz))
            .for_each(|(lo_job, hi_job)| t.apply_to_rows(lo_job, hi_job));
    }
}

#[inline]
fn desired_num_jobs() -> usize {
    16 * current_num_threads()
}

impl<F: ComplexExtendable> CircleDomain<F> {
    pub(crate) fn y_twiddles(&self) -> Vec<F> {
        let mut ys = self.coset0().map(|p| p.y).collect_vec();
        reverse_slice_index_bits(&mut ys);
        ys
    }
    pub(crate) fn nth_y_twiddle(&self, index: usize) -> F {
        self.nth_point(cfft_permute_index(index << 1, self.log_n)).y
    }
    pub(crate) fn x_twiddles(&self, layer: usize) -> Vec<F> {
        let generator = self.subgroup_generator() * (1 << layer);
        let shift = self.shift * (1 << layer);
        let mut xs = iterate(shift, move |&p| p + generator)
            .map(|p| p.x)
            .take(1 << (self.log_n - layer - 2))
            .collect_vec();
        reverse_slice_index_bits(&mut xs);
        xs
    }
    pub(crate) fn nth_x_twiddle(&self, index: usize) -> F {
        (self.shift + self.subgroup_generator() * index).x
    }
}

fn compute_twiddles<F: ComplexExtendable>(domain: CircleDomain<F>) -> Vec<Vec<F>> {
    assert!(domain.log_n >= 1);
    let mut pts = domain.coset0().collect_vec();
    reverse_slice_index_bits(&mut pts);
    let mut twiddles = vec![pts.iter().map(|p| p.y).collect_vec()];
    if domain.log_n >= 2 {
        twiddles.push(pts.iter().step_by(2).map(|p| p.x).collect_vec());
        for i in 0..(domain.log_n - 2) {
            let prev = twiddles.last().unwrap();
            assert_eq!(prev.len(), 1 << (domain.log_n - 2 - i));
            let cur = prev
                .iter()
                .step_by(2)
                .map(|x| x.square().double() - F::ONE)
                .collect_vec();
            twiddles.push(cur);
        }
    }
    twiddles
}

pub fn circle_basis<F: Field>(p: Point<F>, log_n: usize) -> Vec<F> {
    let mut b = vec![F::ONE, p.y];
    let mut x = p.x;
    for _ in 0..(log_n - 1) {
        for i in 0..b.len() {
            b.push(b[i] * x);
        }
        x = x.square().double() - F::ONE;
    }
    assert_eq!(b.len(), 1 << log_n);
    b
}

#[cfg(test)]
mod tests {
    use itertools::iproduct;
    use p3_field::extension::BinomialExtensionField;
    use p3_mersenne_31::Mersenne31;
    use rand::rngs::SmallRng;
    use rand::{Rng, SeedableRng};

    use super::*;

    type F = Mersenne31;
    type EF = BinomialExtensionField<F, 3>;

    #[test]
    fn test_cfft_icfft() {
        let mut rng = SmallRng::seed_from_u64(1);
        for (log_n, width) in iproduct!(2..5, [1, 4, 11]) {
            let shift = Point::generator(F::CIRCLE_TWO_ADICITY) * (rng.random::<u16>() as usize);
            let domain = CircleDomain::new(log_n, shift);
            let trace = RowMajorMatrix::<F>::rand(&mut rng, 1 << log_n, width);
            let coeffs = CircleEvaluations::from_natural_order(domain, trace.clone()).interpolate();
            assert_eq!(
                CircleEvaluations::evaluate(domain, coeffs.clone())
                    .to_natural_order()
                    .to_row_major_matrix(),
                trace,
                "icfft(cfft(evals)) is identity",
            );
            for (i, pt) in domain.points().enumerate() {
                assert_eq!(
                    &*trace.row_slice(i),
                    coeffs.columnwise_dot_product(&circle_basis(pt, log_n)),
                    "coeffs can be evaluated with circle_basis",
                );
            }
        }
    }

    #[test]
    fn test_extrapolation() {
        let mut rng = SmallRng::seed_from_u64(1);
        for (log_n, log_blowup) in iproduct!(2..5, [1, 2, 3]) {
            let evals = CircleEvaluations::<F>::from_natural_order(
                CircleDomain::standard(log_n),
                RowMajorMatrix::rand(&mut rng, 1 << log_n, 11),
            );
            let lde = evals
                .clone()
                .extrapolate(CircleDomain::standard(log_n + log_blowup));

            let coeffs = evals.interpolate();
            let lde_coeffs = lde.interpolate();

            for r in 0..coeffs.height() {
                assert_eq!(&*coeffs.row_slice(r), &*lde_coeffs.row_slice(r));
            }
            for r in coeffs.height()..lde_coeffs.height() {
                assert!(lde_coeffs.row(r).all(|x| x.is_zero()));
            }
        }
    }

    #[test]
    fn eval_at_point_matches_cfft() {
        let mut rng = SmallRng::seed_from_u64(1);
        for (log_n, width) in iproduct!(2..5, [1, 4, 11]) {
            let evals = CircleEvaluations::<F>::from_natural_order(
                CircleDomain::standard(log_n),
                RowMajorMatrix::rand(&mut rng, 1 << log_n, width),
            );

            let pt = Point::<EF>::from_projective_line(rng.random());

            assert_eq!(
                evals.clone().evaluate_at_point(pt),
                evals
                    .interpolate()
                    .columnwise_dot_product(&circle_basis(pt, log_n))
            );
        }
    }

    #[test]
    fn eval_at_point_matches_lde() {
        let mut rng = SmallRng::seed_from_u64(1);
        for (log_n, width, log_blowup) in iproduct!(2..8, [1, 4, 11], [1, 2]) {
            let evals = CircleEvaluations::<F>::from_natural_order(
                CircleDomain::standard(log_n),
                RowMajorMatrix::rand(&mut rng, 1 << log_n, width),
            );
            let lde = evals
                .clone()
                .extrapolate(CircleDomain::standard(log_n + log_blowup));
            let zeta = Point::<EF>::from_projective_line(rng.random());
            assert_eq!(evals.evaluate_at_point(zeta), lde.evaluate_at_point(zeta));
            assert_eq!(
                evals.evaluate_at_point(zeta),
                evals
                    .interpolate()
                    .columnwise_dot_product(&circle_basis(zeta, log_n))
            );
            assert_eq!(
                lde.evaluate_at_point(zeta),
                lde.interpolate()
                    .columnwise_dot_product(&circle_basis(zeta, log_n + log_blowup))
            );
        }
    }
}
