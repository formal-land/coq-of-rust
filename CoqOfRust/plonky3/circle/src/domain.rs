use alloc::vec;
use alloc::vec::Vec;

use itertools::{Itertools, iterate};
use p3_commit::{LagrangeSelectors, PolynomialSpace};
use p3_field::ExtensionField;
use p3_field::extension::ComplexExtendable;
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use p3_util::{log2_ceil_usize, log2_strict_usize};
use tracing::instrument;

use crate::point::Point;

/// A twin-coset of the circle group on F. It has a power-of-two size and an arbitrary shift.
///
/// X is generator, O is the first coset, goes counterclockwise
/// ```text
///   O X .
///  .     .
/// .       O <- start = shift
/// .   .   - (1,0)
/// O       .
///  .     .
///   . . O
/// ```
///
/// For ordering reasons, the other half will start at gen / shift:
/// ```text
///   . X O  <- start = gen/shift
///  .     .
/// O       .
/// .   .   - (1,0)
/// .       O
///  .     .
///   O . .
/// ```
///
/// The full domain is the interleaving of these two cosets
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct CircleDomain<F> {
    // log_n corresponds to the log size of the WHOLE domain
    pub(crate) log_n: usize,
    pub(crate) shift: Point<F>,
}

impl<F: ComplexExtendable> CircleDomain<F> {
    pub const fn new(log_n: usize, shift: Point<F>) -> Self {
        Self { log_n, shift }
    }
    pub fn standard(log_n: usize) -> Self {
        Self {
            log_n,
            shift: Point::generator(log_n + 1),
        }
    }
    fn is_standard(&self) -> bool {
        self.shift == Point::generator(self.log_n + 1)
    }
    pub(crate) fn subgroup_generator(&self) -> Point<F> {
        Point::generator(self.log_n - 1)
    }
    pub(crate) fn coset0(&self) -> impl Iterator<Item = Point<F>> {
        let g = self.subgroup_generator();
        iterate(self.shift, move |&p| p + g).take(1 << (self.log_n - 1))
    }
    fn coset1(&self) -> impl Iterator<Item = Point<F>> {
        let g = self.subgroup_generator();
        iterate(g - self.shift, move |&p| p + g).take(1 << (self.log_n - 1))
    }
    pub(crate) fn points(&self) -> impl Iterator<Item = Point<F>> {
        self.coset0().interleave(self.coset1())
    }
    pub(crate) fn nth_point(&self, idx: usize) -> Point<F> {
        let (idx, lsb) = (idx >> 1, idx & 1);
        if lsb == 0 {
            self.shift + self.subgroup_generator() * idx
        } else {
            -self.shift + self.subgroup_generator() * (idx + 1)
        }
    }

    pub(crate) fn vanishing_poly<EF: ExtensionField<F>>(&self, at: Point<EF>) -> EF {
        at.v_n(self.log_n) - self.shift.v_n(self.log_n)
    }

    pub(crate) fn s_p<EF: ExtensionField<F>>(&self, p: Point<F>, at: Point<EF>) -> EF {
        self.vanishing_poly(at) / p.v_tilde_p(at)
    }

    pub(crate) fn s_p_normalized<EF: ExtensionField<F>>(&self, p: Point<F>, at: Point<EF>) -> EF {
        self.vanishing_poly(at) / (p.v_tilde_p(at) * p.s_p_at_p(self.log_n))
    }
}

impl<F: ComplexExtendable> PolynomialSpace for CircleDomain<F> {
    type Val = F;

    fn size(&self) -> usize {
        1 << self.log_n
    }

    fn first_point(&self) -> Self::Val {
        self.shift.to_projective_line().unwrap()
    }

    fn next_point<Ext: ExtensionField<Self::Val>>(&self, x: Ext) -> Option<Ext> {
        // Only in standard position do we have an algebraic expression to access the next point.
        if self.is_standard() {
            (Point::from_projective_line(x) + Point::generator(self.log_n)).to_projective_line()
        } else {
            None
        }
    }

    fn create_disjoint_domain(&self, min_size: usize) -> Self {
        // Right now we simply guarantee the domain is disjoint by returning a
        // larger standard position coset, which is fine because we always ask for a larger
        // domain. If we wanted good performance for a disjoint domain of the same size,
        // we could change the shift. Also we could support nonstandard twin cosets.
        assert!(
            self.is_standard(),
            "create_disjoint_domain not currently supported for nonstandard twin cosets"
        );
        let log_n = log2_ceil_usize(min_size);
        // Any standard position coset that is not the same size as us will be disjoint.
        Self::standard(if log_n == self.log_n {
            log_n + 1
        } else {
            log_n
        })
    }

    /// Decompose a domain into disjoint twin-cosets.
    fn split_domains(&self, num_chunks: usize) -> Vec<Self> {
        assert!(self.is_standard());
        let log_chunks = log2_strict_usize(num_chunks);
        assert!(log_chunks <= self.log_n);
        self.points()
            .take(num_chunks)
            .map(|shift| Self {
                log_n: self.log_n - log_chunks,
                shift,
            })
            .collect()
    }

    fn split_evals(
        &self,
        num_chunks: usize,
        evals: RowMajorMatrix<Self::Val>,
    ) -> Vec<RowMajorMatrix<Self::Val>> {
        let log_chunks = log2_strict_usize(num_chunks);
        assert!(evals.height() >> (log_chunks + 1) >= 1);
        let width = evals.width();
        let mut values: Vec<Vec<Self::Val>> = vec![vec![]; num_chunks];
        evals
            .rows()
            .enumerate()
            .for_each(|(i, row)| values[forward_backward_index(i, num_chunks)].extend(row));
        values
            .into_iter()
            .map(|v| RowMajorMatrix::new(v, width))
            .collect()
    }

    fn vanishing_poly_at_point<Ext: ExtensionField<Self::Val>>(&self, point: Ext) -> Ext {
        self.vanishing_poly(Point::from_projective_line(point))
    }

    fn selectors_at_point<Ext: ExtensionField<Self::Val>>(
        &self,
        point: Ext,
    ) -> LagrangeSelectors<Ext> {
        let point = Point::from_projective_line(point);
        LagrangeSelectors {
            is_first_row: self.s_p(self.shift, point),
            is_last_row: self.s_p(-self.shift, point),
            is_transition: Ext::ONE - self.s_p_normalized(-self.shift, point),
            inv_vanishing: self.vanishing_poly(point).inverse(),
        }
    }

    /*
    chunks=2:

          1 . 1
         .     .
        0       0 <-- start
        .   .   - (1,0)
        0       0
         .     .
          1 . 1


    idx -> which chunk to put it in:
    chunks=2: 0 1 1 0 0 1 1 0 0 1 1 0 0 1 1 0
    chunks=4: 0 1 2 3 3 2 1 0 0 1 2 3 3 2 1 0
    */
    // wow, really slow!
    // todo: batch inverses
    #[instrument(skip_all, fields(log_n = %coset.log_n))]
    fn selectors_on_coset(&self, coset: Self) -> LagrangeSelectors<Vec<Self::Val>> {
        let sels = coset
            .points()
            .map(|p| self.selectors_at_point(p.to_projective_line().unwrap()))
            .collect_vec();
        LagrangeSelectors {
            is_first_row: sels.iter().map(|s| s.is_first_row).collect(),
            is_last_row: sels.iter().map(|s| s.is_last_row).collect(),
            is_transition: sels.iter().map(|s| s.is_transition).collect(),
            inv_vanishing: sels.iter().map(|s| s.inv_vanishing).collect(),
        }
    }
}

// 0 1 2 .. len-1 len len len-1 .. 1 0 0 1 ..
const fn forward_backward_index(mut i: usize, len: usize) -> usize {
    i %= 2 * len;
    if i < len { i } else { 2 * len - 1 - i }
}

#[cfg(test)]
mod tests {
    use core::iter;

    use hashbrown::HashSet;
    use itertools::izip;
    use p3_field::{PrimeCharacteristicRing, batch_multiplicative_inverse};
    use p3_mersenne_31::Mersenne31;
    use rand::SeedableRng;
    use rand::rngs::SmallRng;

    use super::*;
    use crate::CircleEvaluations;

    fn assert_is_twin_coset<F: ComplexExtendable>(d: CircleDomain<F>) {
        let pts = d.points().collect_vec();
        let half_n = pts.len() >> 1;
        for (&l, &r) in izip!(&pts[..half_n], pts[half_n..].iter().rev()) {
            assert_eq!(l, -r);
        }
    }

    fn do_test_circle_domain(log_n: usize, width: usize) {
        let n = 1 << log_n;

        type F = Mersenne31;
        let d = CircleDomain::<F>::standard(log_n);

        // we can move around the circle and end up where we started
        let p0 = d.first_point();
        let mut p1 = p0;
        for i in 0..(n - 1) {
            // nth_point is correct
            assert_eq!(Point::from_projective_line(p1), d.nth_point(i));
            p1 = d.next_point(p1).unwrap();
            assert_ne!(p1, p0);
        }
        assert_eq!(d.next_point(p1).unwrap(), p0);

        // .points() is the same as first_point -> next_point
        let mut uni_point = d.first_point();
        for p in d.points() {
            assert_eq!(Point::from_projective_line(uni_point), p);
            uni_point = d.next_point(uni_point).unwrap();
        }

        // disjoint domain is actually disjoint, and large enough
        let seen: HashSet<Point<F>> = d.points().collect();
        for disjoint_size in [10, 100, n - 5, n + 15] {
            let dd = d.create_disjoint_domain(disjoint_size);
            assert!(dd.size() >= disjoint_size);
            for pt in dd.points() {
                assert!(!seen.contains(&pt));
            }
        }

        // zp is zero
        for p in d.points() {
            assert_eq!(
                d.vanishing_poly_at_point(p.to_projective_line().unwrap()),
                F::ZERO
            );
        }

        let mut rng = SmallRng::seed_from_u64(1);

        // split domains
        let evals = RowMajorMatrix::rand(&mut rng, n, width);
        let orig: Vec<(Point<F>, Vec<F>)> = d
            .points()
            .zip(evals.rows().map(|r| r.collect_vec()))
            .collect();
        for num_chunks in [1, 2, 4, 8] {
            let mut combined = vec![];

            let sds = d.split_domains(num_chunks);
            assert_eq!(sds.len(), num_chunks);
            let ses = d.split_evals(num_chunks, evals.clone());
            assert_eq!(ses.len(), num_chunks);
            for (sd, se) in izip!(sds, ses) {
                // Split domains are twin cosets
                assert_is_twin_coset(sd);
                // Split domains have correct size wrt original domain
                assert_eq!(sd.size() * num_chunks, d.size());
                assert_eq!(se.width(), evals.width());
                assert_eq!(se.height() * num_chunks, d.size());
                combined.extend(sd.points().zip(se.rows().map(|r| r.collect_vec())));
            }
            // Union of split domains and evals is the original domain and evals
            assert_eq!(
                orig.iter().map(|x| x.0).collect::<HashSet<_>>(),
                combined.iter().map(|x| x.0).collect::<HashSet<_>>(),
                "union of split domains is orig domain"
            );
            assert_eq!(
                orig.iter().map(|x| &x.1).collect::<HashSet<_>>(),
                combined.iter().map(|x| &x.1).collect::<HashSet<_>>(),
                "union of split evals is orig evals"
            );
            assert_eq!(
                orig.iter().collect::<HashSet<_>>(),
                combined.iter().collect::<HashSet<_>>(),
                "split domains and evals correspond to orig domains and evals"
            );
        }
    }

    #[test]
    fn selectors() {
        type F = Mersenne31;
        let log_n = 8;
        let n = 1 << log_n;

        let d = CircleDomain::<F>::standard(log_n);
        let coset = d.create_disjoint_domain(n);
        let sels = d.selectors_on_coset(coset);

        // selectors_on_coset matches selectors_at_point
        let mut pt = coset.first_point();
        for i in 0..coset.size() {
            let pt_sels = d.selectors_at_point(pt);
            assert_eq!(sels.is_first_row[i], pt_sels.is_first_row);
            assert_eq!(sels.is_last_row[i], pt_sels.is_last_row);
            assert_eq!(sels.is_transition[i], pt_sels.is_transition);
            assert_eq!(sels.inv_vanishing[i], pt_sels.inv_vanishing);
            pt = coset.next_point(pt).unwrap();
        }

        let coset_to_d = |evals: &[F]| {
            let evals = CircleEvaluations::from_natural_order(
                coset,
                RowMajorMatrix::new_col(evals.to_vec()),
            );
            let coeffs = evals.interpolate().to_row_major_matrix();
            let (lo, hi) = coeffs.split_rows(n);
            assert_eq!(hi.values, vec![F::ZERO; n]);
            CircleEvaluations::evaluate(d, lo.to_row_major_matrix())
                .to_natural_order()
                .to_row_major_matrix()
                .values
        };

        // Nonzero at first point, zero everywhere else on domain
        let is_first_row = coset_to_d(&sels.is_first_row);
        assert_ne!(is_first_row[0], F::ZERO);
        assert_eq!(&is_first_row[1..], &vec![F::ZERO; n - 1]);

        // Nonzero at last point, zero everywhere else on domain
        let is_last_row = coset_to_d(&sels.is_last_row);
        assert_eq!(&is_last_row[..n - 1], &vec![F::ZERO; n - 1]);
        assert_ne!(is_last_row[n - 1], F::ZERO);

        // Nonzero everywhere on domain but last point
        let is_transition = coset_to_d(&sels.is_transition);
        assert_ne!(&is_transition[..n - 1], &vec![F::ZERO; n - 1]);
        assert_eq!(is_transition[n - 1], F::ZERO);

        // Vanishing polynomial coefficients look like [0.. (n times), 1, 0.. (n-1 times)]
        let z_coeffs = CircleEvaluations::from_natural_order(
            coset,
            RowMajorMatrix::new_col(batch_multiplicative_inverse(&sels.inv_vanishing)),
        )
        .interpolate()
        .to_row_major_matrix()
        .values;
        assert_eq!(
            z_coeffs,
            iter::empty()
                .chain(iter::repeat_n(F::ZERO, n))
                .chain(iter::once(F::ONE))
                .chain(iter::repeat_n(F::ZERO, n - 1))
                .collect_vec()
        );
    }

    #[test]
    fn test_circle_domain() {
        do_test_circle_domain(4, 8);
        do_test_circle_domain(10, 32);
    }
}
