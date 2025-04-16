use alloc::vec::Vec;

use itertools::Itertools;
use p3_field::coset::TwoAdicMultiplicativeCoset;
use p3_field::{
    ExtensionField, Field, TwoAdicField, batch_multiplicative_inverse,
    cyclic_subgroup_coset_known_order,
};
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use p3_util::{log2_ceil_usize, log2_strict_usize};

/// Given a `PolynomialSpace`, `S`, and a subset `R`, a Lagrange selector `P_R` is
/// a polynomial which is not equal to `0` for every element in `R` but is equal
/// to `0` for every element of `S` not in `R`.
///
/// This struct contains evaluations of several Lagrange selectors for a fixed
/// `PolynomialSpace` over some collection of points disjoint from that
/// `PolynomialSpace`.
///
/// The Lagrange selector is normalized if it is equal to `1` for every element in `R`.
/// The LagrangeSelectors given here are not normalized.
#[derive(Debug)]
pub struct LagrangeSelectors<T> {
    /// A Lagrange selector corresponding to the first point in the space.
    pub is_first_row: T,
    /// A Lagrange selector corresponding to the last point in the space.
    pub is_last_row: T,
    /// A Lagrange selector corresponding the subset of all but the last point.
    pub is_transition: T,
    /// The inverse of the vanishing polynomial which is a Lagrange selector corresponding to the empty set
    pub inv_vanishing: T,
}

/// Fixing a field, `F`, `PolynomialSpace<Val = F>` denotes an indexed subset of `F^n`
/// with some additional algebraic structure.
///
/// We do not expect `PolynomialSpace` to store this subset, instead it usually contains
/// some associated data which allows it to generate the subset or pieces of it.
///
/// Each `PolynomialSpace` should be part of a family of similar spaces for some
/// collection of sizes (usually powers of two). Any space other than at the smallest size
/// should be decomposable into a disjoint collection of smaller spaces. Additionally, the
/// set of all `PolynomialSpace` of a given size should form a disjoint partition of some
/// subset of `F^n` which supports a group structure.
///
/// The canonical example of a `PolynomialSpace` is a coset `gH` of
/// a two-adic subgroup `H` of the multiplicative group `F*`. This satisfies the properties
/// above as cosets partition the group and decompose as `gH = g(H^2) u gh(H^2)` for `h` any
/// generator of `H`.
///
/// The other example in this code base is twin cosets which are sets of the form `gH u g^{-1}H`.
/// The decomposition above extends easily to this case as `h` is a generator if and only if `h^{-1}`
/// is and so `gH u g^{-1}H = (g(H^2) u g^{-1}(H^2)) u (gh(H^2) u (gh)^{-1}(H^2))`.
pub trait PolynomialSpace: Copy {
    /// The base field `F`.
    type Val: Field;

    /// The number of elements of the space.
    fn size(&self) -> usize;

    /// The first point in the space.
    fn first_point(&self) -> Self::Val;

    /// An algebraic function which takes the i'th element of the space and returns
    /// the (i+1)'th evaluated on the given point.
    ///
    /// When `PolynomialSpace` corresponds to a coset, `gH` this
    /// function is multiplication by `h` for a chosen generator `h` of `H`.
    ///
    /// This function may not exist for other classes of `PolynomialSpace` in which
    /// case this will return `None`.
    fn next_point<Ext: ExtensionField<Self::Val>>(&self, x: Ext) -> Option<Ext>;

    /// Return another `PolynomialSpace` with size at least `min_size` disjoint from this space.
    ///
    /// When working with spaces of power of two size, this will return a space of size `2^ceil(log_2(min_size))`.
    /// This will fail if `min_size` is too large. In particular, `log_2(min_size)` should be
    /// smaller than the `2`-adicity of the field.
    ///
    /// This fixes a canonical choice for prover/verifier determinism and LDE caching.
    fn create_disjoint_domain(&self, min_size: usize) -> Self;

    /// Split the `PolynomialSpace` into `num_chunks` smaller `PolynomialSpaces` of equal size.
    ///
    /// `num_chunks` must divide `self.size()` (which usually forces it to be a power of 2.) or
    /// this function will panic.
    fn split_domains(&self, num_chunks: usize) -> Vec<Self>;

    /// Split a set of polynomial evaluations over this `PolynomialSpace` into a vector
    /// of polynomial evaluations over each `PolynomialSpace` generated from `split_domains`.
    ///
    /// `evals.height()` must equal `self.size()` and `num_chunks` must divide `self.size()`.
    fn split_evals(
        &self,
        num_chunks: usize,
        evals: RowMajorMatrix<Self::Val>,
    ) -> Vec<RowMajorMatrix<Self::Val>>;

    /// Compute the vanishing polynomial of the space, evaluated at the given point.
    ///
    /// This is a polynomial which evaluates to `0` on every point of the
    /// space `self` and has degree equal to `self.size()`. In other words it is
    /// a choice of element of the defining ideal of the given set with this extra
    /// degree property.
    ///
    /// In the univariate case, it is equal, up to a linear factor, to the product over
    /// all elements `x`, of `(X - x)`. In particular this implies it will not evaluate
    /// to `0` at any point not in `self`.
    fn vanishing_poly_at_point<Ext: ExtensionField<Self::Val>>(&self, point: Ext) -> Ext;

    /// Compute several Lagrange selectors at a given point.
    /// - The Lagrange selector of the first point.
    /// - The Lagrange selector of the last point.
    /// - The Lagrange selector of everything but the last point.
    /// - The inverse of the vanishing polynomial.
    ///
    /// Note that these may not be normalized.
    fn selectors_at_point<Ext: ExtensionField<Self::Val>>(
        &self,
        point: Ext,
    ) -> LagrangeSelectors<Ext>;

    /// Compute several Lagrange selectors at all points of the given disjoint `PolynomialSpace`.
    /// - The Lagrange selector of the first point.
    /// - The Lagrange selector of the last point.
    /// - The Lagrange selector of everything but the last point.
    /// - The inverse of the vanishing polynomial.
    ///
    /// Note that these may not be normalized.
    fn selectors_on_coset(&self, coset: Self) -> LagrangeSelectors<Vec<Self::Val>>;
}

impl<Val: TwoAdicField> PolynomialSpace for TwoAdicMultiplicativeCoset<Val> {
    type Val = Val;

    fn size(&self) -> usize {
        self.size()
    }

    fn first_point(&self) -> Self::Val {
        self.shift()
    }

    /// Getting the next point corresponds to multiplication by the generator.
    fn next_point<Ext: ExtensionField<Val>>(&self, x: Ext) -> Option<Ext> {
        Some(x * self.subgroup_generator())
    }

    /// Given the coset `gH`, return the disjoint coset `gfK` where `f`
    /// is a fixed generator of `F^*` and `K` is the unique two-adic subgroup
    /// of with size `2^(ceil(log_2(min_size)))`.
    ///
    /// # Panics
    ///
    /// This will panic if `min_size` > `1 << Val::TWO_ADICITY`.
    fn create_disjoint_domain(&self, min_size: usize) -> Self {
        // We provide a short proof that these cosets are always disjoint:
        //
        // Assume without loss of generality that `|H| <= min_size <= |K|`.
        // Then we know that `gH` is entirely contained in `gK`. As cosets are
        // either equal or disjoint, this means that `gH` is disjoint from `g'K`
        // for every `g'` not contained in `gK`. As `f` is a generator of `F^*`
        // it does not lie in `K` and so `gf` cannot lie in `gK`.
        //
        // Thus `gH` and `gfK` are disjoint.

        // This panics if (and only if) `min_size` > `1 << Val::TWO_ADICITY`.
        Self::new(self.shift() * Val::GENERATOR, log2_ceil_usize(min_size)).unwrap()
    }

    /// Given the coset `gH` and generator `h` of `H`, let `K = H^{num_chunks}`
    /// be the unique group of order `|H|/num_chunks`.
    ///
    /// Then we decompose `gH` into `gK, ghK, gh^2K, ..., gh^{num_chunks}K`.
    fn split_domains(&self, num_chunks: usize) -> Vec<Self> {
        let log_chunks = log2_strict_usize(num_chunks);
        debug_assert!(log_chunks <= self.log_size());
        (0..num_chunks)
            .map(|i| {
                Self::new(
                    self.shift() * self.subgroup_generator().exp_u64(i as u64),
                    self.log_size() - log_chunks,
                )
                .unwrap() // This won't panic as `self.log_size() - log_chunks < self.log_size() < Val::TWO_ADICITY`
            })
            .collect()
    }

    fn split_evals(
        &self,
        num_chunks: usize,
        evals: RowMajorMatrix<Self::Val>,
    ) -> Vec<RowMajorMatrix<Self::Val>> {
        debug_assert_eq!(evals.height(), self.size());
        debug_assert!(log2_strict_usize(num_chunks) <= self.log_size());
        // todo less copy
        (0..num_chunks)
            .map(|i| {
                evals
                    .as_view()
                    .vertically_strided(num_chunks, i)
                    .to_row_major_matrix()
            })
            .collect()
    }

    /// Compute the vanishing polynomial at the given point:
    ///
    /// `Z_{gH}(X) = g^{-|H|}\prod_{h \in H} (X - gh) = (g^{-1}X)^|H| - 1`
    fn vanishing_poly_at_point<Ext: ExtensionField<Val>>(&self, point: Ext) -> Ext {
        (point * self.shift().inverse()).exp_power_of_2(self.log_size()) - Ext::ONE
    }

    /// Compute several Lagrange selectors at the given point:
    ///
    /// Defining the vanishing polynomial by `Z_{gH}(X) = g^{-|H|}\prod_{h \in H} (X - gh) = (g^{-1}X)^|H| - 1` return:
    /// - `Z_{gH}(X)/(g^{-1}X - 1)`: The Lagrange selector of the point `g`.
    /// - `Z_{gH}(X)/(g^{-1}X - h^{-1})`: The Lagrange selector of the point `gh^{-1}` where `h` is the generator of `H`.
    /// - `(g^{-1}X - h^{-1})`: The Lagrange selector of the subset consisting of everything but the point `gh^{-1}`.
    /// - `1/Z_{gH}(X)`: The inverse of the vanishing polynomial.
    fn selectors_at_point<Ext: ExtensionField<Val>>(&self, point: Ext) -> LagrangeSelectors<Ext> {
        let unshifted_point = point * self.shift().inverse();
        let z_h = unshifted_point.exp_power_of_2(self.log_size()) - Ext::ONE;
        LagrangeSelectors {
            is_first_row: z_h / (unshifted_point - Ext::ONE),
            is_last_row: z_h / (unshifted_point - self.subgroup_generator().inverse()),
            is_transition: unshifted_point - self.subgroup_generator().inverse(),
            inv_vanishing: z_h.inverse(),
        }
    }

    /// Compute the Lagrange selectors of our space at every point in the coset.
    ///
    /// This will error if our space is not the group `H` and if the given
    /// coset is not disjoint from `H`.
    fn selectors_on_coset(&self, coset: Self) -> LagrangeSelectors<Vec<Val>> {
        assert_eq!(self.shift(), Val::ONE);
        assert_ne!(coset.shift(), Val::ONE);
        assert!(coset.log_size() >= self.log_size());
        let rate_bits = coset.log_size() - self.log_size();

        let s_pow_n = coset.shift().exp_power_of_2(self.log_size());
        // evals of Z_H(X) = X^n - 1
        let evals = Val::two_adic_generator(rate_bits)
            .powers()
            .take(1 << rate_bits)
            .map(|x| s_pow_n * x - Val::ONE)
            .collect_vec();

        let xs = cyclic_subgroup_coset_known_order(
            coset.subgroup_generator(),
            coset.shift(),
            coset.size(),
        )
        .collect_vec();

        let single_point_selector = |i: u64| {
            let coset_i = self.subgroup_generator().exp_u64(i);
            let denoms = xs.iter().map(|&x| x - coset_i).collect_vec();
            let invs = batch_multiplicative_inverse(&denoms);
            evals
                .iter()
                .cycle()
                .zip(invs)
                .map(|(&z_h, inv)| z_h * inv)
                .collect_vec()
        };

        let subgroup_last = self.subgroup_generator().inverse();

        LagrangeSelectors {
            is_first_row: single_point_selector(0),
            is_last_row: single_point_selector(self.size() as u64 - 1),
            is_transition: xs.into_iter().map(|x| x - subgroup_last).collect(),
            inv_vanishing: batch_multiplicative_inverse(&evals)
                .into_iter()
                .cycle()
                .take(coset.size())
                .collect(),
        }
    }
}
