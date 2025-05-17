use alloc::collections::BTreeMap;
use alloc::vec;
use alloc::vec::Vec;
use core::fmt::Debug;
use core::marker::PhantomData;

use itertools::{Itertools, izip};
use p3_challenger::{CanObserve, FieldChallenger, GrindingChallenger};
use p3_commit::{Mmcs, OpenedValues, Pcs};
use p3_dft::TwoAdicSubgroupDft;
use p3_field::coset::TwoAdicMultiplicativeCoset;
use p3_field::{
    ExtensionField, Field, PackedFieldExtension, TwoAdicField, batch_multiplicative_inverse,
    cyclic_subgroup_coset_known_order, dot_product,
};
use p3_interpolation::interpolate_coset;
use p3_matrix::bitrev::{BitReversalPerm, BitReversedMatrixView, BitReversibleMatrix};
use p3_matrix::dense::{DenseMatrix, RowMajorMatrix};
use p3_matrix::{Dimensions, Matrix};
use p3_maybe_rayon::prelude::*;
use p3_util::linear_map::LinearMap;
use p3_util::zip_eq::zip_eq;
use p3_util::{log2_strict_usize, reverse_bits_len, reverse_slice_index_bits};
use serde::{Deserialize, Serialize};
use tracing::{info_span, instrument};

use crate::verifier::{self, FriError};
use crate::{FriConfig, FriGenericConfig, FriProof, prover};

#[derive(Debug)]
pub struct TwoAdicFriPcs<Val, Dft, InputMmcs, FriMmcs> {
    dft: Dft,
    mmcs: InputMmcs,
    fri: FriConfig<FriMmcs>,
    _phantom: PhantomData<Val>,
}

impl<Val, Dft, InputMmcs, FriMmcs> TwoAdicFriPcs<Val, Dft, InputMmcs, FriMmcs> {
    pub const fn new(dft: Dft, mmcs: InputMmcs, fri: FriConfig<FriMmcs>) -> Self {
        Self {
            dft,
            mmcs,
            fri,
            _phantom: PhantomData,
        }
    }
}

#[derive(Serialize, Deserialize, Clone)]
#[serde(bound = "")]
pub struct BatchOpening<Val: Field, InputMmcs: Mmcs<Val>> {
    pub opened_values: Vec<Vec<Val>>,
    pub opening_proof: <InputMmcs as Mmcs<Val>>::Proof,
}

pub struct TwoAdicFriGenericConfig<InputProof, InputError>(
    pub PhantomData<(InputProof, InputError)>,
);

pub type TwoAdicFriGenericConfigForMmcs<F, M> =
    TwoAdicFriGenericConfig<Vec<BatchOpening<F, M>>, <M as Mmcs<F>>::Error>;

impl<F: TwoAdicField, InputProof, InputError: Debug> FriGenericConfig<F>
    for TwoAdicFriGenericConfig<InputProof, InputError>
{
    type InputProof = InputProof;
    type InputError = InputError;

    fn extra_query_index_bits(&self) -> usize {
        0
    }

    fn fold_row(
        &self,
        index: usize,
        log_height: usize,
        beta: F,
        evals: impl Iterator<Item = F>,
    ) -> F {
        let arity = 2;
        let log_arity = 1;
        let (e0, e1) = evals
            .collect_tuple()
            .expect("TwoAdicFriFolder only supports arity=2");
        // If performance critical, make this API stateful to avoid this
        // This is a bit more math than is necessary, but leaving it here
        // in case we want higher arity in the future
        let subgroup_start = F::two_adic_generator(log_height + log_arity)
            .exp_u64(reverse_bits_len(index, log_height) as u64);
        let mut xs = F::two_adic_generator(log_arity)
            .shifted_powers(subgroup_start)
            .take(arity)
            .collect_vec();
        reverse_slice_index_bits(&mut xs);
        assert_eq!(log_arity, 1, "can only interpolate two points for now");
        // interpolate and evaluate at beta
        e0 + (beta - xs[0]) * (e1 - e0) / (xs[1] - xs[0])
    }

    fn fold_matrix<M: Matrix<F>>(&self, beta: F, m: M) -> Vec<F> {
        // We use the fact that
        //     p_e(x^2) = (p(x) + p(-x)) / 2
        //     p_o(x^2) = (p(x) - p(-x)) / (2 x)
        // that is,
        //     p_e(g^(2i)) = (p(g^i) + p(g^(n/2 + i))) / 2
        //     p_o(g^(2i)) = (p(g^i) - p(g^(n/2 + i))) / (2 g^i)
        // so
        //     result(g^(2i)) = p_e(g^(2i)) + beta p_o(g^(2i))
        //                    = (1/2 + beta/2 g_inv^i) p(g^i)
        //                    + (1/2 - beta/2 g_inv^i) p(g^(n/2 + i))
        let g_inv = F::two_adic_generator(log2_strict_usize(m.height()) + 1).inverse();
        let one_half = F::ONE.halve();
        let half_beta = beta * one_half;

        // TODO: vectorize this (after we have packed extension fields)

        // beta/2 times successive powers of g_inv
        let mut powers = g_inv
            .shifted_powers(half_beta)
            .take(m.height())
            .collect_vec();
        reverse_slice_index_bits(&mut powers);

        m.par_rows()
            .zip(powers)
            .map(|(mut row, power)| {
                let (lo, hi) = row.next_tuple().unwrap();
                (one_half + power) * lo + (one_half - power) * hi
            })
            .collect()
    }
}

impl<Val, Dft, InputMmcs, FriMmcs, Challenge, Challenger> Pcs<Challenge, Challenger>
    for TwoAdicFriPcs<Val, Dft, InputMmcs, FriMmcs>
where
    Val: TwoAdicField,
    Dft: TwoAdicSubgroupDft<Val>,
    InputMmcs: Mmcs<Val>,
    FriMmcs: Mmcs<Challenge>,
    Challenge: TwoAdicField + ExtensionField<Val>,
    Challenger:
        FieldChallenger<Val> + CanObserve<FriMmcs::Commitment> + GrindingChallenger<Witness = Val>,
{
    type Domain = TwoAdicMultiplicativeCoset<Val>;
    type Commitment = InputMmcs::Commitment;
    type ProverData = InputMmcs::ProverData<RowMajorMatrix<Val>>;
    type EvaluationsOnDomain<'a> = BitReversedMatrixView<DenseMatrix<Val, &'a [Val]>>;
    type Proof = FriProof<Challenge, FriMmcs, Val, Vec<BatchOpening<Val, InputMmcs>>>;
    type Error = FriError<FriMmcs::Error, InputMmcs::Error>;

    fn natural_domain_for_degree(&self, degree: usize) -> Self::Domain {
        // This panics if (and only if) `degree` is not a power of 2 or `degree`
        // > `1 << Val::TWO_ADICITY`.
        TwoAdicMultiplicativeCoset::new(Val::ONE, log2_strict_usize(degree)).unwrap()
    }

    fn commit(
        &self,
        evaluations: Vec<(Self::Domain, RowMajorMatrix<Val>)>,
    ) -> (Self::Commitment, Self::ProverData) {
        let ldes: Vec<_> = evaluations
            .into_iter()
            .map(|(domain, evals)| {
                assert_eq!(domain.size(), evals.height());
                let shift = Val::GENERATOR / domain.shift();
                // Commit to the bit-reversed LDE.
                self.dft
                    .coset_lde_batch(evals, self.fri.log_blowup, shift)
                    .bit_reverse_rows()
                    .to_row_major_matrix()
            })
            .collect();

        self.mmcs.commit(ldes)
    }

    fn get_evaluations_on_domain<'a>(
        &self,
        prover_data: &'a Self::ProverData,
        idx: usize,
        domain: Self::Domain,
    ) -> Self::EvaluationsOnDomain<'a> {
        // todo: handle extrapolation for LDEs we don't have
        assert_eq!(domain.shift(), Val::GENERATOR);
        let lde = self.mmcs.get_matrices(prover_data)[idx];
        assert!(lde.height() >= domain.size());
        lde.split_rows(domain.size()).0.bit_reverse_rows()
    }

    fn open(
        &self,
        // For each round,
        rounds: Vec<(
            &Self::ProverData,
            // for each matrix,
            Vec<
                // points to open
                Vec<Challenge>,
            >,
        )>,
        challenger: &mut Challenger,
    ) -> (OpenedValues<Challenge>, Self::Proof) {
        /*

        A quick rundown of the optimizations in this function:
        We are trying to compute sum_i alpha^i * (p(X) - y)/(X - z),
        for each z an opening point, y = p(z). Each p(X) is given as evaluations in bit-reversed order
        in the columns of the matrices. y is computed by barycentric interpolation.
        X and p(X) are in the base field; alpha, y and z are in the extension.
        The primary goal is to minimize extension multiplications.

        - Instead of computing all alpha^i, we just compute alpha^i for i up to the largest width
        of a matrix, then multiply by an "alpha offset" when accumulating.
              a^0 x0 + a^1 x1 + a^2 x2 + a^3 x3 + ...
            = a^0 ( a^0 x0 + a^1 x1 ) + a^2 ( a^0 x2 + a^1 x3 ) + ...
            (see `alpha_pows`, `alpha_pow_offset`, `num_reduced`)

        - For each unique point z, we precompute 1/(X-z) for the largest subgroup opened at this point.
        Since we compute it in bit-reversed order, smaller subgroups can simply truncate the vector.
            (see `inv_denoms`)

        - Then, for each matrix (with columns p_i) and opening point z, we want:
            for each row (corresponding to subgroup element X):
                reduced[X] += alpha_offset * sum_i [ alpha^i * inv_denom[X] * (p_i[X] - y[i]) ]

            We can factor out inv_denom, and expand what's left:
                reduced[X] += alpha_offset * inv_denom[X] * sum_i [ alpha^i * p_i[X] - alpha^i * y[i] ]

            And separate the sum:
                reduced[X] += alpha_offset * inv_denom[X] * [ sum_i [ alpha^i * p_i[X] ] - sum_i [ alpha^i * y[i] ] ]

            And now the last sum doesn't depend on X, so we can precompute that for the matrix, too.
            So the hot loop (that depends on both X and i) is just:
                sum_i [ alpha^i * p_i[X] ]

            with alpha^i an extension, p_i[X] a base

        */

        let mats_and_points = rounds
            .iter()
            .map(|(data, points)| {
                let mats = self
                    .mmcs
                    .get_matrices(data)
                    .into_iter()
                    .map(|m| m.as_view())
                    .collect_vec();
                debug_assert_eq!(
                    mats.len(),
                    points.len(),
                    "each matrix should have a corresponding set of evaluation points"
                );
                (mats, points)
            })
            .collect_vec();

        // Find the maximum height and the maximum width of matrices in the batch.
        // These do not need to correspond to the same matrix.
        let (global_max_height, global_max_width) = mats_and_points
            .iter()
            .flat_map(|(mats, _)| mats.iter().map(|m| (m.height(), m.width())))
            .reduce(|(hmax, wmax), (h, w)| (hmax.max(h), wmax.max(w)))
            .expect("No Matrices Supplied?");
        let log_global_max_height = log2_strict_usize(global_max_height);

        // For each unique opening point z, we will find the largest degree bound
        // for that point, and precompute 1/(z - X) for the largest subgroup (in bitrev order).
        let inv_denoms = compute_inverse_denominators(&mats_and_points, Val::GENERATOR);

        // Evaluate coset representations and write openings to the challenger
        let all_opened_values = mats_and_points
            .iter()
            .map(|(mats, points)| {
                izip!(mats.iter(), points.iter())
                    .map(|(mat, points_for_mat)| {
                        points_for_mat
                            .iter()
                            .map(|&point| {
                                let _guard =
                                    info_span!("evaluate matrix", dims = %mat.dimensions())
                                        .entered();

                                // Use Barycentric interpolation to evaluate the matrix at the given point.
                                let ys =
                                    info_span!("compute opened values with Lagrange interpolation")
                                        .in_scope(|| {
                                            let h = mat.height() >> self.fri.log_blowup;
                                            let (low_coset, _) = mat.split_rows(h);
                                            let mut inv_denoms =
                                                inv_denoms.get(&point).unwrap()[..h].to_vec();
                                            reverse_slice_index_bits(&mut inv_denoms);
                                            interpolate_coset(
                                                &BitReversalPerm::new_view(low_coset),
                                                Val::GENERATOR,
                                                point,
                                                Some(&inv_denoms),
                                            )
                                        });
                                ys.iter()
                                    .for_each(|&y| challenger.observe_algebra_element(y));
                                ys
                            })
                            .collect_vec()
                    })
                    .collect_vec()
            })
            .collect_vec();

        // Batch combination challenge
        // TODO: Should we be computing a different alpha for each height?
        let alpha: Challenge = challenger.sample_algebra_element();

        // We precompute powers of alpha as we need the same powers for each matrix.
        // We compute both a vector of unpacked powers and a vector of packed powers.
        // TODO: It should be possible to refactor this to only use the packed powers but
        // this is not a bottleneck so is not a priority.
        let packed_alpha_powers =
            Challenge::ExtensionPacking::packed_ext_powers_capped(alpha, global_max_width)
                .collect_vec();
        let alpha_powers =
            Challenge::ExtensionPacking::to_ext_iter(packed_alpha_powers.iter().copied())
                .collect_vec();

        // Now that we have sent the openings to the verifier, it remains to prove
        // that those openings are correct.

        // Given a low degree polynomial `f(x)` with claimed evaluation `f(zeta)`, we can check
        // that `f(zeta)` is correct by doing a low degree test on `(f(zeta) - f(x))/(zeta - x)`.
        // We will use `alpha` to batch together both different claimed openings `zeta` and
        // different polynomials `f` whose evaluation vectors have the same height.

        // TODO: If we allow different polynomials to have different blow_up factors
        // we may need to revisit this and to ensure it is safe to batch them together.

        // num_reduced records the number of reduced function opening point pairs
        // of each given `log_height`.
        let mut num_reduced = [0; 32];

        // For each `log_height` from 2^1 -> 2^32, reduced_openings will contain either `None`
        // if there are no matrices of that height, or `Some(vec)` where `vec` is equal to
        // a sum of `(f(zeta) - f(x))/(zeta - x)` over all `f`'s of that height and
        // opening points `zeta` with the sum weighted by powers of alpha.
        let mut reduced_openings: [_; 32] = core::array::from_fn(|_| None);

        for ((mats, points), openings_for_round) in
            mats_and_points.iter().zip(all_opened_values.iter())
        {
            for (mat, points_for_mat, openings_for_mat) in
                izip!(mats.iter(), points.iter(), openings_for_round.iter())
            {
                let _guard =
                    info_span!("reduce matrix quotient", dims = %mat.dimensions()).entered();

                let log_height = log2_strict_usize(mat.height());

                // If this is our first matrix at this height, initialise reduced_openings to zero.
                // Otherwise, get a mutable reference to it.
                let reduced_opening_for_log_height = reduced_openings[log_height]
                    .get_or_insert_with(|| vec![Challenge::ZERO; mat.height()]);
                debug_assert_eq!(reduced_opening_for_log_height.len(), mat.height());

                // Treating our matrix M as the evaluations of functions M0, M1, ...
                // Compute the evaluations of `Mred(x) = M0(x) + alpha*M1(x) + ...`
                let mat_compressed = info_span!("compress mat").in_scope(|| {
                    // This will be reused for all points z which M is opened at so we collect into a vector.
                    mat.rowwise_packed_dot_product::<Challenge>(&packed_alpha_powers)
                        .collect::<Vec<_>>()
                });

                for (&point, openings) in points_for_mat.iter().zip(openings_for_mat) {
                    // If we have multiple matrices at the same height, we need to scale mat to combine them.
                    let alpha_pow_offset = alpha.exp_u64(num_reduced[log_height] as u64);

                    // As we have all the openings `Mi(z)`, we can combine them using `alpha`
                    // in an identical way to before to also compute `Mred(z)`.
                    let reduced_openings: Challenge =
                        dot_product(alpha_powers.iter().copied(), openings.iter().copied());

                    mat_compressed
                        .par_iter()
                        .zip(reduced_opening_for_log_height.par_iter_mut())
                        // inv_denoms contains `1/(point - x)` for `x` in a coset `gK`.
                        // If `|K| =/= mat.height()` we actually want a subset of this
                        // corresponding to the evaluations over `gH` for `|H| = mat.height()`.
                        // As inv_denoms is bit reversed, the evaluations over `gH` are exactly
                        // the evaluations over `gK` at the indices `0..mat.height()`.
                        // So zip will truncate to the desired smaller length.
                        .zip(inv_denoms.get(&point).unwrap().par_iter())
                        // Map the function `Mred(x) -> (Mred(z) - Mred(x))/(z - x)`
                        // across the evaluations vector of `Mred(x)`.
                        .for_each(|((&reduced_row, ro), &inv_denom)| {
                            *ro += alpha_pow_offset * (reduced_openings - reduced_row) * inv_denom
                        });
                    num_reduced[log_height] += mat.width();
                }
            }
        }

        let fri_input = reduced_openings.into_iter().rev().flatten().collect_vec();

        let g: TwoAdicFriGenericConfigForMmcs<Val, InputMmcs> =
            TwoAdicFriGenericConfig(PhantomData);

        let fri_proof = prover::prove(&g, &self.fri, fri_input, challenger, |index| {
            rounds
                .iter()
                .map(|(data, _)| {
                    let log_max_height = log2_strict_usize(self.mmcs.get_max_height(data));
                    let bits_reduced = log_global_max_height - log_max_height;
                    let reduced_index = index >> bits_reduced;
                    let (opened_values, opening_proof) = self.mmcs.open_batch(reduced_index, data);
                    BatchOpening {
                        opened_values,
                        opening_proof,
                    }
                })
                .collect()
        });

        (all_opened_values, fri_proof)
    }

    fn verify(
        &self,
        // For each round:
        rounds: Vec<(
            Self::Commitment,
            // for each matrix:
            Vec<(
                // its domain,
                Self::Domain,
                // for each point:
                Vec<(
                    // the point,
                    Challenge,
                    // values at the point
                    Vec<Challenge>,
                )>,
            )>,
        )>,
        proof: &Self::Proof,
        challenger: &mut Challenger,
    ) -> Result<(), Self::Error> {
        // Write evaluations to challenger
        for (_, round) in &rounds {
            for (_, mat) in round {
                for (_, point) in mat {
                    point
                        .iter()
                        .for_each(|&opening| challenger.observe_algebra_element(opening));
                }
            }
        }

        // Batch combination challenge
        let alpha: Challenge = challenger.sample_algebra_element();

        let log_global_max_height =
            proof.commit_phase_commits.len() + self.fri.log_blowup + self.fri.log_final_poly_len;

        let g: TwoAdicFriGenericConfigForMmcs<Val, InputMmcs> =
            TwoAdicFriGenericConfig(PhantomData);

        verifier::verify(&g, &self.fri, proof, challenger, |index, input_proof| {
            // TODO: separate this out into functions

            // log_height -> (alpha_pow, reduced_opening)
            let mut reduced_openings = BTreeMap::<usize, (Challenge, Challenge)>::new();

            for (batch_opening, (batch_commit, mats)) in
                zip_eq(input_proof, &rounds, FriError::InvalidProofShape)?
            {
                let batch_heights = mats
                    .iter()
                    .map(|(domain, _)| domain.size() << self.fri.log_blowup)
                    .collect_vec();
                let batch_dims = batch_heights
                    .iter()
                    // TODO: MMCS doesn't really need width; we put 0 for now.
                    .map(|&height| Dimensions { width: 0, height })
                    .collect_vec();

                if let Some(batch_max_height) = batch_heights.iter().max() {
                    let log_batch_max_height = log2_strict_usize(*batch_max_height);
                    let bits_reduced = log_global_max_height - log_batch_max_height;
                    let reduced_index = index >> bits_reduced;

                    self.mmcs.verify_batch(
                        batch_commit,
                        &batch_dims,
                        reduced_index,
                        &batch_opening.opened_values,
                        &batch_opening.opening_proof,
                    )
                } else {
                    // Empty batch?
                    self.mmcs.verify_batch(
                        batch_commit,
                        &[],
                        0,
                        &batch_opening.opened_values,
                        &batch_opening.opening_proof,
                    )
                }
                .map_err(FriError::InputError)?;

                for (mat_opening, (mat_domain, mat_points_and_values)) in zip_eq(
                    &batch_opening.opened_values,
                    mats,
                    FriError::InvalidProofShape,
                )? {
                    let log_height = log2_strict_usize(mat_domain.size()) + self.fri.log_blowup;

                    let bits_reduced = log_global_max_height - log_height;
                    let rev_reduced_index = reverse_bits_len(index >> bits_reduced, log_height);

                    // todo: this can be nicer with domain methods?

                    let x = Val::GENERATOR
                        * Val::two_adic_generator(log_height).exp_u64(rev_reduced_index as u64);

                    let (alpha_pow, ro) = reduced_openings
                        .entry(log_height)
                        .or_insert((Challenge::ONE, Challenge::ZERO));

                    for (z, ps_at_z) in mat_points_and_values {
                        for (&p_at_x, &p_at_z) in
                            zip_eq(mat_opening, ps_at_z, FriError::InvalidProofShape)?
                        {
                            let quotient = (-p_at_z + p_at_x) / (-*z + x);
                            *ro += *alpha_pow * quotient;
                            *alpha_pow *= alpha;
                        }
                    }
                }
            }

            // `reduced_openings` would have a log_height = log_blowup entry only if there was a
            // trace matrix of height 1. In this case the reduced opening can be skipped as it will
            // not be checked against any commit phase commit.
            if let Some((_alpha_pow, ro)) = reduced_openings.remove(&self.fri.log_blowup) {
                assert!(ro.is_zero());
            }

            // Return reduced openings descending by log_height.
            Ok(reduced_openings
                .into_iter()
                .rev()
                .map(|(log_height, (_alpha_pow, ro))| (log_height, ro))
                .collect())
        })?;

        Ok(())
    }
}

#[instrument(skip_all)]
fn compute_inverse_denominators<F: TwoAdicField, EF: ExtensionField<F>, M: Matrix<F>>(
    mats_and_points: &[(Vec<M>, &Vec<Vec<EF>>)],
    coset_shift: F,
) -> LinearMap<EF, Vec<EF>> {
    let mut max_log_height_for_point: LinearMap<EF, usize> = LinearMap::new();
    for (mats, points) in mats_and_points {
        for (mat, points_for_mat) in izip!(mats, *points) {
            let log_height = log2_strict_usize(mat.height());
            for &z in points_for_mat {
                if let Some(lh) = max_log_height_for_point.get_mut(&z) {
                    *lh = core::cmp::max(*lh, log_height);
                } else {
                    max_log_height_for_point.insert(z, log_height);
                }
            }
        }
    }

    // Compute the largest subgroup we will use, in bitrev order.
    let max_log_height = *max_log_height_for_point.values().max().unwrap();
    let mut subgroup = cyclic_subgroup_coset_known_order(
        F::two_adic_generator(max_log_height),
        coset_shift,
        1 << max_log_height,
    )
    .collect_vec();
    reverse_slice_index_bits(&mut subgroup);

    max_log_height_for_point
        .into_iter()
        .map(|(z, log_height)| {
            (
                z,
                batch_multiplicative_inverse(
                    &subgroup[..(1 << log_height)]
                        .iter()
                        .map(|&x| z - x)
                        .collect_vec(),
                ),
            )
        })
        .collect()
}
