use alloc::borrow::Cow;
use alloc::collections::BTreeMap;
use alloc::vec;
use alloc::vec::Vec;
use core::marker::PhantomData;

use itertools::{Itertools, izip};
use p3_challenger::{CanObserve, FieldChallenger, GrindingChallenger};
use p3_commit::{Mmcs, OpenedValues, Pcs, PolynomialSpace};
use p3_field::extension::ComplexExtendable;
use p3_field::{ExtensionField, Field};
use p3_fri::FriConfig;
use p3_fri::verifier::FriError;
use p3_matrix::dense::{DenseMatrix, RowMajorMatrix};
use p3_matrix::row_index_mapped::RowIndexMappedView;
use p3_matrix::{Dimensions, Matrix};
use p3_maybe_rayon::prelude::*;
use p3_util::log2_strict_usize;
use p3_util::zip_eq::zip_eq;
use serde::{Deserialize, Serialize};
use tracing::info_span;

use crate::deep_quotient::{deep_quotient_reduce_row, extract_lambda};
use crate::domain::CircleDomain;
use crate::folding::{CircleFriConfig, CircleFriGenericConfig, fold_y, fold_y_row};
use crate::point::Point;
use crate::prover::prove;
use crate::verifier::verify;
use crate::{CfftPerm, CfftPermutable, CircleEvaluations, CircleFriProof, cfft_permute_index};

#[derive(Debug)]
pub struct CirclePcs<Val: Field, InputMmcs, FriMmcs> {
    pub mmcs: InputMmcs,
    pub fri_config: FriConfig<FriMmcs>,
    pub _phantom: PhantomData<Val>,
}

impl<Val: Field, InputMmcs, FriMmcs> CirclePcs<Val, InputMmcs, FriMmcs> {
    pub const fn new(mmcs: InputMmcs, fri_config: FriConfig<FriMmcs>) -> Self {
        Self {
            mmcs,
            fri_config,
            _phantom: PhantomData,
        }
    }
}

#[derive(Serialize, Deserialize, Clone)]
#[serde(bound = "")]
pub struct BatchOpening<Val: Field, InputMmcs: Mmcs<Val>> {
    pub(crate) opened_values: Vec<Vec<Val>>,
    pub(crate) opening_proof: <InputMmcs as Mmcs<Val>>::Proof,
}

#[derive(Serialize, Deserialize, Clone)]
#[serde(bound = "")]
pub struct CircleInputProof<
    Val: Field,
    Challenge: Field,
    InputMmcs: Mmcs<Val>,
    FriMmcs: Mmcs<Challenge>,
> {
    input_openings: Vec<BatchOpening<Val, InputMmcs>>,
    first_layer_siblings: Vec<Challenge>,
    first_layer_proof: FriMmcs::Proof,
}

#[derive(Debug)]
pub enum InputError<InputMmcsError, FriMmcsError> {
    InputMmcsError(InputMmcsError),
    FirstLayerMmcsError(FriMmcsError),
    InputShapeError,
}

#[derive(Serialize, Deserialize, Clone)]
#[serde(bound(
    serialize = "Witness: Serialize",
    deserialize = "Witness: Deserialize<'de>"
))]
pub struct CirclePcsProof<
    Val: Field,
    Challenge: Field,
    InputMmcs: Mmcs<Val>,
    FriMmcs: Mmcs<Challenge>,
    Witness,
> {
    first_layer_commitment: FriMmcs::Commitment,
    lambdas: Vec<Challenge>,
    fri_proof: CircleFriProof<
        Challenge,
        FriMmcs,
        Witness,
        CircleInputProof<Val, Challenge, InputMmcs, FriMmcs>,
    >,
}

impl<Val, InputMmcs, FriMmcs, Challenge, Challenger> Pcs<Challenge, Challenger>
    for CirclePcs<Val, InputMmcs, FriMmcs>
where
    Val: ComplexExtendable,
    Challenge: ExtensionField<Val>,
    InputMmcs: Mmcs<Val>,
    FriMmcs: Mmcs<Challenge>,
    Challenger: FieldChallenger<Val> + GrindingChallenger + CanObserve<FriMmcs::Commitment>,
{
    type Domain = CircleDomain<Val>;
    type Commitment = InputMmcs::Commitment;
    type ProverData = InputMmcs::ProverData<RowMajorMatrix<Val>>;
    type EvaluationsOnDomain<'a> = RowIndexMappedView<CfftPerm, DenseMatrix<Val, Cow<'a, [Val]>>>;
    type Proof = CirclePcsProof<Val, Challenge, InputMmcs, FriMmcs, Challenger::Witness>;
    type Error = FriError<FriMmcs::Error, InputError<InputMmcs::Error, FriMmcs::Error>>;

    fn natural_domain_for_degree(&self, degree: usize) -> Self::Domain {
        CircleDomain::standard(log2_strict_usize(degree))
    }

    fn commit(
        &self,
        evaluations: Vec<(Self::Domain, RowMajorMatrix<Val>)>,
    ) -> (Self::Commitment, Self::ProverData) {
        let ldes = evaluations
            .into_iter()
            .map(|(domain, evals)| {
                assert!(
                    domain.log_n >= 2,
                    "CirclePcs cannot commit to a matrix with fewer than 4 rows.",
                    // (because we bivariate fold one bit, and fri needs one more bit)
                );
                CircleEvaluations::from_natural_order(domain, evals)
                    .extrapolate(CircleDomain::standard(
                        domain.log_n + self.fri_config.log_blowup,
                    ))
                    .to_cfft_order()
            })
            .collect_vec();
        let (comm, mmcs_data) = self.mmcs.commit(ldes);
        (comm, mmcs_data)
    }

    fn get_evaluations_on_domain<'a>(
        &self,
        data: &'a Self::ProverData,
        idx: usize,
        domain: Self::Domain,
    ) -> Self::EvaluationsOnDomain<'a> {
        let mat = self.mmcs.get_matrices(data)[idx].as_view();
        let committed_domain = CircleDomain::standard(log2_strict_usize(mat.height()));
        if domain == committed_domain {
            mat.as_cow().cfft_perm_rows()
        } else {
            CircleEvaluations::from_cfft_order(committed_domain, mat)
                .extrapolate(domain)
                .to_cfft_order()
                .as_cow()
                .cfft_perm_rows()
        }
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
        // Open matrices at points
        let values: OpenedValues<Challenge> = rounds
            .iter()
            .map(|(data, points_for_mats)| {
                let mats = self.mmcs.get_matrices(data);
                debug_assert_eq!(
                    mats.len(),
                    points_for_mats.len(),
                    "Mismatched number of matrices and points"
                );
                izip!(mats, points_for_mats)
                    .map(|(mat, points_for_mat)| {
                        let log_height = log2_strict_usize(mat.height());
                        // It was committed in cfft order.
                        let evals = CircleEvaluations::from_cfft_order(
                            CircleDomain::standard(log_height),
                            mat.as_view(),
                        );
                        points_for_mat
                            .iter()
                            .map(|&zeta| {
                                let zeta = Point::from_projective_line(zeta);
                                let ps_at_zeta =
                                    info_span!("compute opened values with Lagrange interpolation")
                                        .in_scope(|| evals.evaluate_at_point(zeta));
                                ps_at_zeta
                                    .iter()
                                    .for_each(|&p| challenger.observe_algebra_element(p));
                                ps_at_zeta
                            })
                            .collect()
                    })
                    .collect()
            })
            .collect();

        // Batch combination challenge
        let alpha: Challenge = challenger.sample_algebra_element();

        /*
        We are reducing columns ("ro" = reduced opening) with powers of alpha:
          ro = .. + α^n c_n + α^(n+1) c_(n+1) + ..
        But we want to precompute small powers of alpha, and batch the columns. So we can do:
          ro = .. + α^n (α^0 c_n + α^1 c_(n+1) + ..) + ..
        reusing the α^0, α^1, etc., then at the end of each column batch we multiply by the α^n.
        (Due to circle stark specifics, we need 2 powers of α for each column, so actually α^(2n)).
        We store this α^(2n), the running reducing factor per log_height, and call it the "alpha offset".
        */

        // log_height -> (alpha offset, reduced openings column)
        let mut reduced_openings: BTreeMap<usize, (Challenge, Vec<Challenge>)> = BTreeMap::new();

        rounds
            .iter()
            .zip(values.iter())
            .for_each(|((data, points_for_mats), values)| {
                let mats = self.mmcs.get_matrices(data);
                izip!(mats, points_for_mats, values).for_each(|(mat, points_for_mat, values)| {
                    let log_height = log2_strict_usize(mat.height());
                    // It was committed in cfft order.
                    let evals = CircleEvaluations::from_cfft_order(
                        CircleDomain::standard(log_height),
                        mat.as_view(),
                    );

                    let (alpha_offset, reduced_opening_for_log_height) =
                        reduced_openings.entry(log_height).or_insert_with(|| {
                            (Challenge::ONE, vec![Challenge::ZERO; 1 << log_height])
                        });

                    points_for_mat
                        .iter()
                        .zip(values.iter())
                        .for_each(|(&zeta, ps_at_zeta)| {
                            let zeta = Point::from_projective_line(zeta);

                            // Reduce this matrix, as a deep quotient, into one column with powers of α.
                            let mat_ros = evals.deep_quotient_reduce(alpha, zeta, ps_at_zeta);

                            // Fold it into our running reduction, offset by alpha_offset.
                            reduced_opening_for_log_height
                                .par_iter_mut()
                                .zip(mat_ros)
                                .for_each(|(ro, mat_ro)| {
                                    *ro += *alpha_offset * mat_ro;
                                });

                            // Update alpha_offset from α^i -> α^(i + 2 * width)
                            *alpha_offset *= alpha.exp_u64(2 * evals.values.width() as u64);
                        });
                });
            });

        // Iterate over our reduced columns and extract lambda - the multiple of the vanishing polynomial
        // which may appear in the reduced quotient due to CFFT dimension gap.

        let mut lambdas = vec![];
        let mut log_heights = vec![];
        let first_layer_mats: Vec<RowMajorMatrix<Challenge>> = reduced_openings
            .into_iter()
            .map(|(log_height, (_, mut ro))| {
                assert!(log_height > 0);
                log_heights.push(log_height);
                let lambda = extract_lambda(&mut ro, self.fri_config.log_blowup);
                lambdas.push(lambda);
                // Prepare for first layer fold with 2 siblings per leaf.
                RowMajorMatrix::new(ro, 2)
            })
            .collect();
        let log_max_height = log_heights.iter().max().copied().unwrap();

        // Commit to reduced openings at each log_height, so we can challenge a global
        // folding factor for all first layers, which we use for a "manual" (not part of p3-fri) fold.
        // This is necessary because the first layer of folding uses different twiddles, so it's easiest
        // to do it here, before p3-fri.

        let (first_layer_commitment, first_layer_data) =
            self.fri_config.mmcs.commit(first_layer_mats);
        challenger.observe(first_layer_commitment.clone());
        let bivariate_beta: Challenge = challenger.sample_algebra_element();

        // Fold all first layers at bivariate_beta.

        let fri_input: Vec<Vec<Challenge>> = self
            .fri_config
            .mmcs
            .get_matrices(&first_layer_data)
            .into_iter()
            .map(|m| fold_y(bivariate_beta, m.as_view()))
            // Reverse, because FRI expects descending by height
            .rev()
            .collect();

        let g: CircleFriConfig<Val, Challenge, InputMmcs, FriMmcs> =
            CircleFriGenericConfig(PhantomData);

        let fri_proof = prove(&g, &self.fri_config, fri_input, challenger, |index| {
            // CircleFriFolder asks for an extra query index bit, so we use that here to index
            // the first layer fold.

            // Open the input (big opening, lots of columns) at the full index...
            let input_openings = rounds
                .iter()
                .map(|(data, _)| {
                    let log_max_batch_height = log2_strict_usize(self.mmcs.get_max_height(data));
                    let reduced_index = index >> (log_max_height - log_max_batch_height);
                    let (opened_values, opening_proof) = self.mmcs.open_batch(reduced_index, data);
                    BatchOpening {
                        opened_values,
                        opening_proof,
                    }
                })
                .collect();

            // We committed to first_layer in pairs, so open the reduced index and include the sibling
            // as part of the input proof.
            let (first_layer_values, first_layer_proof) = self
                .fri_config
                .mmcs
                .open_batch(index >> 1, &first_layer_data);
            let first_layer_siblings = izip!(&first_layer_values, &log_heights)
                .map(|(v, log_height)| {
                    let reduced_index = index >> (log_max_height - log_height);
                    let sibling_index = (reduced_index & 1) ^ 1;
                    v[sibling_index]
                })
                .collect();
            CircleInputProof {
                input_openings,
                first_layer_siblings,
                first_layer_proof,
            }
        });

        (
            values,
            CirclePcsProof {
                first_layer_commitment,
                lambdas,
                fri_proof,
            },
        )
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
        challenger.observe(proof.first_layer_commitment.clone());
        let bivariate_beta: Challenge = challenger.sample_algebra_element();

        // +1 to account for first layer
        let log_global_max_height =
            proof.fri_proof.commit_phase_commits.len() + self.fri_config.log_blowup + 1;

        let g: CircleFriConfig<Val, Challenge, InputMmcs, FriMmcs> =
            CircleFriGenericConfig(PhantomData);

        verify(
            &g,
            &self.fri_config,
            &proof.fri_proof,
            challenger,
            |index, input_proof| {
                // log_height -> (alpha_offset, ro)
                let mut reduced_openings = BTreeMap::new();

                let CircleInputProof {
                    input_openings,
                    first_layer_siblings,
                    first_layer_proof,
                } = input_proof;

                for (batch_opening, (batch_commit, mats)) in
                    zip_eq(input_openings, &rounds, InputError::InputShapeError)?
                {
                    let batch_heights: Vec<usize> = mats
                        .iter()
                        .map(|(domain, _)| (domain.size() << self.fri_config.log_blowup))
                        .collect_vec();
                    let batch_dims: Vec<Dimensions> = batch_heights
                        .iter()
                        // todo: mmcs doesn't really need width
                        .map(|&height| Dimensions { width: 0, height })
                        .collect_vec();

                    let (dims, idx) = if let Some(log_batch_max_height) =
                        batch_heights.iter().max().map(|x| log2_strict_usize(*x))
                    {
                        (
                            &batch_dims[..],
                            index >> (log_global_max_height - log_batch_max_height),
                        )
                    } else {
                        // Empty batch?
                        (&[][..], 0)
                    };

                    self.mmcs
                        .verify_batch(
                            batch_commit,
                            dims,
                            idx,
                            &batch_opening.opened_values,
                            &batch_opening.opening_proof,
                        )
                        .map_err(InputError::InputMmcsError)?;

                    for (ps_at_x, (mat_domain, mat_points_and_values)) in zip_eq(
                        &batch_opening.opened_values,
                        mats,
                        InputError::InputShapeError,
                    )? {
                        let log_height = mat_domain.log_n + self.fri_config.log_blowup;
                        let bits_reduced = log_global_max_height - log_height;
                        let orig_idx = cfft_permute_index(index >> bits_reduced, log_height);

                        let committed_domain = CircleDomain::standard(log_height);
                        let x = committed_domain.nth_point(orig_idx);

                        let (alpha_offset, ro) = reduced_openings
                            .entry(log_height)
                            .or_insert((Challenge::ONE, Challenge::ZERO));
                        let alpha_pow_width_2 = alpha.exp_u64(ps_at_x.len() as u64).square();

                        for (zeta_uni, ps_at_zeta) in mat_points_and_values {
                            let zeta = Point::from_projective_line(*zeta_uni);

                            *ro += *alpha_offset
                                * deep_quotient_reduce_row(alpha, x, zeta, ps_at_x, ps_at_zeta);

                            *alpha_offset *= alpha_pow_width_2;
                        }
                    }
                }

                // Verify bivariate fold and lambda correction

                let (mut fri_input, fl_dims, fl_leaves): (Vec<_>, Vec<_>, Vec<_>) = zip_eq(
                    zip_eq(
                        reduced_openings,
                        first_layer_siblings,
                        InputError::InputShapeError,
                    )?,
                    &proof.lambdas,
                    InputError::InputShapeError,
                )?
                .map(|(((log_height, (_, ro)), &fl_sib), &lambda)| {
                    assert!(log_height > 0);

                    let orig_size = log_height - self.fri_config.log_blowup;
                    let bits_reduced = log_global_max_height - log_height;
                    let orig_idx = cfft_permute_index(index >> bits_reduced, log_height);

                    let lde_domain = CircleDomain::standard(log_height);
                    let p: Point<Val> = lde_domain.nth_point(orig_idx);

                    let lambda_corrected = ro - lambda * p.v_n(orig_size);

                    let mut fl_values = vec![lambda_corrected; 2];
                    fl_values[((index >> bits_reduced) & 1) ^ 1] = fl_sib;

                    let fri_input = (
                        // - 1 here is because we have already folded a layer.
                        log_height - 1,
                        fold_y_row(
                            index >> (bits_reduced + 1),
                            // - 1 here is log_arity.
                            log_height - 1,
                            bivariate_beta,
                            fl_values.iter().copied(),
                        ),
                    );

                    let fl_dims = Dimensions {
                        width: 0,
                        height: 1 << (log_height - 1),
                    };

                    (fri_input, fl_dims, fl_values)
                })
                .multiunzip();

                // sort descending
                fri_input.reverse();

                self.fri_config
                    .mmcs
                    .verify_batch(
                        &proof.first_layer_commitment,
                        &fl_dims,
                        index >> 1,
                        &fl_leaves,
                        first_layer_proof,
                    )
                    .map_err(InputError::FirstLayerMmcsError)?;

                Ok(fri_input)
            },
        )
    }
}

#[cfg(test)]
mod tests {
    use p3_challenger::{HashChallenger, SerializingChallenger32};
    use p3_commit::ExtensionMmcs;
    use p3_field::extension::BinomialExtensionField;
    use p3_fri::create_test_fri_config;
    use p3_keccak::Keccak256Hash;
    use p3_merkle_tree::MerkleTreeMmcs;
    use p3_mersenne_31::Mersenne31;
    use p3_symmetric::{CompressionFunctionFromHasher, SerializingHasher32};
    use rand::rngs::SmallRng;
    use rand::{Rng, SeedableRng};

    use super::*;

    #[test]
    fn circle_pcs() {
        // Very simple pcs test. More rigorous tests in p3_fri/tests/pcs.

        let mut rng = SmallRng::seed_from_u64(0);

        type Val = Mersenne31;
        type Challenge = BinomialExtensionField<Mersenne31, 3>;

        type ByteHash = Keccak256Hash;
        type FieldHash = SerializingHasher32<ByteHash>;
        let byte_hash = ByteHash {};
        let field_hash = FieldHash::new(byte_hash);

        type MyCompress = CompressionFunctionFromHasher<ByteHash, 2, 32>;
        let compress = MyCompress::new(byte_hash);

        type ValMmcs = MerkleTreeMmcs<Val, u8, FieldHash, MyCompress, 32>;
        let val_mmcs = ValMmcs::new(field_hash, compress);

        type ChallengeMmcs = ExtensionMmcs<Val, Challenge, ValMmcs>;
        let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());

        type Challenger = SerializingChallenger32<Val, HashChallenger<u8, ByteHash, 32>>;

        let fri_config = create_test_fri_config(challenge_mmcs, 0);

        type Pcs = CirclePcs<Val, ValMmcs, ChallengeMmcs>;
        let pcs = Pcs {
            mmcs: val_mmcs,
            fri_config,
            _phantom: PhantomData,
        };

        let log_n = 10;

        let d = <Pcs as p3_commit::Pcs<Challenge, Challenger>>::natural_domain_for_degree(
            &pcs,
            1 << log_n,
        );

        let evals = RowMajorMatrix::rand(&mut rng, 1 << log_n, 1);

        let (comm, data) =
            <Pcs as p3_commit::Pcs<Challenge, Challenger>>::commit(&pcs, vec![(d, evals)]);

        let zeta: Challenge = rng.random();

        let mut chal = Challenger::from_hasher(vec![], byte_hash);
        let (values, proof) = pcs.open(vec![(&data, vec![vec![zeta]])], &mut chal);

        let mut chal = Challenger::from_hasher(vec![], byte_hash);
        pcs.verify(
            vec![(comm, vec![(d, vec![(zeta, values[0][0][0].clone())])])],
            &proof,
            &mut chal,
        )
        .expect("verify err");
    }
}
