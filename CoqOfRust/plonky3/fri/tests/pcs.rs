use itertools::{Itertools, izip};
use p3_baby_bear::{BabyBear, Poseidon2BabyBear};
use p3_challenger::{CanObserve, DuplexChallenger, FieldChallenger};
use p3_commit::{ExtensionMmcs, Pcs, PolynomialSpace};
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::{ExtensionField, Field};
use p3_fri::{FriConfig, TwoAdicFriPcs};
use p3_matrix::dense::RowMajorMatrix;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use rand::distr::{Distribution, StandardUniform};
use rand::rngs::SmallRng;
use rand::{Rng, SeedableRng};

fn seeded_rng() -> impl Rng {
    SmallRng::seed_from_u64(0)
}

fn do_test_fri_pcs<Val, Challenge, Challenger, P>(
    (pcs, challenger): &(P, Challenger),
    log_degrees_by_round: &[&[usize]],
) where
    P: Pcs<Challenge, Challenger>,
    P::Domain: PolynomialSpace<Val = Val>,
    Val: Field,
    StandardUniform: Distribution<Val>,
    Challenge: ExtensionField<Val>,
    Challenger: Clone + CanObserve<P::Commitment> + FieldChallenger<Val>,
{
    let num_rounds = log_degrees_by_round.len();
    let mut rng = seeded_rng();

    let mut p_challenger = challenger.clone();

    let domains_and_polys_by_round = log_degrees_by_round
        .iter()
        .map(|log_degrees| {
            log_degrees
                .iter()
                .map(|&log_degree| {
                    let d = 1 << log_degree;
                    // random width 5-15
                    let width = 5 + rng.random_range(0..=10);
                    (
                        pcs.natural_domain_for_degree(d),
                        RowMajorMatrix::<Val>::rand(&mut rng, d, width),
                    )
                })
                .collect_vec()
        })
        .collect_vec();

    let (commits_by_round, data_by_round): (Vec<_>, Vec<_>) = domains_and_polys_by_round
        .iter()
        .map(|domains_and_polys| pcs.commit(domains_and_polys.clone()))
        .unzip();
    assert_eq!(commits_by_round.len(), num_rounds);
    assert_eq!(data_by_round.len(), num_rounds);
    p_challenger.observe_slice(&commits_by_round);

    let zeta: Challenge = p_challenger.sample_algebra_element();

    let points_by_round = log_degrees_by_round
        .iter()
        .map(|log_degrees| vec![vec![zeta]; log_degrees.len()])
        .collect_vec();
    let data_and_points = data_by_round.iter().zip(points_by_round).collect();
    let (opening_by_round, proof) = pcs.open(data_and_points, &mut p_challenger);
    assert_eq!(opening_by_round.len(), num_rounds);

    // Verify the proof.
    let mut v_challenger = challenger.clone();
    v_challenger.observe_slice(&commits_by_round);
    let verifier_zeta: Challenge = v_challenger.sample_algebra_element();
    assert_eq!(verifier_zeta, zeta);

    let commits_and_claims_by_round = izip!(
        commits_by_round,
        domains_and_polys_by_round,
        opening_by_round
    )
    .map(|(commit, domains_and_polys, openings)| {
        let claims = domains_and_polys
            .iter()
            .zip(openings)
            .map(|((domain, _), mat_openings)| (*domain, vec![(zeta, mat_openings[0].clone())]))
            .collect_vec();
        (commit, claims)
    })
    .collect_vec();
    assert_eq!(commits_and_claims_by_round.len(), num_rounds);

    pcs.verify(commits_and_claims_by_round, &proof, &mut v_challenger)
        .unwrap()
}

// Set it up so we create tests inside a module for each pcs, so we get nice error reports
// specific to a failing PCS.
macro_rules! make_tests_for_pcs {
    ($p:expr) => {
        #[test]
        fn single() {
            let p = $p;
            for i in 3..6 {
                $crate::do_test_fri_pcs(&p, &[&[i]]);
            }
        }

        #[test]
        fn many_equal() {
            let p = $p;
            for i in 5..8 {
                $crate::do_test_fri_pcs(&p, &[&[i; 5]]);
                println!("{i} ok");
            }
        }

        #[test]
        fn many_different() {
            let p = $p;
            for i in 3..8 {
                let degrees = (3..3 + i).collect::<Vec<_>>();
                $crate::do_test_fri_pcs(&p, &[&degrees]);
            }
        }

        #[test]
        fn many_different_rev() {
            let p = $p;
            for i in 3..8 {
                let degrees = (3..3 + i).rev().collect::<Vec<_>>();
                $crate::do_test_fri_pcs(&p, &[&degrees]);
            }
        }

        #[test]
        fn multiple_rounds() {
            let p = $p;
            $crate::do_test_fri_pcs(&p, &[&[3]]);
            $crate::do_test_fri_pcs(&p, &[&[3], &[3]]);
            $crate::do_test_fri_pcs(&p, &[&[3], &[2]]);
            $crate::do_test_fri_pcs(&p, &[&[2], &[3]]);
            $crate::do_test_fri_pcs(&p, &[&[3, 4], &[3, 4]]);
            $crate::do_test_fri_pcs(&p, &[&[4, 2], &[4, 2]]);
            $crate::do_test_fri_pcs(&p, &[&[2, 2], &[3, 3]]);
            $crate::do_test_fri_pcs(&p, &[&[3, 3], &[2, 2]]);
            $crate::do_test_fri_pcs(&p, &[&[2], &[3, 3]]);
        }
    };
}

mod babybear_fri_pcs {
    use super::*;

    type Val = BabyBear;
    type Challenge = BinomialExtensionField<Val, 4>;

    type Perm = Poseidon2BabyBear<16>;
    type MyHash = PaddingFreeSponge<Perm, 16, 8, 8>;
    type MyCompress = TruncatedPermutation<Perm, 2, 8, 16>;

    type ValMmcs =
        MerkleTreeMmcs<<Val as Field>::Packing, <Val as Field>::Packing, MyHash, MyCompress, 8>;
    type ChallengeMmcs = ExtensionMmcs<Val, Challenge, ValMmcs>;

    type Dft = Radix2DitParallel<Val>;
    type Challenger = DuplexChallenger<Val, Perm, 16, 8>;
    type MyPcs = TwoAdicFriPcs<Val, Dft, ValMmcs, ChallengeMmcs>;

    fn get_pcs(log_blowup: usize) -> (MyPcs, Challenger) {
        let perm = Perm::new_from_rng_128(&mut seeded_rng());
        let hash = MyHash::new(perm.clone());
        let compress = MyCompress::new(perm.clone());

        let val_mmcs = ValMmcs::new(hash, compress);
        let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());

        let fri_config = FriConfig {
            log_blowup,
            log_final_poly_len: 0,
            num_queries: 10,
            proof_of_work_bits: 8,
            mmcs: challenge_mmcs,
        };

        let pcs = MyPcs::new(Dft::default(), val_mmcs, fri_config);
        (pcs, Challenger::new(perm))
    }

    mod blowup_1 {
        make_tests_for_pcs!(super::get_pcs(1));
    }
    mod blowup_2 {
        make_tests_for_pcs!(super::get_pcs(2));
    }
}

mod m31_fri_pcs {
    use core::marker::PhantomData;

    use p3_challenger::{HashChallenger, SerializingChallenger32};
    use p3_circle::CirclePcs;
    use p3_keccak::Keccak256Hash;
    use p3_mersenne_31::Mersenne31;
    use p3_symmetric::{CompressionFunctionFromHasher, SerializingHasher32};

    use super::*;

    type Val = Mersenne31;
    type Challenge = BinomialExtensionField<Mersenne31, 3>;

    type ByteHash = Keccak256Hash;
    type FieldHash = SerializingHasher32<ByteHash>;

    type MyCompress = CompressionFunctionFromHasher<ByteHash, 2, 32>;

    type ValMmcs = MerkleTreeMmcs<Val, u8, FieldHash, MyCompress, 32>;

    type ChallengeMmcs = ExtensionMmcs<Val, Challenge, ValMmcs>;

    type Challenger = SerializingChallenger32<Val, HashChallenger<u8, ByteHash, 32>>;

    type Pcs = CirclePcs<Val, ValMmcs, ChallengeMmcs>;

    fn get_pcs(log_blowup: usize) -> (Pcs, Challenger) {
        let byte_hash = ByteHash {};
        let field_hash = FieldHash::new(byte_hash);
        let compress = MyCompress::new(byte_hash);
        let val_mmcs = ValMmcs::new(field_hash, compress);
        let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
        let fri_config = FriConfig {
            log_blowup,
            log_final_poly_len: 0,
            num_queries: 10,
            proof_of_work_bits: 8,
            mmcs: challenge_mmcs,
        };
        let pcs = Pcs {
            mmcs: val_mmcs,
            fri_config,
            _phantom: PhantomData,
        };
        (pcs, Challenger::from_hasher(vec![], byte_hash))
    }

    mod blowup_1 {
        make_tests_for_pcs!(super::get_pcs(1));
    }
    mod blowup_2 {
        make_tests_for_pcs!(super::get_pcs(2));
    }
}
