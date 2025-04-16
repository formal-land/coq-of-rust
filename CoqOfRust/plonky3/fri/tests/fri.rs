use core::cmp::Reverse;
use core::marker::PhantomData;

use p3_baby_bear::{BabyBear, Poseidon2BabyBear};
use p3_challenger::{CanSampleBits, DuplexChallenger, FieldChallenger};
use p3_commit::ExtensionMmcs;
use p3_dft::{Radix2Dit, TwoAdicSubgroupDft};
use p3_field::extension::BinomialExtensionField;
use p3_field::{Field, PrimeCharacteristicRing};
use p3_fri::{FriConfig, TwoAdicFriGenericConfig, prover, verifier};
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::util::reverse_matrix_index_bits;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use p3_util::log2_strict_usize;
use rand::rngs::SmallRng;
use rand::{Rng, SeedableRng};

type Val = BabyBear;
type Challenge = BinomialExtensionField<Val, 4>;

type Perm = Poseidon2BabyBear<16>;
type MyHash = PaddingFreeSponge<Perm, 16, 8, 8>;
type MyCompress = TruncatedPermutation<Perm, 2, 8, 16>;
type ValMmcs =
    MerkleTreeMmcs<<Val as Field>::Packing, <Val as Field>::Packing, MyHash, MyCompress, 8>;
type ChallengeMmcs = ExtensionMmcs<Val, Challenge, ValMmcs>;
type Challenger = DuplexChallenger<Val, Perm, 16, 8>;
type MyFriConfig = FriConfig<ChallengeMmcs>;

fn get_ldt_for_testing<R: Rng>(rng: &mut R, log_final_poly_len: usize) -> (Perm, MyFriConfig) {
    let perm = Perm::new_from_rng_128(rng);
    let hash = MyHash::new(perm.clone());
    let compress = MyCompress::new(perm.clone());
    let mmcs = ChallengeMmcs::new(ValMmcs::new(hash, compress));
    let fri_config = FriConfig {
        log_blowup: 1,
        log_final_poly_len,
        num_queries: 10,
        proof_of_work_bits: 8,
        mmcs,
    };
    (perm, fri_config)
}

fn do_test_fri_ldt<R: Rng>(rng: &mut R, log_final_poly_len: usize) {
    let (perm, fc) = get_ldt_for_testing(rng, log_final_poly_len);
    let dft = Radix2Dit::default();

    let shift = Val::GENERATOR;

    let ldes: Vec<RowMajorMatrix<Val>> = (5..10)
        .map(|deg_bits| {
            let evals = RowMajorMatrix::<Val>::rand_nonzero(rng, 1 << deg_bits, 16);
            let mut lde = dft.coset_lde_batch(evals, 1, shift);
            reverse_matrix_index_bits(&mut lde);
            lde
        })
        .collect();

    let (proof, p_sample) = {
        // Prover world
        let mut chal = Challenger::new(perm.clone());
        let alpha: Challenge = chal.sample_algebra_element();

        let input: [_; 32] = core::array::from_fn(|log_height| {
            let matrices_with_log_height: Vec<&RowMajorMatrix<Val>> = ldes
                .iter()
                .filter(|m| log2_strict_usize(m.height()) == log_height)
                .collect();
            if matrices_with_log_height.is_empty() {
                None
            } else {
                let reduced: Vec<Challenge> = (0..(1 << log_height))
                    .map(|r| {
                        alpha
                            .powers()
                            .zip(matrices_with_log_height.iter().flat_map(|m| m.row(r)))
                            .map(|(alpha_pow, v)| alpha_pow * v)
                            .sum()
                    })
                    .collect();
                Some(reduced)
            }
        });

        let input: Vec<Vec<Challenge>> = input.into_iter().rev().flatten().collect();

        let log_max_height = log2_strict_usize(input[0].len());

        let proof = prover::prove(
            &TwoAdicFriGenericConfig::<Vec<(usize, Challenge)>, ()>(PhantomData),
            &fc,
            input.clone(),
            &mut chal,
            |idx| {
                // As our "input opening proof", just pass through the literal reduced openings.
                let mut ro = vec![];
                for v in &input {
                    let log_height = log2_strict_usize(v.len());
                    ro.push((log_height, v[idx >> (log_max_height - log_height)]));
                }
                ro.sort_by_key(|(lh, _)| Reverse(*lh));
                ro
            },
        );

        (proof, chal.sample_bits(8))
    };

    let mut v_challenger = Challenger::new(perm);
    let _alpha: Challenge = v_challenger.sample_algebra_element();
    verifier::verify(
        &TwoAdicFriGenericConfig::<Vec<(usize, Challenge)>, ()>(PhantomData),
        &fc,
        &proof,
        &mut v_challenger,
        |_index, proof| Ok(proof.clone()),
    )
    .unwrap();

    assert_eq!(
        p_sample,
        v_challenger.sample_bits(8),
        "prover and verifier transcript have same state after FRI"
    );
}

#[test]
fn test_fri_ldt() {
    // FRI is kind of flaky depending on indexing luck
    for i in 0..4 {
        let mut rng = SmallRng::seed_from_u64(i as u64);
        do_test_fri_ldt(&mut rng, i + 1);
    }
}

// This test is expected to panic because the polynomial degree is less than the final_poly_degree in the config.
#[test]
#[should_panic]
fn test_fri_ldt_should_panic() {
    // FRI is kind of flaky depending on indexing luck
    for i in 0..4 {
        let mut rng = SmallRng::seed_from_u64(i);
        do_test_fri_ldt(&mut rng, 5);
    }
}
