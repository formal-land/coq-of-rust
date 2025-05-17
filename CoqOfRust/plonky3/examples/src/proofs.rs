use core::fmt::Debug;

use p3_challenger::{DuplexChallenger, SerializingChallenger32};
use p3_circle::CirclePcs;
use p3_commit::ExtensionMmcs;
use p3_dft::TwoAdicSubgroupDft;
use p3_field::extension::{BinomialExtensionField, ComplexExtendable};
use p3_field::{ExtensionField, Field, PrimeField32, PrimeField64, TwoAdicField};
use p3_fri::{TwoAdicFriPcs, create_benchmark_fri_config};
use p3_keccak::{Keccak256Hash, KeccakF};
use p3_mersenne_31::Mersenne31;
use p3_symmetric::{CryptographicPermutation, PaddingFreeSponge, SerializingHasher32To64};
use p3_uni_stark::{Proof, StarkGenericConfig, prove, verify};
use rand::distr::StandardUniform;
use rand::prelude::Distribution;

use crate::airs::ExampleHashAir;
use crate::types::{
    KeccakCircleStarkConfig, KeccakCompressionFunction, KeccakMerkleMmcs, KeccakStarkConfig,
    Poseidon2CircleStarkConfig, Poseidon2Compression, Poseidon2MerkleMmcs, Poseidon2Sponge,
    Poseidon2StarkConfig,
};

/// Produce a MerkleTreeMmcs which uses the KeccakF permutation.
const fn get_keccak_mmcs<F: Field>() -> KeccakMerkleMmcs<F> {
    let u64_hash = PaddingFreeSponge::<KeccakF, 25, 17, 4>::new(KeccakF {});

    let field_hash = SerializingHasher32To64::new(u64_hash);

    let compress = KeccakCompressionFunction::new(u64_hash);

    KeccakMerkleMmcs::new(field_hash, compress)
}

/// Produce a MerkleTreeMmcs from a pair of cryptographic field permutations.
///
/// The first permutation will be used for compression and the second for more sponge hashing.
/// Currently this is only intended to be used with a pair of Poseidon2 hashes of with 16 and 24
/// but this can easily be generalised in future if we desire.
const fn get_poseidon2_mmcs<
    F: Field,
    Perm16: CryptographicPermutation<[F; 16]> + CryptographicPermutation<[F::Packing; 16]>,
    Perm24: CryptographicPermutation<[F; 24]> + CryptographicPermutation<[F::Packing; 24]>,
>(
    perm16: Perm16,
    perm24: Perm24,
) -> Poseidon2MerkleMmcs<F, Perm16, Perm24> {
    let hash = Poseidon2Sponge::new(perm24);

    let compress = Poseidon2Compression::new(perm16);

    Poseidon2MerkleMmcs::<F, _, _>::new(hash, compress)
}

/// Prove the given ProofGoal using the Keccak hash function to build the merkle tree.
///
/// This allows the user to choose:
/// - The Field
/// - The Proof Goal (Choice of both hash function and desired number of hashes to prove)
/// - The DFT
#[inline]
pub fn prove_monty31_keccak<
    F: PrimeField32 + TwoAdicField,
    EF: ExtensionField<F> + TwoAdicField,
    DFT: TwoAdicSubgroupDft<F>,
    PG: ExampleHashAir<F, KeccakStarkConfig<F, EF, DFT>>,
>(
    proof_goal: PG,
    dft: DFT,
    num_hashes: usize,
) -> Result<(), impl Debug>
where
    StandardUniform: Distribution<F>,
{
    let val_mmcs = get_keccak_mmcs();

    let challenge_mmcs = ExtensionMmcs::<F, EF, _>::new(val_mmcs.clone());
    let fri_config = create_benchmark_fri_config(challenge_mmcs);

    let trace = proof_goal.generate_trace_rows(num_hashes, fri_config.log_blowup);

    let pcs = TwoAdicFriPcs::new(dft, val_mmcs, fri_config);
    let challenger = SerializingChallenger32::from_hasher(vec![], Keccak256Hash {});

    let config = KeccakStarkConfig::new(pcs, challenger);

    let proof = prove(&config, &proof_goal, trace, &vec![]);
    report_proof_size(&proof);

    verify(&config, &proof_goal, &proof, &vec![])
}

/// Prove the given ProofGoal using the Poseidon2 hash function to build the merkle tree.
///
/// This allows the user to choose:
/// - The Field
/// - The Proof Goal (Choice of Hash function and number of hashes to prove)
/// - The DFT
#[inline]
pub fn prove_monty31_poseidon2<
    F: PrimeField32 + TwoAdicField,
    EF: ExtensionField<F> + TwoAdicField,
    DFT: TwoAdicSubgroupDft<F>,
    Perm16: CryptographicPermutation<[F; 16]> + CryptographicPermutation<[F::Packing; 16]>,
    Perm24: CryptographicPermutation<[F; 24]> + CryptographicPermutation<[F::Packing; 24]>,
    PG: ExampleHashAir<F, Poseidon2StarkConfig<F, EF, DFT, Perm16, Perm24>>,
>(
    proof_goal: PG,
    dft: DFT,
    num_hashes: usize,
    perm16: Perm16,
    perm24: Perm24,
) -> Result<(), impl Debug>
where
    StandardUniform: Distribution<F>,
{
    let val_mmcs = get_poseidon2_mmcs::<F, _, _>(perm16, perm24.clone());

    let challenge_mmcs = ExtensionMmcs::<F, EF, _>::new(val_mmcs.clone());
    let fri_config = create_benchmark_fri_config(challenge_mmcs);

    let trace = proof_goal.generate_trace_rows(num_hashes, fri_config.log_blowup);

    let pcs = TwoAdicFriPcs::new(dft, val_mmcs, fri_config);
    let challenger = DuplexChallenger::new(perm24);

    let config = Poseidon2StarkConfig::new(pcs, challenger);

    let proof = prove(&config, &proof_goal, trace, &vec![]);
    report_proof_size(&proof);

    verify(&config, &proof_goal, &proof, &vec![])
}

/// Prove the given ProofGoal using the Keccak hash function to build the merkle tree.
///
/// This fixes the field and Mersenne31 and makes use of the circle stark.
///
/// It currently allows the user to choose:
/// - The Proof Goal (Choice of Hash function and number of hashes to prove)
#[inline]
pub fn prove_m31_keccak<
    PG: ExampleHashAir<
            Mersenne31,
            KeccakCircleStarkConfig<Mersenne31, BinomialExtensionField<Mersenne31, 3>>,
        >,
>(
    proof_goal: PG,
    num_hashes: usize,
) -> Result<(), impl Debug> {
    type F = Mersenne31;
    type EF = BinomialExtensionField<Mersenne31, 3>;

    let val_mmcs = get_keccak_mmcs();
    let challenge_mmcs = ExtensionMmcs::<F, EF, _>::new(val_mmcs.clone());
    let fri_config = create_benchmark_fri_config(challenge_mmcs);

    let trace = proof_goal.generate_trace_rows(num_hashes, fri_config.log_blowup);

    let pcs = CirclePcs::new(val_mmcs, fri_config);
    let challenger = SerializingChallenger32::from_hasher(vec![], Keccak256Hash {});

    let config = KeccakCircleStarkConfig::new(pcs, challenger);

    let proof = prove(&config, &proof_goal, trace, &vec![]);
    report_proof_size(&proof);

    verify(&config, &proof_goal, &proof, &vec![])
}

/// Prove the given ProofGoal using the Keccak hash function to build the merkle tree.
///
/// This fixes the field and Mersenne31 and makes use of the circle stark.
///
/// It currently allows the user to choose:
/// - The Proof Goal (Choice of Hash function and number of hashes to prove)
#[inline]
pub fn prove_m31_poseidon2<
    F: PrimeField64 + ComplexExtendable,
    EF: ExtensionField<F>,
    Perm16: CryptographicPermutation<[F; 16]> + CryptographicPermutation<[F::Packing; 16]>,
    Perm24: CryptographicPermutation<[F; 24]> + CryptographicPermutation<[F::Packing; 24]>,
    PG: ExampleHashAir<F, Poseidon2CircleStarkConfig<F, EF, Perm16, Perm24>>,
>(
    proof_goal: PG,
    num_hashes: usize,
    perm16: Perm16,
    perm24: Perm24,
) -> Result<(), impl Debug>
where
    StandardUniform: Distribution<F>,
{
    let val_mmcs = get_poseidon2_mmcs::<F, _, _>(perm16, perm24.clone());

    let challenge_mmcs = ExtensionMmcs::<F, EF, _>::new(val_mmcs.clone());
    let fri_config = create_benchmark_fri_config(challenge_mmcs);

    let trace = proof_goal.generate_trace_rows(num_hashes, fri_config.log_blowup);

    let pcs = CirclePcs::new(val_mmcs, fri_config);
    let challenger = DuplexChallenger::new(perm24);

    let config = Poseidon2CircleStarkConfig::new(pcs, challenger);

    let proof = prove(&config, &proof_goal, trace, &vec![]);
    report_proof_size(&proof);

    verify(&config, &proof_goal, &proof, &vec![])
}

/// Report the result of the proof.
///
/// Either print that the proof was successful or panic and return the error.
#[inline]
pub fn report_result(result: Result<(), impl Debug>) {
    if let Err(e) = result {
        panic!("{:?}", e);
    } else {
        println!("Proof Verified Successfully")
    }
}

/// Report the size of the serialized proof.
///
/// Serializes the given proof instance using bincode and prints the size in bytes.
/// Panics if serialization fails.
#[inline]
pub fn report_proof_size<SC>(proof: &Proof<SC>)
where
    SC: StarkGenericConfig,
{
    let config = bincode::config::standard()
        .with_little_endian()
        .with_fixed_int_encoding();
    let proof_bytes =
        bincode::serde::encode_to_vec(proof, config).expect("Failed to serialize proof");
    println!("Proof size: {} bytes", proof_bytes.len());
}
