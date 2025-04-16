use clap::Parser;
use p3_baby_bear::{BabyBear, GenericPoseidon2LinearLayersBabyBear, Poseidon2BabyBear};
use p3_blake3_air::Blake3Air;
use p3_dft::Radix2DitParallel;
use p3_examples::airs::ProofObjective;
use p3_examples::dfts::DftChoice;
use p3_examples::parsers::{DftOptions, FieldOptions, MerkleHashOptions, ProofOptions};
use p3_examples::proofs::{
    prove_m31_keccak, prove_m31_poseidon2, prove_monty31_keccak, prove_monty31_poseidon2,
    report_result,
};
use p3_field::extension::BinomialExtensionField;
use p3_keccak_air::KeccakAir;
use p3_koala_bear::{GenericPoseidon2LinearLayersKoalaBear, KoalaBear, Poseidon2KoalaBear};
use p3_mersenne_31::{GenericPoseidon2LinearLayersMersenne31, Mersenne31, Poseidon2Mersenne31};
use p3_monty_31::dft::RecursiveDft;
use p3_poseidon2_air::{RoundConstants, VectorizedPoseidon2Air};
use rand::SeedableRng;
use rand::rngs::SmallRng;
use tracing_forest::ForestLayer;
use tracing_forest::util::LevelFilter;
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::util::SubscriberInitExt;
use tracing_subscriber::{EnvFilter, Registry};

// General constants for constructing the Poseidon2 AIR.
const P2_WIDTH: usize = 16;
const P2_HALF_FULL_ROUNDS: usize = 4;
const P2_LOG_VECTOR_LEN: u8 = 3;
const P2_VECTOR_LEN: usize = 1 << P2_LOG_VECTOR_LEN;

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
struct Args {
    /// The field to use for our proof.
    #[arg(short, long, ignore_case = true, value_enum)]
    field: FieldOptions,

    /// What we are trying to prove.
    #[arg(short, long, ignore_case = true, value_enum)]
    objective: ProofOptions,

    /// The log base 2 of the desired trace length.
    #[arg(short, long)]
    log_trace_length: u8,

    /// The discrete fourier transform to use in the proof.
    #[arg(short, long, ignore_case = true, value_enum, default_value_t = DftOptions::None)]
    discrete_fourier_transform: DftOptions,

    /// The hash function to use when assembling the Merkle tree.
    #[arg(short, long, ignore_case = true, value_enum)]
    merkle_hash: MerkleHashOptions,
}

fn main() {
    let env_filter = EnvFilter::builder()
        .with_default_directive(LevelFilter::INFO.into())
        .from_env_lossy();

    Registry::default()
        .with(env_filter)
        .with(ForestLayer::default())
        .init();

    let args = Args::parse();

    let trace_height = 1 << args.log_trace_length;

    let num_hashes = match args.objective {
        ProofOptions::Blake3Permutations => {
            println!("Proving 2^{} Blake-3 permutations", {
                args.log_trace_length
            });
            trace_height
        }
        ProofOptions::Poseidon2Permutations => {
            println!("Proving 2^{} native Poseidon-2 permutations", {
                args.log_trace_length + P2_LOG_VECTOR_LEN
            });
            trace_height << P2_LOG_VECTOR_LEN
        }
        ProofOptions::KeccakFPermutations => {
            let num_hashes = trace_height / 24;
            println!("Proving {num_hashes} Keccak-F permutations");
            num_hashes
        }
    };

    // WARNING: Use a real cryptographic PRNG in applications!!
    let mut rng = SmallRng::seed_from_u64(1);

    match args.field {
        FieldOptions::KoalaBear => {
            type EF = BinomialExtensionField<KoalaBear, 4>;

            let proof_goal = match args.objective {
                ProofOptions::Blake3Permutations => ProofObjective::Blake3(Blake3Air {}),
                ProofOptions::KeccakFPermutations => ProofObjective::Keccak(KeccakAir {}),
                ProofOptions::Poseidon2Permutations => {
                    let constants = RoundConstants::from_rng(&mut rng);

                    // Field specific constants for constructing the Poseidon2 AIR.
                    const SBOX_DEGREE: u64 = 3;
                    const SBOX_REGISTERS: usize = 0;
                    const PARTIAL_ROUNDS: usize = 20;

                    let p2_air: VectorizedPoseidon2Air<
                        KoalaBear,
                        GenericPoseidon2LinearLayersKoalaBear,
                        P2_WIDTH,
                        SBOX_DEGREE,
                        SBOX_REGISTERS,
                        P2_HALF_FULL_ROUNDS,
                        PARTIAL_ROUNDS,
                        P2_VECTOR_LEN,
                    > = VectorizedPoseidon2Air::new(constants);
                    ProofObjective::Poseidon2(p2_air)
                }
            };

            let dft = match args.discrete_fourier_transform {
                DftOptions::RecursiveDft => {
                    DftChoice::Recursive(RecursiveDft::new(trace_height << 1))
                }
                DftOptions::Radix2DitParallel => DftChoice::Parallel(Radix2DitParallel::default()),
                DftOptions::None => panic!(
                    "Please specify what dft to use. Options are recursive-dft and radix-2-dit-parallel"
                ),
            };

            match args.merkle_hash {
                MerkleHashOptions::KeccakF => {
                    let result = prove_monty31_keccak::<_, EF, _, _>(proof_goal, dft, num_hashes);
                    report_result(result);
                }
                MerkleHashOptions::Poseidon2 => {
                    let perm16 = Poseidon2KoalaBear::<16>::new_from_rng_128(&mut rng);
                    let perm24 = Poseidon2KoalaBear::<24>::new_from_rng_128(&mut rng);
                    let result = prove_monty31_poseidon2::<_, EF, _, _, _, _>(
                        proof_goal, dft, num_hashes, perm16, perm24,
                    );
                    report_result(result);
                }
            };
        }
        FieldOptions::BabyBear => {
            type EF = BinomialExtensionField<BabyBear, 4>;

            let proof_goal = match args.objective {
                ProofOptions::Blake3Permutations => ProofObjective::Blake3(Blake3Air {}),
                ProofOptions::KeccakFPermutations => ProofObjective::Keccak(KeccakAir {}),
                ProofOptions::Poseidon2Permutations => {
                    let constants = RoundConstants::from_rng(&mut rng);

                    // Field specific constants for constructing the Poseidon2 AIR.
                    const SBOX_DEGREE: u64 = 7;
                    const SBOX_REGISTERS: usize = 1;
                    const PARTIAL_ROUNDS: usize = 13;

                    let p2_air: VectorizedPoseidon2Air<
                        BabyBear,
                        GenericPoseidon2LinearLayersBabyBear,
                        P2_WIDTH,
                        SBOX_DEGREE,
                        SBOX_REGISTERS,
                        P2_HALF_FULL_ROUNDS,
                        PARTIAL_ROUNDS,
                        P2_VECTOR_LEN,
                    > = VectorizedPoseidon2Air::new(constants);
                    ProofObjective::Poseidon2(p2_air)
                }
            };

            let dft = match args.discrete_fourier_transform {
                DftOptions::RecursiveDft => {
                    DftChoice::Recursive(RecursiveDft::new(trace_height << 1))
                }
                DftOptions::Radix2DitParallel => DftChoice::Parallel(Radix2DitParallel::default()),
                DftOptions::None => panic!(
                    "Please specify what dft to use. Options are recursive-dft and radix-2-dit-parallel"
                ),
            };

            match args.merkle_hash {
                MerkleHashOptions::KeccakF => {
                    let result = prove_monty31_keccak::<_, EF, _, _>(proof_goal, dft, num_hashes);
                    report_result(result);
                }
                MerkleHashOptions::Poseidon2 => {
                    let perm16 = Poseidon2BabyBear::<16>::new_from_rng_128(&mut rng);
                    let perm24 = Poseidon2BabyBear::<24>::new_from_rng_128(&mut rng);
                    let result = prove_monty31_poseidon2::<_, EF, _, _, _, _>(
                        proof_goal, dft, num_hashes, perm16, perm24,
                    );
                    report_result(result);
                }
            };
        }
        FieldOptions::Mersenne31 => {
            type EF = BinomialExtensionField<Mersenne31, 3>;

            let proof_goal = match args.objective {
                ProofOptions::Blake3Permutations => ProofObjective::Blake3(Blake3Air {}),
                ProofOptions::KeccakFPermutations => ProofObjective::Keccak(KeccakAir {}),
                ProofOptions::Poseidon2Permutations => {
                    let constants = RoundConstants::from_rng(&mut rng);

                    // Field specific constants for constructing the Poseidon2 AIR.
                    const SBOX_DEGREE: u64 = 5;
                    const SBOX_REGISTERS: usize = 1;
                    const PARTIAL_ROUNDS: usize = 14;

                    let p2_air: VectorizedPoseidon2Air<
                        Mersenne31,
                        GenericPoseidon2LinearLayersMersenne31,
                        P2_WIDTH,
                        SBOX_DEGREE,
                        SBOX_REGISTERS,
                        P2_HALF_FULL_ROUNDS,
                        PARTIAL_ROUNDS,
                        P2_VECTOR_LEN,
                    > = VectorizedPoseidon2Air::new(constants);
                    ProofObjective::Poseidon2(p2_air)
                }
            };

            match args.discrete_fourier_transform {
                DftOptions::None => {}
                _ => panic!(
                    "Currently there are no available DFT options when using Mersenne31. Please remove the --discrete_fourier_transform flag."
                ),
            };

            match args.merkle_hash {
                MerkleHashOptions::KeccakF => {
                    let result = prove_m31_keccak(proof_goal, num_hashes);
                    report_result(result);
                }
                MerkleHashOptions::Poseidon2 => {
                    let perm16 = Poseidon2Mersenne31::<16>::new_from_rng_128(&mut rng);
                    let perm24 = Poseidon2Mersenne31::<24>::new_from_rng_128(&mut rng);
                    let result = prove_m31_poseidon2::<_, EF, _, _, _>(
                        proof_goal, num_hashes, perm16, perm24,
                    );
                    report_result(result);
                }
            };
        }
    }
}
