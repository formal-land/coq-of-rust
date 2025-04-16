use core::fmt::Debug;

use p3_baby_bear::{BabyBear, GenericPoseidon2LinearLayersBabyBear};
use p3_challenger::{HashChallenger, SerializingChallenger32};
use p3_commit::ExtensionMmcs;
use p3_field::extension::BinomialExtensionField;
use p3_fri::{HidingFriPcs, create_benchmark_fri_config};
use p3_keccak::{Keccak256Hash, KeccakF};
use p3_merkle_tree::MerkleTreeHidingMmcs;
use p3_poseidon2_air::{RoundConstants, VectorizedPoseidon2Air};
use p3_symmetric::{CompressionFunctionFromHasher, PaddingFreeSponge, SerializingHasher32To64};
use p3_uni_stark::{StarkConfig, prove, verify};
use rand::SeedableRng;
use rand::rngs::SmallRng;
#[cfg(target_family = "unix")]
use tikv_jemallocator::Jemalloc;
use tracing_forest::ForestLayer;
use tracing_forest::util::LevelFilter;
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::util::SubscriberInitExt;
use tracing_subscriber::{EnvFilter, Registry};

#[cfg(target_family = "unix")]
#[global_allocator]
static GLOBAL: Jemalloc = Jemalloc;

const WIDTH: usize = 16;
const SBOX_DEGREE: u64 = 7;
const SBOX_REGISTERS: usize = 1;
const HALF_FULL_ROUNDS: usize = 4;
const PARTIAL_ROUNDS: usize = 20;

const NUM_ROWS: usize = 1 << 16;
const VECTOR_LEN: usize = 1 << 3;
const NUM_PERMUTATIONS: usize = NUM_ROWS * VECTOR_LEN;

type Dft = p3_dft::Radix2DitParallel<BabyBear>;

fn main() -> Result<(), impl Debug> {
    let env_filter = EnvFilter::builder()
        .with_default_directive(LevelFilter::INFO.into())
        .from_env_lossy();

    Registry::default()
        .with(env_filter)
        .with(ForestLayer::default())
        .init();

    type Val = BabyBear;
    type Challenge = BinomialExtensionField<Val, 4>;

    type ByteHash = Keccak256Hash;
    let byte_hash = ByteHash {};

    type U64Hash = PaddingFreeSponge<KeccakF, 25, 17, 4>;
    let u64_hash = U64Hash::new(KeccakF {});

    type FieldHash = SerializingHasher32To64<U64Hash>;
    let field_hash = FieldHash::new(u64_hash);

    type MyCompress = CompressionFunctionFromHasher<U64Hash, 2, 4>;
    let compress = MyCompress::new(u64_hash);

    // WARNING: DO NOT USE SmallRng in proper applications! Use a real PRNG instead!
    type ValMmcs = MerkleTreeHidingMmcs<
        [Val; p3_keccak::VECTOR_LEN],
        [u64; p3_keccak::VECTOR_LEN],
        FieldHash,
        MyCompress,
        SmallRng,
        4,
        4,
    >;
    let mut rng = SmallRng::seed_from_u64(1);
    let constants = RoundConstants::from_rng(&mut rng);
    let val_mmcs = ValMmcs::new(field_hash, compress, rng);

    type ChallengeMmcs = ExtensionMmcs<Val, Challenge, ValMmcs>;
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());

    type Challenger = SerializingChallenger32<Val, HashChallenger<u8, ByteHash, 32>>;
    let challenger = Challenger::from_hasher(vec![], byte_hash);

    let air: VectorizedPoseidon2Air<
        Val,
        GenericPoseidon2LinearLayersBabyBear,
        WIDTH,
        SBOX_DEGREE,
        SBOX_REGISTERS,
        HALF_FULL_ROUNDS,
        PARTIAL_ROUNDS,
        VECTOR_LEN,
    > = VectorizedPoseidon2Air::new(constants);

    let fri_config = create_benchmark_fri_config(challenge_mmcs);

    let trace = air.generate_vectorized_trace_rows(NUM_PERMUTATIONS, fri_config.log_blowup);

    let dft = Dft::default();

    type Pcs = HidingFriPcs<Val, Dft, ValMmcs, ChallengeMmcs, SmallRng>;
    let pcs = Pcs::new(dft, val_mmcs, fri_config, 4, SmallRng::seed_from_u64(1));

    type MyConfig = StarkConfig<Pcs, Challenge, Challenger>;
    let config = MyConfig::new(pcs, challenger);

    let proof = prove(&config, &air, trace, &vec![]);

    verify(&config, &air, &proof, &vec![])
}
