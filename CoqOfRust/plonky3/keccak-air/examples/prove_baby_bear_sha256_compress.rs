use core::fmt::Debug;

use p3_baby_bear::BabyBear;
use p3_challenger::{HashChallenger, SerializingChallenger32};
use p3_commit::ExtensionMmcs;
use p3_field::extension::BinomialExtensionField;
use p3_fri::{TwoAdicFriPcs, create_benchmark_fri_config};
use p3_keccak_air::{KeccakAir, generate_trace_rows};
use p3_merkle_tree::MerkleTreeMmcs;
use p3_sha256::{Sha256, Sha256Compress};
use p3_symmetric::SerializingHasher32;
use p3_uni_stark::{StarkConfig, prove, verify};
use rand::rngs::SmallRng;
use rand::{Rng, SeedableRng};
use tracing_forest::ForestLayer;
use tracing_forest::util::LevelFilter;
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::util::SubscriberInitExt;
use tracing_subscriber::{EnvFilter, Registry};

#[cfg(feature = "parallel")]
type Dft = p3_dft::Radix2DitParallel<BabyBear>;
#[cfg(not(feature = "parallel"))]
type Dft = p3_dft::Radix2Bowers;

const NUM_HASHES: usize = 1_365;

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

    type ByteHash = Sha256;
    type FieldHash = SerializingHasher32<ByteHash>;
    let byte_hash = ByteHash {};
    let field_hash = FieldHash::new(byte_hash);

    type MyCompress = Sha256Compress;
    let compress = MyCompress {};

    type ValMmcs = MerkleTreeMmcs<Val, u8, FieldHash, MyCompress, 32>;
    let val_mmcs = ValMmcs::new(field_hash, compress);

    type ChallengeMmcs = ExtensionMmcs<Val, Challenge, ValMmcs>;
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs);

    let dft = Dft::default();

    type Challenger = SerializingChallenger32<Val, HashChallenger<u8, ByteHash, 32>>;
    let challenger = Challenger::from_hasher(vec![], byte_hash);

    let fri_config = create_benchmark_fri_config(challenge_mmcs);

    let mut rng = SmallRng::seed_from_u64(1);
    let inputs = (0..NUM_HASHES).map(|_| rng.random()).collect::<Vec<_>>();
    let trace = generate_trace_rows::<Val>(inputs, fri_config.log_blowup);

    type Pcs = TwoAdicFriPcs<Val, Dft, ValMmcs, ChallengeMmcs>;
    let pcs = Pcs::new(dft, val_mmcs, fri_config);

    type MyConfig = StarkConfig<Pcs, Challenge, Challenger>;
    let config = MyConfig::new(pcs, challenger);

    let proof = prove(&config, &KeccakAir {}, trace, &vec![]);
    verify(&config, &KeccakAir {}, &proof, &vec![])
}
