use core::fmt::Debug;
use core::marker::PhantomData;

use p3_challenger::{HashChallenger, SerializingChallenger32};
use p3_circle::CirclePcs;
use p3_commit::ExtensionMmcs;
use p3_field::extension::BinomialExtensionField;
use p3_fri::create_benchmark_fri_config;
use p3_keccak_air::{KeccakAir, generate_trace_rows};
use p3_merkle_tree::MerkleTreeMmcs;
use p3_mersenne_31::Mersenne31;
use p3_sha256::Sha256;
use p3_symmetric::{CompressionFunctionFromHasher, SerializingHasher32};
use p3_uni_stark::{StarkConfig, prove, verify};
use rand::rngs::SmallRng;
use rand::{Rng, SeedableRng};
use tracing_forest::ForestLayer;
use tracing_forest::util::LevelFilter;
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::util::SubscriberInitExt;
use tracing_subscriber::{EnvFilter, Registry};

const NUM_HASHES: usize = 1365;

fn main() -> Result<(), impl Debug> {
    let env_filter = EnvFilter::builder()
        .with_default_directive(LevelFilter::INFO.into())
        .from_env_lossy();

    Registry::default()
        .with(env_filter)
        .with(ForestLayer::default())
        .init();

    type Val = Mersenne31;
    type Challenge = BinomialExtensionField<Val, 3>;

    type ByteHash = Sha256;
    type FieldHash = SerializingHasher32<ByteHash>;
    let byte_hash = ByteHash {};
    let field_hash = FieldHash::new(Sha256);

    type MyCompress = CompressionFunctionFromHasher<ByteHash, 2, 32>;
    let compress = MyCompress::new(byte_hash);

    type ValMmcs = MerkleTreeMmcs<Val, u8, FieldHash, MyCompress, 32>;
    let val_mmcs = ValMmcs::new(field_hash, compress);

    type ChallengeMmcs = ExtensionMmcs<Val, Challenge, ValMmcs>;
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());

    type Challenger = SerializingChallenger32<Val, HashChallenger<u8, ByteHash, 32>>;
    let challenger = Challenger::from_hasher(vec![], byte_hash);

    let fri_config = create_benchmark_fri_config(challenge_mmcs);

    let mut rng = SmallRng::seed_from_u64(1);
    let inputs = (0..NUM_HASHES).map(|_| rng.random()).collect::<Vec<_>>();
    let trace = generate_trace_rows::<Val>(inputs, fri_config.log_blowup);

    type Pcs = CirclePcs<Val, ValMmcs, ChallengeMmcs>;
    let pcs = Pcs {
        mmcs: val_mmcs,
        fri_config,
        _phantom: PhantomData,
    };

    type MyConfig = StarkConfig<Pcs, Challenge, Challenger>;
    let config = MyConfig::new(pcs, challenger);

    let proof = prove(&config, &KeccakAir {}, trace, &vec![]);
    verify(&config, &KeccakAir {}, &proof, &vec![])
}
