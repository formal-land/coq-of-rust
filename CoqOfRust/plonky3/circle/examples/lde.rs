use core::hint::black_box;
use std::time::{Duration, Instant};

use p3_baby_bear::BabyBear;
use p3_circle::{CircleDomain, CircleEvaluations};
use p3_dft::{Radix2DitParallel, TwoAdicSubgroupDft};
use p3_field::Field;
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use p3_mersenne_31::Mersenne31;
use rand::SeedableRng;
use rand::rngs::SmallRng;
use tracing_forest::ForestLayer;
use tracing_forest::util::LevelFilter;
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::util::SubscriberInitExt;
use tracing_subscriber::{EnvFilter, Registry};

type F = Mersenne31;

fn go<M: Matrix<F>>(evals: CircleEvaluations<F, M>, log_n: usize) -> CircleEvaluations<F> {
    evals.extrapolate(CircleDomain::standard(log_n))
}

fn main() {
    let env_filter = EnvFilter::builder()
        .with_default_directive(LevelFilter::INFO.into())
        .from_env_lossy();

    let mut args = std::env::args().skip(1);
    let log_n = args.next().map(|s| s.parse().unwrap()).unwrap_or(16);
    let log_w = args.next().map(|s| s.parse().unwrap()).unwrap_or(8);
    println!("log_n={log_n}, log_w={log_w}");

    let mut rng = SmallRng::seed_from_u64(1);
    let m = RowMajorMatrix::<F>::rand(&mut rng, 1 << log_n, 1 << log_w);
    let evals = CircleEvaluations::from_natural_order(CircleDomain::standard(log_n), m);

    println!("warming up for 1s...");
    let t0 = Instant::now();
    while Instant::now().duration_since(t0) < Duration::from_secs(1) {
        black_box(go(black_box(evals.clone()), log_n + 1));
    }

    Registry::default()
        .with(env_filter)
        .with(ForestLayer::default())
        .init();

    black_box(go(black_box(evals), log_n + 1));

    let m = RowMajorMatrix::<BabyBear>::rand(&mut rng, 1 << log_n, 1 << log_w);
    black_box(Radix2DitParallel::default().coset_lde_batch(black_box(m), 1, BabyBear::GENERATOR));
}
