use criterion::{BatchSize, Criterion, criterion_group, criterion_main};
use p3_field::PrimeCharacteristicRing;
use p3_field_testing::bench_func::{
    benchmark_add_latency, benchmark_add_throughput, benchmark_inv, benchmark_iter_sum,
    benchmark_sub_latency, benchmark_sub_throughput, benchmark_sum_array,
};
use p3_mersenne_31::Mersenne31;
use rand::rngs::SmallRng;
use rand::{Rng, SeedableRng};

type F = Mersenne31;

fn bench_field(c: &mut Criterion) {
    let name = "Mersenne31";
    const REPS: usize = 500;
    benchmark_inv::<F>(c, name);
    benchmark_iter_sum::<F, 4, REPS>(c, name);
    benchmark_sum_array::<F, 4, REPS>(c, name);
    benchmark_iter_sum::<F, 6, REPS>(c, name);
    benchmark_sum_array::<F, 6, REPS>(c, name);

    // Note that each round of throughput has 10 operations
    // So we should have 10 * more repetitions for latency tests.
    const L_REPS: usize = 10 * REPS;
    benchmark_add_latency::<F, L_REPS>(c, name);
    benchmark_add_throughput::<F, REPS>(c, name);
    benchmark_sub_latency::<F, L_REPS>(c, name);
    benchmark_sub_throughput::<F, REPS>(c, name);

    let mut rng = SmallRng::seed_from_u64(1);
    c.bench_function("5th_root", |b| {
        b.iter_batched(
            || rng.random::<F>(),
            |x| x.exp_u64(1717986917),
            BatchSize::SmallInput,
        )
    });
}

criterion_group!(mersenne31_arithmetics, bench_field);
criterion_main!(mersenne31_arithmetics);
