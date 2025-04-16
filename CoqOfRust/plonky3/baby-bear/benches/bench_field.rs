use core::any::type_name;

use criterion::{BatchSize, Criterion, criterion_group, criterion_main};
use p3_baby_bear::BabyBear;
use p3_field::{Field, PrimeCharacteristicRing};
use p3_field_testing::bench_func::{
    benchmark_add_latency, benchmark_add_throughput, benchmark_inv, benchmark_iter_sum,
    benchmark_mul_latency, benchmark_mul_throughput, benchmark_sub_latency,
    benchmark_sub_throughput,
};
use rand::rngs::SmallRng;
use rand::{Rng, SeedableRng};

type F = BabyBear;

fn bench_field(c: &mut Criterion) {
    let name = "BabyBear";
    const REPS: usize = 1000;
    benchmark_inv::<F>(c, name);
    benchmark_iter_sum::<F, 4, REPS>(c, name);
    benchmark_iter_sum::<F, 8, REPS>(c, name);
    benchmark_iter_sum::<F, 12, REPS>(c, name);

    // Note that each round of throughput has 10 operations
    // So we should have 10 * more repetitions for latency tests.
    const L_REPS: usize = 10 * REPS;
    benchmark_add_latency::<F, L_REPS>(c, name);
    benchmark_add_throughput::<F, REPS>(c, name);
    benchmark_sub_latency::<F, L_REPS>(c, name);
    benchmark_sub_throughput::<F, REPS>(c, name);

    let mut rng = SmallRng::seed_from_u64(1);
    c.bench_function("7th_root", |b| {
        b.iter_batched(
            || rng.random::<F>(),
            |x| x.exp_u64(1725656503),
            BatchSize::SmallInput,
        )
    });
}

fn bench_packedfield(c: &mut Criterion) {
    let name = type_name::<<F as Field>::Packing>().to_string();
    // Note that each round of throughput has 10 operations
    // So we should have 10 * more repetitions for latency tests.
    const REPS: usize = 100;
    const L_REPS: usize = 10 * REPS;

    benchmark_add_latency::<<F as Field>::Packing, L_REPS>(c, &name);
    benchmark_add_throughput::<<F as Field>::Packing, REPS>(c, &name);
    benchmark_sub_latency::<<F as Field>::Packing, L_REPS>(c, &name);
    benchmark_sub_throughput::<<F as Field>::Packing, REPS>(c, &name);
    benchmark_mul_latency::<<F as Field>::Packing, L_REPS>(c, &name);
    benchmark_mul_throughput::<<F as Field>::Packing, REPS>(c, &name);
}

criterion_group!(baby_bear_arithmetic, bench_field, bench_packedfield);
criterion_main!(baby_bear_arithmetic);
