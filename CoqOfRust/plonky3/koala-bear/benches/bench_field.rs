use criterion::{BatchSize, Criterion, criterion_group, criterion_main};
use p3_field::{Field, PrimeCharacteristicRing};
use p3_field_testing::bench_func::{
    benchmark_add_latency, benchmark_add_throughput, benchmark_div_2exp, benchmark_inv,
    benchmark_iter_sum, benchmark_mul_2exp, benchmark_mul_latency, benchmark_mul_throughput,
    benchmark_sub_latency, benchmark_sub_throughput,
};
use p3_field_testing::benchmark_sum_array;
use p3_koala_bear::KoalaBear;
use p3_util::pretty_name;
use rand::rngs::SmallRng;
use rand::{Rng, SeedableRng};

type F = KoalaBear;
type PF = <KoalaBear as Field>::Packing;

fn bench_field(c: &mut Criterion) {
    let name = "KoalaBear";
    const REPS: usize = 500;
    benchmark_inv::<F>(c, name);
    benchmark_mul_2exp::<F, 100>(c, name, 16);
    benchmark_mul_2exp::<F, 100>(c, name, 64);
    benchmark_mul_2exp::<F, 100>(c, name, (1 << 63) - 1);
    benchmark_div_2exp::<F, 100>(c, name, 16);
    benchmark_div_2exp::<F, 100>(c, name, 33);
    benchmark_div_2exp::<F, 100>(c, name, (1 << 63) - 1);
    benchmark_iter_sum::<F, 4, REPS>(c, name);
    benchmark_sum_array::<F, 4, REPS>(c, name);
    benchmark_iter_sum::<F, 8, REPS>(c, name);
    benchmark_sum_array::<F, 8, REPS>(c, name);

    // Note that each round of throughput has 10 operations
    // So we should have 10 * more repetitions for latency tests.
    const L_REPS: usize = 10 * REPS;
    benchmark_add_latency::<F, L_REPS>(c, name);
    benchmark_add_throughput::<F, REPS>(c, name);
    benchmark_sub_latency::<F, L_REPS>(c, name);
    benchmark_sub_throughput::<F, REPS>(c, name);

    let mut rng = SmallRng::seed_from_u64(1);
    c.bench_function("3rd_root", |b| {
        b.iter_batched(
            || rng.random::<F>(),
            |x| x.exp_u64(1420470955),
            BatchSize::SmallInput,
        )
    });
}

fn bench_packedfield(c: &mut Criterion) {
    let name = &pretty_name::<PF>();
    // Note that each round of throughput has 10 operations
    // So we should have 10 * more repetitions for latency tests.
    const REPS: usize = 100;
    const L_REPS: usize = 10 * REPS;

    // Choosing constants so that the number of summations is the same.
    benchmark_iter_sum::<PF, 64, 46>(c, name);
    benchmark_sum_array::<PF, 64, 46>(c, name);
    benchmark_iter_sum::<PF, 2944, 1>(c, name);
    benchmark_sum_array::<PF, 2944, 1>(c, name);

    benchmark_add_latency::<<F as Field>::Packing, L_REPS>(c, name);
    benchmark_add_throughput::<<F as Field>::Packing, REPS>(c, name);
    benchmark_sub_latency::<<F as Field>::Packing, L_REPS>(c, name);
    benchmark_sub_throughput::<<F as Field>::Packing, REPS>(c, name);
    benchmark_mul_latency::<<F as Field>::Packing, L_REPS>(c, name);
    benchmark_mul_throughput::<<F as Field>::Packing, REPS>(c, name);
}

criterion_group!(koala_bear_arithmetic, bench_field, bench_packedfield);
criterion_main!(koala_bear_arithmetic);
