use criterion::{Criterion, criterion_group, criterion_main};
use p3_baby_bear::BabyBear;
use p3_field::extension::BinomialExtensionField;
use p3_field_testing::bench_func::{
    benchmark_inv, benchmark_mul_latency, benchmark_mul_throughput, benchmark_square,
};

type EF4 = BinomialExtensionField<BabyBear, 4>;
type EF5 = BinomialExtensionField<BabyBear, 5>;

// Note that each round of throughput has 10 operations
// So we should have 10 * more repetitions for latency tests.
const REPS: usize = 100;
const L_REPS: usize = 10 * REPS;

fn bench_quartic_extension(c: &mut Criterion) {
    let name = "BinomialExtensionField<BabyBear, 4>";
    benchmark_square::<EF4>(c, name);
    benchmark_inv::<EF4>(c, name);
    benchmark_mul_throughput::<EF4, REPS>(c, name);
    benchmark_mul_latency::<EF4, L_REPS>(c, name);
}

fn bench_qunitic_extension(c: &mut Criterion) {
    let name = "BinomialExtensionField<BabyBear, 5>";
    benchmark_square::<EF5>(c, name);
    benchmark_inv::<EF5>(c, name);
    benchmark_mul_throughput::<EF5, REPS>(c, name);
    benchmark_mul_latency::<EF5, L_REPS>(c, name);
}

criterion_group!(
    bench_babybear_ef,
    bench_quartic_extension,
    bench_qunitic_extension
);
criterion_main!(bench_babybear_ef);
