use criterion::{BatchSize, Criterion, criterion_group, criterion_main};
use p3_baby_bear::BabyBear;
use p3_field::extension::BinomialExtensionField;
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use rand::SeedableRng;
use rand::rngs::SmallRng;

fn columnwise_dot_product(c: &mut Criterion) {
    let mut rng = SmallRng::seed_from_u64(0);

    type F = BabyBear;
    type EF = BinomialExtensionField<F, 4>;
    let log_rows = 16;

    c.benchmark_group("babybear")
        .sample_size(10)
        .bench_function("columnwise_dot_product", |b| {
            b.iter_batched(
                || {
                    (
                        RowMajorMatrix::<F>::rand_nonzero(&mut rng, 1 << log_rows, 1 << 12),
                        RowMajorMatrix::<EF>::rand_nonzero(&mut rng, 1 << log_rows, 1).values,
                    )
                },
                |(m, v)| m.columnwise_dot_product(&v),
                BatchSize::PerIteration,
            );
        });
}

criterion_group!(benches, columnwise_dot_product);
criterion_main!(benches);
