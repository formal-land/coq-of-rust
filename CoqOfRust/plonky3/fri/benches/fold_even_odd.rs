use core::any::type_name;

use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use itertools::Itertools;
use p3_baby_bear::BabyBear;
use p3_field::TwoAdicField;
use p3_field::extension::Complex;
use p3_fri::fold_even_odd;
use p3_goldilocks::Goldilocks;
use p3_mersenne_31::Mersenne31;
use rand::distr::{Distribution, StandardUniform};
use rand::rngs::SmallRng;
use rand::{Rng, SeedableRng};

fn bench<F: TwoAdicField>(c: &mut Criterion, log_sizes: &[usize])
where
    StandardUniform: Distribution<F>,
{
    let name = format!("fold_even_odd::<{}>", type_name::<F>(),);
    let mut group = c.benchmark_group(&name);
    group.sample_size(10);

    for log_size in log_sizes {
        let n = 1 << log_size;

        let mut rng = SmallRng::seed_from_u64(n as u64);
        let beta = rng.sample(StandardUniform);
        let poly = rng.sample_iter(StandardUniform).take(n).collect_vec();

        group.bench_function(BenchmarkId::from_parameter(n), |b| {
            b.iter(|| {
                fold_even_odd(poly.clone(), beta);
            })
        });
    }
}

fn bench_fold_even_odd(c: &mut Criterion) {
    let log_sizes = [12, 14, 16, 18, 20, 22];

    bench::<BabyBear>(c, &log_sizes);
    bench::<Goldilocks>(c, &log_sizes);
    bench::<Complex<Mersenne31>>(c, &log_sizes);
}

criterion_group!(benches, bench_fold_even_odd);
criterion_main!(benches);
