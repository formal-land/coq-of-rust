use alloc::format;
use alloc::vec::Vec;

use criterion::{BatchSize, Criterion, black_box};
use p3_field::{Field, PrimeCharacteristicRing};
use rand::distr::StandardUniform;
use rand::prelude::Distribution;
use rand::rngs::SmallRng;
use rand::{Rng, SeedableRng};

pub fn benchmark_square<F: Field>(c: &mut Criterion, name: &str)
where
    StandardUniform: Distribution<F>,
{
    let mut rng = SmallRng::seed_from_u64(1);
    let x = rng.random::<F>();
    c.bench_function(&format!("{} square", name), |b| {
        b.iter(|| black_box(black_box(x).square()))
    });
}

pub fn benchmark_inv<F: Field>(c: &mut Criterion, name: &str)
where
    StandardUniform: Distribution<F>,
{
    let mut rng = SmallRng::seed_from_u64(1);
    let x = rng.random::<F>();
    c.bench_function(&format!("{} inv", name), |b| {
        b.iter(|| black_box(black_box(x)).inverse())
    });
}

pub fn benchmark_mul_2exp<R: PrimeCharacteristicRing + Copy, const REPS: usize>(
    c: &mut Criterion,
    name: &str,
    val: u64,
) where
    StandardUniform: Distribution<R>,
{
    let mut rng = SmallRng::seed_from_u64(1);
    let mut input = Vec::new();
    for _ in 0..REPS {
        input.push(rng.random::<R>())
    }
    c.bench_function(&format!("{} mul_2exp_u64 {}", name, val), |b| {
        b.iter(|| input.iter_mut().for_each(|i| *i = i.mul_2exp_u64(val)))
    });
}

pub fn benchmark_div_2exp<F: Field, const REPS: usize>(c: &mut Criterion, name: &str, val: u64)
where
    StandardUniform: Distribution<F>,
{
    let mut rng = SmallRng::seed_from_u64(1);
    let mut input = Vec::new();
    for _ in 0..REPS {
        input.push(rng.random::<F>())
    }
    c.bench_function(&format!("{} div_2exp_u64 {}", name, val), |b| {
        b.iter(|| input.iter_mut().for_each(|i| *i = i.div_2exp_u64(val)))
    });
}

/// Benchmark the time taken to sum an array [[F; N]; REPS] by summing each array
/// [F; N] using .sum() method and accumulating the sums into an accumulator.
///
/// Making N larger and REPS smaller (vs the opposite) leans the benchmark more sensitive towards
/// the latency (resp throughput) of the sum method.
pub fn benchmark_iter_sum<R: PrimeCharacteristicRing + Copy, const N: usize, const REPS: usize>(
    c: &mut Criterion,
    name: &str,
) where
    StandardUniform: Distribution<R>,
{
    let mut rng = SmallRng::seed_from_u64(1);
    let mut input = Vec::new();
    for _ in 0..REPS {
        input.push(rng.random::<[R; N]>())
    }
    c.bench_function(&format!("{} sum/{}, {}", name, REPS, N), |b| {
        b.iter(|| {
            let mut acc = R::ZERO;
            for row in &mut input {
                acc += row.iter().copied().sum()
            }
            acc
        })
    });
}

/// Benchmark the time taken to sum an array [[F; N]; REPS] by summing each array
/// [F; N] using sum_array method and accumulating the sums into an accumulator.
///
/// Making N larger and REPS smaller (vs the opposite) leans the benchmark more sensitive towards
/// the latency (resp throughput) of the sum method.
pub fn benchmark_sum_array<R: PrimeCharacteristicRing + Copy, const N: usize, const REPS: usize>(
    c: &mut Criterion,
    name: &str,
) where
    StandardUniform: Distribution<R>,
{
    let mut rng = SmallRng::seed_from_u64(1);
    let mut input = Vec::new();
    for _ in 0..REPS {
        input.push(rng.random::<[R; N]>())
    }
    c.bench_function(&format!("{} tree sum/{}, {}", name, REPS, N), |b| {
        b.iter(|| {
            let mut acc = R::ZERO;
            for row in &mut input {
                acc += R::sum_array::<N>(row)
            }
            acc
        })
    });
}

pub fn benchmark_add_latency<R: PrimeCharacteristicRing + Copy, const N: usize>(
    c: &mut Criterion,
    name: &str,
) where
    StandardUniform: Distribution<R>,
{
    c.bench_function(&format!("add-latency/{} {}", N, name), |b| {
        b.iter_batched(
            || {
                let mut rng = SmallRng::seed_from_u64(1);
                let mut vec = Vec::new();
                for _ in 0..N {
                    vec.push(rng.random::<R>())
                }
                vec
            },
            |x| x.iter().fold(R::ZERO, |x, y| x + *y),
            BatchSize::SmallInput,
        )
    });
}

pub fn benchmark_add_throughput<R: PrimeCharacteristicRing + Copy, const N: usize>(
    c: &mut Criterion,
    name: &str,
) where
    StandardUniform: Distribution<R>,
{
    c.bench_function(&format!("add-throughput/{} {}", N, name), |b| {
        b.iter_batched(
            || {
                let mut rng = SmallRng::seed_from_u64(1);
                (
                    rng.random::<R>(),
                    rng.random::<R>(),
                    rng.random::<R>(),
                    rng.random::<R>(),
                    rng.random::<R>(),
                    rng.random::<R>(),
                    rng.random::<R>(),
                    rng.random::<R>(),
                    rng.random::<R>(),
                    rng.random::<R>(),
                )
            },
            |(mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h, mut i, mut j)| {
                for _ in 0..N {
                    (a, b, c, d, e, f, g, h, i, j) = (
                        a + b,
                        b + c,
                        c + d,
                        d + e,
                        e + f,
                        f + g,
                        g + h,
                        h + i,
                        i + j,
                        j + a,
                    );
                }
                (a, b, c, d, e, f, g, h, i, j)
            },
            BatchSize::SmallInput,
        )
    });
}

pub fn benchmark_sub_latency<R: PrimeCharacteristicRing + Copy, const N: usize>(
    c: &mut Criterion,
    name: &str,
) where
    StandardUniform: Distribution<R>,
{
    c.bench_function(&format!("sub-latency/{} {}", N, name), |b| {
        b.iter_batched(
            || {
                let mut rng = SmallRng::seed_from_u64(1);
                let mut vec = Vec::new();
                for _ in 0..N {
                    vec.push(rng.random::<R>())
                }
                vec
            },
            |x| x.iter().fold(R::ZERO, |x, y| x - *y),
            BatchSize::SmallInput,
        )
    });
}

pub fn benchmark_sub_throughput<R: PrimeCharacteristicRing + Copy, const N: usize>(
    c: &mut Criterion,
    name: &str,
) where
    StandardUniform: Distribution<R>,
{
    c.bench_function(&format!("sub-throughput/{} {}", N, name), |b| {
        b.iter_batched(
            || {
                let mut rng = SmallRng::seed_from_u64(1);
                (
                    rng.random::<R>(),
                    rng.random::<R>(),
                    rng.random::<R>(),
                    rng.random::<R>(),
                    rng.random::<R>(),
                    rng.random::<R>(),
                    rng.random::<R>(),
                    rng.random::<R>(),
                    rng.random::<R>(),
                    rng.random::<R>(),
                )
            },
            |(mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h, mut i, mut j)| {
                for _ in 0..N {
                    (a, b, c, d, e, f, g, h, i, j) = (
                        a - b,
                        b - c,
                        c - d,
                        d - e,
                        e - f,
                        f - g,
                        g - h,
                        h - i,
                        i - j,
                        j - a,
                    );
                }
                (a, b, c, d, e, f, g, h, i, j)
            },
            BatchSize::SmallInput,
        )
    });
}

pub fn benchmark_mul_latency<R: PrimeCharacteristicRing + Copy, const N: usize>(
    c: &mut Criterion,
    name: &str,
) where
    StandardUniform: Distribution<R>,
{
    c.bench_function(&format!("mul-latency/{} {}", N, name), |b| {
        b.iter_batched(
            || {
                let mut rng = SmallRng::seed_from_u64(1);
                let mut vec = Vec::new();
                for _ in 0..N {
                    vec.push(rng.random::<R>())
                }
                vec
            },
            |x| x.iter().fold(R::ZERO, |x, y| x * *y),
            BatchSize::SmallInput,
        )
    });
}

pub fn benchmark_mul_throughput<R: PrimeCharacteristicRing + Copy, const N: usize>(
    c: &mut Criterion,
    name: &str,
) where
    StandardUniform: Distribution<R>,
{
    c.bench_function(&format!("mul-throughput/{} {}", N, name), |b| {
        b.iter_batched(
            || {
                let mut rng = SmallRng::seed_from_u64(1);
                (
                    rng.random::<R>(),
                    rng.random::<R>(),
                    rng.random::<R>(),
                    rng.random::<R>(),
                    rng.random::<R>(),
                    rng.random::<R>(),
                    rng.random::<R>(),
                    rng.random::<R>(),
                    rng.random::<R>(),
                    rng.random::<R>(),
                )
            },
            |(mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h, mut i, mut j)| {
                for _ in 0..N {
                    (a, b, c, d, e, f, g, h, i, j) = (
                        a * b,
                        b * c,
                        c * d,
                        d * e,
                        e * f,
                        f * g,
                        g * h,
                        h * i,
                        i * j,
                        j * a,
                    );
                }
                (a, b, c, d, e, f, g, h, i, j)
            },
            BatchSize::SmallInput,
        )
    });
}
