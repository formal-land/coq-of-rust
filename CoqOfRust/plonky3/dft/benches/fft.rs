use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use p3_baby_bear::BabyBear;
use p3_dft::{Radix2Bowers, Radix2Dit, Radix2DitParallel, TwoAdicSubgroupDft};
use p3_field::extension::{BinomialExtensionField, Complex};
use p3_field::{Algebra, BasedVectorSpace, TwoAdicField};
use p3_goldilocks::Goldilocks;
use p3_matrix::dense::RowMajorMatrix;
use p3_mersenne_31::{Mersenne31, Mersenne31ComplexRadix2Dit, Mersenne31Dft};
use p3_monty_31::dft::RecursiveDft;
use p3_util::pretty_name;
use rand::SeedableRng;
use rand::distr::{Distribution, StandardUniform};
use rand::rngs::SmallRng;

fn bench_fft(c: &mut Criterion) {
    // log_sizes correspond to the sizes of DFT we want to benchmark;
    // for the DFT over the quadratic extension "Mersenne31Complex" a
    // fairer comparison is to use half sizes, which is the log minus 1.
    let log_sizes = &[14, 16, 18, 20, 22];
    let log_half_sizes = &[13, 15, 17];

    const BATCH_SIZE: usize = 256;
    type BBExt = BinomialExtensionField<BabyBear, 5>;

    fft::<BabyBear, Radix2Dit<_>, BATCH_SIZE>(c, log_sizes);
    fft::<BabyBear, RecursiveDft<_>, BATCH_SIZE>(c, log_sizes);
    fft::<BabyBear, Radix2Bowers, BATCH_SIZE>(c, log_sizes);
    fft::<BabyBear, Radix2DitParallel<_>, BATCH_SIZE>(c, log_sizes);
    fft::<Goldilocks, Radix2Dit<_>, BATCH_SIZE>(c, log_sizes);
    fft::<Goldilocks, Radix2Bowers, BATCH_SIZE>(c, log_sizes);
    fft::<Goldilocks, Radix2DitParallel<_>, BATCH_SIZE>(c, log_sizes);
    fft::<Complex<Mersenne31>, Radix2Dit<_>, BATCH_SIZE>(c, log_half_sizes);
    fft::<Complex<Mersenne31>, Radix2Bowers, BATCH_SIZE>(c, log_half_sizes);
    fft::<Complex<Mersenne31>, Radix2DitParallel<_>, BATCH_SIZE>(c, log_half_sizes);

    fft::<Complex<Mersenne31>, Mersenne31ComplexRadix2Dit, BATCH_SIZE>(c, log_half_sizes);
    m31_fft::<Radix2Dit<_>, BATCH_SIZE>(c, log_sizes);
    m31_fft::<Mersenne31ComplexRadix2Dit, BATCH_SIZE>(c, log_sizes);

    ifft::<Goldilocks, Radix2Dit<_>, BATCH_SIZE>(c, log_sizes);

    coset_lde::<BabyBear, RecursiveDft<_>, BATCH_SIZE>(c, log_sizes);
    coset_lde::<BabyBear, Radix2Dit<_>, BATCH_SIZE>(c, log_sizes);
    coset_lde::<BabyBear, Radix2Bowers, BATCH_SIZE>(c, log_sizes);
    coset_lde::<BabyBear, Radix2DitParallel<_>, BATCH_SIZE>(c, log_sizes);
    coset_lde::<Goldilocks, Radix2Bowers, BATCH_SIZE>(c, log_sizes);

    // The FFT is much slower when handling extension fields so we use smaller sizes:
    let ext_log_sizes = &[10, 12, 14];
    const EXT_BATCH_SIZE: usize = 50;
    fft::<BBExt, Radix2Dit<_>, EXT_BATCH_SIZE>(c, ext_log_sizes);
    fft::<BBExt, Radix2DitParallel<_>, EXT_BATCH_SIZE>(c, ext_log_sizes);
    fft_algebra::<BabyBear, BBExt, Radix2Dit<_>, EXT_BATCH_SIZE>(c, ext_log_sizes);
    fft_algebra::<BabyBear, BBExt, Radix2DitParallel<_>, EXT_BATCH_SIZE>(c, ext_log_sizes);
    fft_algebra::<BabyBear, BBExt, RecursiveDft<_>, EXT_BATCH_SIZE>(c, ext_log_sizes);
}

fn fft<F, Dft, const BATCH_SIZE: usize>(c: &mut Criterion, log_sizes: &[usize])
where
    F: TwoAdicField,
    Dft: TwoAdicSubgroupDft<F>,
    StandardUniform: Distribution<F>,
{
    let mut group = c.benchmark_group(format!(
        "fft/{}/{}/ncols={}",
        pretty_name::<F>(),
        pretty_name::<Dft>(),
        BATCH_SIZE
    ));
    group.sample_size(10);

    let mut rng = SmallRng::seed_from_u64(1);
    for n_log in log_sizes {
        let n = 1 << n_log;

        let messages = RowMajorMatrix::rand(&mut rng, n, BATCH_SIZE);

        let dft = Dft::default();
        group.bench_with_input(BenchmarkId::from_parameter(n), &dft, |b, dft| {
            b.iter(|| {
                dft.dft_batch(messages.clone());
            });
        });
    }
}

fn fft_algebra<F, V, Dft, const BATCH_SIZE: usize>(c: &mut Criterion, log_sizes: &[usize])
where
    F: TwoAdicField,
    V: Algebra<F> + BasedVectorSpace<F> + Clone + Default + Send + Sync,
    Dft: TwoAdicSubgroupDft<F>,
    StandardUniform: Distribution<V>,
{
    let mut group = c.benchmark_group(format!(
        "fft_algebra/{}/{}/{}/ncols={}",
        pretty_name::<F>(),
        pretty_name::<Dft>(),
        pretty_name::<V>(),
        BATCH_SIZE
    ));
    group.sample_size(10);

    let mut rng = SmallRng::seed_from_u64(1);
    for n_log in log_sizes {
        let n = 1 << n_log;

        let messages = RowMajorMatrix::<V>::rand(&mut rng, n, BATCH_SIZE);

        let dft = Dft::default();
        group.bench_with_input(BenchmarkId::from_parameter(n), &dft, |b, dft| {
            b.iter(|| {
                dft.dft_algebra_batch(messages.clone());
            });
        });
    }
}

fn m31_fft<Dft, const BATCH_SIZE: usize>(c: &mut Criterion, log_sizes: &[usize])
where
    Dft: TwoAdicSubgroupDft<Complex<Mersenne31>>,
    StandardUniform: Distribution<Mersenne31>,
{
    let mut group = c.benchmark_group(format!(
        "m31_fft::<{}, {}>",
        pretty_name::<Dft>(),
        BATCH_SIZE
    ));
    group.sample_size(10);

    let mut rng = SmallRng::seed_from_u64(1);
    for n_log in log_sizes {
        let n = 1 << n_log;

        let messages = RowMajorMatrix::rand(&mut rng, n, BATCH_SIZE);

        group.bench_function(BenchmarkId::from_parameter(n), |b| {
            b.iter(|| {
                Mersenne31Dft::dft_batch::<Dft>(messages.clone());
            });
        });
    }
}

fn ifft<F, Dft, const BATCH_SIZE: usize>(c: &mut Criterion, log_sizes: &[usize])
where
    F: TwoAdicField,
    Dft: TwoAdicSubgroupDft<F>,
    StandardUniform: Distribution<F>,
{
    let mut group = c.benchmark_group(format!(
        "ifft/{}/{}/ncols={}",
        pretty_name::<F>(),
        pretty_name::<Dft>(),
        BATCH_SIZE
    ));
    group.sample_size(10);

    let mut rng = SmallRng::seed_from_u64(1);
    for n_log in log_sizes {
        let n = 1 << n_log;

        let messages = RowMajorMatrix::rand(&mut rng, n, BATCH_SIZE);

        let dft = Dft::default();
        group.bench_with_input(BenchmarkId::from_parameter(n), &dft, |b, dft| {
            b.iter(|| {
                dft.idft_batch(messages.clone());
            });
        });
    }
}

fn coset_lde<F, Dft, const BATCH_SIZE: usize>(c: &mut Criterion, log_sizes: &[usize])
where
    F: TwoAdicField,
    Dft: TwoAdicSubgroupDft<F>,
    StandardUniform: Distribution<F>,
{
    let mut group = c.benchmark_group(format!(
        "coset_lde/{}/{}/ncols={}",
        pretty_name::<F>(),
        pretty_name::<Dft>(),
        BATCH_SIZE
    ));
    group.sample_size(10);

    let mut rng = SmallRng::seed_from_u64(1);
    for n_log in log_sizes {
        let n = 1 << n_log;

        let messages = RowMajorMatrix::rand(&mut rng, n, BATCH_SIZE);

        let dft = Dft::default();
        group.bench_with_input(BenchmarkId::from_parameter(n), &dft, |b, dft| {
            b.iter(|| {
                dft.coset_lde_batch(messages.clone(), 1, F::GENERATOR);
            });
        });
    }
}

criterion_group!(benches, bench_fft);
criterion_main!(benches);
