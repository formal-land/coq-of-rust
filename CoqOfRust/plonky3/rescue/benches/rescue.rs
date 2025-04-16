use core::any::type_name;
use core::array;

use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use p3_baby_bear::{BabyBear, MdsMatrixBabyBear};
use p3_field::{Algebra, Field, PermutationMonomial, PrimeField64};
use p3_goldilocks::{Goldilocks, MdsMatrixGoldilocks};
use p3_mds::MdsPermutation;
use p3_mds::integrated_coset_mds::IntegratedCosetMds;
use p3_mersenne_31::{MdsMatrixMersenne31, Mersenne31};
use p3_rescue::Rescue;
use p3_symmetric::Permutation;
use rand::distr::{Distribution, StandardUniform};
use rand::rngs::SmallRng;
use rand::{Rng, SeedableRng};

fn bench_rescue(c: &mut Criterion) {
    rescue::<BabyBear, BabyBear, IntegratedCosetMds<_, 16>, 16, 7>(c);
    rescue::<BabyBear, <BabyBear as Field>::Packing, IntegratedCosetMds<BabyBear, 16>, 16, 7>(c);
    rescue::<BabyBear, BabyBear, MdsMatrixBabyBear, 24, 7>(c);
    rescue::<BabyBear, BabyBear, MdsMatrixBabyBear, 32, 7>(c);

    rescue::<Goldilocks, Goldilocks, MdsMatrixGoldilocks, 8, 7>(c);
    rescue::<Goldilocks, Goldilocks, MdsMatrixGoldilocks, 12, 7>(c);
    rescue::<Goldilocks, Goldilocks, MdsMatrixGoldilocks, 16, 7>(c);

    rescue::<Mersenne31, Mersenne31, MdsMatrixMersenne31, 16, 5>(c);
    rescue::<Mersenne31, Mersenne31, MdsMatrixMersenne31, 32, 5>(c);
}

fn rescue<F, A, Mds, const WIDTH: usize, const ALPHA: u64>(c: &mut Criterion)
where
    F: PrimeField64 + PermutationMonomial<ALPHA>,
    A: Algebra<F> + PermutationMonomial<ALPHA>,
    StandardUniform: Distribution<F>,
    Mds: MdsPermutation<A, WIDTH> + Default,
{
    // 8 rounds seems to work for the configs we use in practice. For benchmarking purposes we will
    // assume it suffices; for real usage the Sage calculation in the paper should be used.
    const NUM_ROUNDS: usize = 8;

    let rng = SmallRng::seed_from_u64(1);
    let num_constants = 2 * WIDTH * NUM_ROUNDS;
    let round_constants = rng
        .sample_iter(StandardUniform)
        .take(num_constants)
        .collect();
    let mds = Mds::default();
    let rescue = Rescue::<F, Mds, WIDTH, ALPHA>::new(NUM_ROUNDS, round_constants, mds);
    let input: [A; WIDTH] = array::from_fn(|_| A::ZERO);
    let name = format!("rescue::<{}, {}>", type_name::<A>(), ALPHA);
    let id = BenchmarkId::new(name, WIDTH);
    c.bench_with_input(id, &input, |b, input| {
        b.iter(|| rescue.permute(input.clone()))
    });
}

criterion_group!(benches, bench_rescue);
criterion_main!(benches);
