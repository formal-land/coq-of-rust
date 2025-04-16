use criterion::{BenchmarkId, Criterion, criterion_group, criterion_main};
use p3_baby_bear::{BabyBear, Poseidon2BabyBear};
use p3_bn254_fr::{Bn254Fr, Poseidon2Bn254};
use p3_field::{Field, PrimeCharacteristicRing};
use p3_goldilocks::{Goldilocks, Poseidon2Goldilocks};
use p3_koala_bear::{KoalaBear, Poseidon2KoalaBear};
use p3_mersenne_31::{Mersenne31, Poseidon2Mersenne31};
use p3_symmetric::Permutation;
use p3_util::pretty_name;
use rand::SeedableRng;
use rand::rngs::SmallRng;

fn bench_poseidon2(c: &mut Criterion) {
    let mut rng = SmallRng::seed_from_u64(1);

    let poseidon2_bb_16 = Poseidon2BabyBear::<16>::new_from_rng_128(&mut rng);
    poseidon2::<BabyBear, Poseidon2BabyBear<16>, 16>(c, poseidon2_bb_16);
    let poseidon2_bb_24 = Poseidon2BabyBear::<24>::new_from_rng_128(&mut rng);
    poseidon2::<BabyBear, Poseidon2BabyBear<24>, 24>(c, poseidon2_bb_24);

    let poseidon2_kb_16 = Poseidon2KoalaBear::<16>::new_from_rng_128(&mut rng);
    poseidon2::<KoalaBear, Poseidon2KoalaBear<16>, 16>(c, poseidon2_kb_16);
    let poseidon2_kb_24 = Poseidon2KoalaBear::<24>::new_from_rng_128(&mut rng);
    poseidon2::<KoalaBear, Poseidon2KoalaBear<24>, 24>(c, poseidon2_kb_24);

    let poseidon2_m31_16 = Poseidon2Mersenne31::<16>::new_from_rng_128(&mut rng);
    poseidon2::<Mersenne31, Poseidon2Mersenne31<16>, 16>(c, poseidon2_m31_16);
    let poseidon2_m31_24 = Poseidon2Mersenne31::<24>::new_from_rng_128(&mut rng);
    poseidon2::<Mersenne31, Poseidon2Mersenne31<24>, 24>(c, poseidon2_m31_24);

    let poseidon2_gold_8 = Poseidon2Goldilocks::<8>::new_from_rng_128(&mut rng);
    poseidon2::<Goldilocks, Poseidon2Goldilocks<8>, 8>(c, poseidon2_gold_8);
    let poseidon2_gold_12 = Poseidon2Goldilocks::<12>::new_from_rng_128(&mut rng);
    poseidon2::<Goldilocks, Poseidon2Goldilocks<12>, 12>(c, poseidon2_gold_12);
    let poseidon2_gold_16 = Poseidon2Goldilocks::<16>::new_from_rng_128(&mut rng);
    poseidon2::<Goldilocks, Poseidon2Goldilocks<16>, 16>(c, poseidon2_gold_16);

    // We hard code the round numbers for Bn254Fr.
    let poseidon2_bn254 = Poseidon2Bn254::<3>::new_from_rng(8, 22, &mut rng);
    poseidon2::<Bn254Fr, Poseidon2Bn254<3>, 3>(c, poseidon2_bn254);
}

fn poseidon2<F, Perm, const WIDTH: usize>(c: &mut Criterion, poseidon2: Perm)
where
    F: Field,
    Perm: Permutation<[F::Packing; WIDTH]>,
{
    let input = [F::Packing::ZERO; WIDTH];
    let name = format!("poseidon2::<{}, {}>", pretty_name::<F::Packing>(), WIDTH);
    let id = BenchmarkId::new(name, WIDTH);
    c.bench_with_input(id, &input, |b, &input| b.iter(|| poseidon2.permute(input)));
}

criterion_group!(benches, bench_poseidon2);
criterion_main!(benches);
