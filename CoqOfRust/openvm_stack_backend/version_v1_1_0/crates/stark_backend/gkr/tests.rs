use std::iter::zip;

use itertools::Itertools;
use openvm_stark_sdk::{
    config::baby_bear_blake3::default_engine, engine::StarkEngine, utils::create_seeded_rng,
};
use p3_baby_bear::BabyBear;
use p3_field::FieldAlgebra;
use rand::Rng;

use crate::{
    gkr::{self, Gate, GkrArtifact, GkrError, Layer},
    poly::{multi::Mle, uni::Fraction},
};

#[test]
fn test_batch() -> Result<(), GkrError<BabyBear>> {
    const LOG_N: usize = 5;

    let engine = default_engine();
    let mut rng = create_seeded_rng();

    let col0 = Mle::new((0..1 << LOG_N).map(|_| rng.gen()).collect_vec());
    let col1 = Mle::new((0..1 << LOG_N).map(|_| rng.gen()).collect_vec());

    let product0 = col0.iter().copied().product();
    let product1 = col1.iter().copied().product();

    let input_layers = vec![
        Layer::GrandProduct(col0.clone()),
        Layer::GrandProduct(col1.clone()),
    ];
    let (proof, _) = gkr::prove_batch(&mut engine.new_challenger(), input_layers);

    let GkrArtifact {
        ood_point,
        claims_to_verify_by_instance,
        n_variables_by_instance,
    } = gkr::partially_verify_batch(
        vec![Gate::GrandProduct; 2],
        &proof,
        &mut engine.new_challenger(),
    )?;

    assert_eq!(n_variables_by_instance, [LOG_N, LOG_N]);
    assert_eq!(proof.output_claims_by_instance.len(), 2);
    assert_eq!(claims_to_verify_by_instance.len(), 2);
    assert_eq!(proof.output_claims_by_instance[0], &[product0]);
    assert_eq!(proof.output_claims_by_instance[1], &[product1]);
    let claim0 = &claims_to_verify_by_instance[0];
    let claim1 = &claims_to_verify_by_instance[1];
    assert_eq!(claim0, &[col0.eval(&ood_point)]);
    assert_eq!(claim1, &[col1.eval(&ood_point)]);
    Ok(())
}

#[test]
fn test_batch_with_different_sizes() -> Result<(), GkrError<BabyBear>> {
    let engine = default_engine();
    let mut rng = create_seeded_rng();

    const LOG_N0: usize = 5;
    const LOG_N1: usize = 7;

    let col0 = Mle::new((0..1 << LOG_N0).map(|_| rng.gen()).collect());
    let col1 = Mle::new((0..1 << LOG_N1).map(|_| rng.gen()).collect());

    let product0 = col0.iter().copied().product();
    let product1 = col1.iter().copied().product();

    let input_layers = vec![
        Layer::GrandProduct(col0.clone()),
        Layer::GrandProduct(col1.clone()),
    ];
    let (proof, _) = gkr::prove_batch(&mut engine.new_challenger(), input_layers);

    let GkrArtifact {
        ood_point,
        claims_to_verify_by_instance,
        n_variables_by_instance,
    } = gkr::partially_verify_batch(
        vec![Gate::GrandProduct; 2],
        &proof,
        &mut engine.new_challenger(),
    )?;

    assert_eq!(n_variables_by_instance, [LOG_N0, LOG_N1]);
    assert_eq!(proof.output_claims_by_instance.len(), 2);
    assert_eq!(claims_to_verify_by_instance.len(), 2);
    assert_eq!(proof.output_claims_by_instance[0], &[product0]);
    assert_eq!(proof.output_claims_by_instance[1], &[product1]);
    let claim0 = &claims_to_verify_by_instance[0];
    let claim1 = &claims_to_verify_by_instance[1];
    let n_vars = ood_point.len();
    assert_eq!(claim0, &[col0.eval(&ood_point[n_vars - LOG_N0..])]);
    assert_eq!(claim1, &[col1.eval(&ood_point[n_vars - LOG_N1..])]);
    Ok(())
}

#[test]
fn test_grand_product() -> Result<(), GkrError<BabyBear>> {
    const N: usize = 1 << 5;

    let engine = default_engine();
    let mut rng = create_seeded_rng();

    let values = (0..N).map(|_| rng.gen()).collect_vec();
    let product = values.iter().copied().product();
    let col = Mle::<BabyBear>::new(values);
    let input_layer = Layer::GrandProduct(col.clone());
    let (proof, _) = gkr::prove_batch(&mut engine.new_challenger(), vec![input_layer]);

    let GkrArtifact {
        ood_point: r,
        claims_to_verify_by_instance,
        n_variables_by_instance: _,
    } = gkr::partially_verify_batch(
        vec![Gate::GrandProduct],
        &proof,
        &mut engine.new_challenger(),
    )?;

    assert_eq!(proof.output_claims_by_instance, [vec![product]]);
    assert_eq!(claims_to_verify_by_instance, [vec![col.eval(&r)]]);
    Ok(())
}

#[test]
fn test_logup_with_generic_trace() -> Result<(), GkrError<BabyBear>> {
    const N: usize = 1 << 5;
    type F = BabyBear;
    let mut rng = create_seeded_rng();

    let numerator_values = (0..N).map(|_| rng.gen()).collect();
    let denominator_values = (0..N).map(|_| rng.gen()).collect();

    let sum: Fraction<F> = zip(&numerator_values, &denominator_values)
        .map(|(&n, &d)| Fraction::new(n, d))
        .sum();
    let numerators = Mle::<F>::new(numerator_values);
    let denominators = Mle::<F>::new(denominator_values);
    let top_layer = Layer::LogUpGeneric {
        numerators: numerators.clone(),
        denominators: denominators.clone(),
    };

    let engine = default_engine();

    let (proof, _) = gkr::prove_batch(&mut engine.new_challenger(), vec![top_layer]);

    let GkrArtifact {
        ood_point,
        claims_to_verify_by_instance,
        n_variables_by_instance: _,
    } = gkr::partially_verify_batch(vec![Gate::LogUp], &proof, &mut engine.new_challenger())?;

    assert_eq!(claims_to_verify_by_instance.len(), 1);
    assert_eq!(proof.output_claims_by_instance.len(), 1);
    assert_eq!(
        claims_to_verify_by_instance[0],
        [numerators.eval(&ood_point), denominators.eval(&ood_point)]
    );
    assert_eq!(
        proof.output_claims_by_instance[0],
        [sum.numerator, sum.denominator]
    );
    Ok(())
}

#[test]
fn test_logup_with_singles_trace() -> Result<(), GkrError<BabyBear>> {
    const N: usize = 1 << 5;
    type F = BabyBear;

    let mut rng = create_seeded_rng();
    let denominator_values = (0..N).map(|_| rng.gen()).collect_vec();
    let sum: Fraction<F> = denominator_values
        .iter()
        .map(|&d| Fraction::new(F::ONE, d))
        .sum();
    let denominators = Mle::new(denominator_values);
    let top_layer = Layer::LogUpSingles {
        denominators: denominators.clone(),
    };

    let engine = default_engine();
    let (proof, _) = gkr::prove_batch(&mut engine.new_challenger(), vec![top_layer]);

    let GkrArtifact {
        ood_point,
        claims_to_verify_by_instance,
        n_variables_by_instance: _,
    } = gkr::partially_verify_batch(vec![Gate::LogUp], &proof, &mut engine.new_challenger())?;

    assert_eq!(claims_to_verify_by_instance.len(), 1);
    assert_eq!(proof.output_claims_by_instance.len(), 1);
    assert_eq!(
        claims_to_verify_by_instance[0],
        [F::ONE, denominators.eval(&ood_point)]
    );
    assert_eq!(
        proof.output_claims_by_instance[0],
        [sum.numerator, sum.denominator]
    );
    Ok(())
}

#[test]
fn test_logup_with_multiplicities_trace() -> Result<(), GkrError<BabyBear>> {
    const N: usize = 1 << 5;
    let mut rng = create_seeded_rng();
    let numerator_values = (0..N).map(|_| rng.gen::<BabyBear>()).collect_vec();
    let denominator_values = (0..N).map(|_| rng.gen::<BabyBear>()).collect_vec();
    let sum: Fraction<BabyBear> = zip(&numerator_values, &denominator_values)
        .map(|(&n, &d)| Fraction::new(n, d))
        .sum();
    let numerators = Mle::new(numerator_values);
    let denominators = Mle::new(denominator_values);
    let top_layer = Layer::LogUpMultiplicities {
        numerators: numerators.clone(),
        denominators: denominators.clone(),
    };

    let engine = default_engine();
    let (proof, _) = gkr::prove_batch(&mut engine.new_challenger(), vec![top_layer]);

    let GkrArtifact {
        ood_point,
        claims_to_verify_by_instance,
        n_variables_by_instance: _,
    } = gkr::partially_verify_batch(vec![Gate::LogUp], &proof, &mut engine.new_challenger())?;

    assert_eq!(claims_to_verify_by_instance.len(), 1);
    assert_eq!(proof.output_claims_by_instance.len(), 1);
    assert_eq!(
        claims_to_verify_by_instance[0],
        [numerators.eval(&ood_point), denominators.eval(&ood_point)]
    );
    assert_eq!(
        proof.output_claims_by_instance[0],
        [sum.numerator, sum.denominator]
    );
    Ok(())
}
