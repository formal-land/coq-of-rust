use std::sync::Arc;

use openvm_stark_backend::{
    interaction::InteractionBuilder,
    p3_air::{Air, AirBuilderWithPublicValues},
    p3_field::{Field, FieldAlgebra},
    p3_matrix::{dense::RowMajorMatrix, Matrix},
    prover::types::AirProofInput,
    rap::PartitionedBaseAir,
    utils::disable_debug_builder,
    verifier::VerificationError,
    AirRef,
};
use openvm_stark_sdk::{
    config::baby_bear_poseidon2::BabyBearPoseidon2Engine, engine::StarkFriEngine,
    p3_baby_bear::BabyBear, utils::to_field_vec,
};

use crate::{
    arch::VmCoreAir,
    system::public_values::{
        columns::PublicValuesCoreColsView,
        core::{AdapterInterface, PublicValuesCoreAir},
    },
};

type F = BabyBear;

impl<F: Field> PartitionedBaseAir<F> for PublicValuesCoreAir {}

impl<AB: InteractionBuilder + AirBuilderWithPublicValues> Air<AB> for PublicValuesCoreAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local_core = main.row_slice(0);
        // It's never used, so pick any value.
        let dummy_pc = local_core[0];
        VmCoreAir::<AB, AdapterInterface<AB::Expr>>::eval(self, builder, &local_core, dummy_pc);
    }
}

#[test]
fn public_values_happy_path_1() {
    let cols = PublicValuesCoreColsView::<F, F> {
        is_valid: F::ONE,
        value: F::from_canonical_u32(12),
        index: F::from_canonical_u32(2),
        custom_pv_vars: to_field_vec(vec![1, 0]),
        _marker: Default::default(),
    };
    let air: AirRef<_> = Arc::new(PublicValuesCoreAir::new(3, 2));
    let trace = RowMajorMatrix::new_row(cols.flatten());
    let pvs = to_field_vec(vec![0, 0, 12]);

    BabyBearPoseidon2Engine::run_test_fast(vec![air], vec![AirProofInput::simple(trace, pvs)])
        .expect("Verification failed");
}

#[test]
fn public_values_neg_pv_not_match() {
    let cols = PublicValuesCoreColsView::<F, F> {
        is_valid: F::ONE,
        value: F::from_canonical_u32(12),
        index: F::from_canonical_u32(2),
        custom_pv_vars: to_field_vec(vec![1, 0]),
        _marker: Default::default(),
    };
    let air: AirRef<_> = Arc::new(PublicValuesCoreAir::new(3, 2));
    let trace = RowMajorMatrix::new_row(cols.flatten());
    let pvs = to_field_vec(vec![0, 0, 56456]);

    disable_debug_builder();
    assert_eq!(
        BabyBearPoseidon2Engine::run_test_fast(vec![air], vec![AirProofInput::simple(trace, pvs)])
            .err(),
        Some(VerificationError::OodEvaluationMismatch)
    );
}

#[test]
fn public_values_neg_index_out_of_bound() {
    let cols = PublicValuesCoreColsView::<F, F> {
        is_valid: F::ONE,
        value: F::from_canonical_u32(12),
        index: F::from_canonical_u32(8),
        custom_pv_vars: to_field_vec(vec![0, 0]),
        _marker: Default::default(),
    };
    let air: AirRef<_> = Arc::new(PublicValuesCoreAir::new(3, 2));
    let trace = RowMajorMatrix::new_row(cols.flatten());
    let pvs = to_field_vec(vec![0, 0, 0]);

    disable_debug_builder();
    assert_eq!(
        BabyBearPoseidon2Engine::run_test_fast(vec![air], vec![AirProofInput::simple(trace, pvs)])
            .err(),
        Some(VerificationError::OodEvaluationMismatch)
    );
}

#[test]
fn public_values_neg_double_publish() {
    // A public value is published twice with different values. Neither of them should be accepted.
    public_values_neg_double_publish_impl(12);
    public_values_neg_double_publish_impl(13);
}

fn public_values_neg_double_publish_impl(actual_pv: u32) {
    let rows = [
        PublicValuesCoreColsView::<F, F> {
            is_valid: F::ONE,
            value: F::from_canonical_u32(12),
            index: F::from_canonical_u32(0),
            custom_pv_vars: to_field_vec(vec![0, 1]),
            _marker: Default::default(),
        },
        PublicValuesCoreColsView::<F, F> {
            is_valid: F::ONE,
            value: F::from_canonical_u32(13),
            index: F::from_canonical_u32(0),
            custom_pv_vars: to_field_vec(vec![0, 1]),
            _marker: Default::default(),
        },
    ];
    let width = rows[0].width();
    let flatten_rows: Vec<_> = rows.into_iter().flat_map(|r| r.flatten()).collect();
    let trace = RowMajorMatrix::new(flatten_rows, width);
    let air: AirRef<_> = Arc::new(PublicValuesCoreAir::new(3, 2));
    let pvs = to_field_vec(vec![0, 0, actual_pv]);

    disable_debug_builder();
    assert_eq!(
        BabyBearPoseidon2Engine::run_test_fast(vec![air], vec![AirProofInput::simple(trace, pvs)])
            .err(),
        Some(VerificationError::OodEvaluationMismatch)
    );
}
