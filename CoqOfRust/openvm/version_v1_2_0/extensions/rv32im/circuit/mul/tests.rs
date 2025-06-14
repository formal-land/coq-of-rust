use std::borrow::BorrowMut;

use openvm_circuit::{
    arch::{
        testing::{TestAdapterChip, VmChipTestBuilder, RANGE_TUPLE_CHECKER_BUS},
        ExecutionBridge, VmAdapterChip, VmChipWrapper,
    },
    utils::generate_long_number,
};
use openvm_circuit_primitives::range_tuple::{RangeTupleCheckerBus, SharedRangeTupleCheckerChip};
use openvm_instructions::{instruction::Instruction, LocalOpcode};
use openvm_rv32im_transpiler::MulOpcode;
use openvm_stark_backend::{
    p3_air::BaseAir,
    p3_field::FieldAlgebra,
    p3_matrix::{
        dense::{DenseMatrix, RowMajorMatrix},
        Matrix,
    },
    utils::disable_debug_builder,
    verifier::VerificationError,
    ChipUsageGetter,
};
use openvm_stark_sdk::{p3_baby_bear::BabyBear, utils::create_seeded_rng};

use super::core::run_mul;
use crate::{
    adapters::{Rv32MultAdapterChip, RV32_CELL_BITS, RV32_REGISTER_NUM_LIMBS},
    mul::{MultiplicationCoreChip, MultiplicationCoreCols, Rv32MultiplicationChip},
    test_utils::rv32_rand_write_register_or_imm,
};

type F = BabyBear;

//////////////////////////////////////////////////////////////////////////////////////
// POSITIVE TESTS
//
// Randomly generate computations and execute, ensuring that the generated trace
// passes all constraints.
//////////////////////////////////////////////////////////////////////////////////////

fn run_rv32_mul_rand_test(num_ops: usize) {
    // the max number of limbs we currently support MUL for is 32 (i.e. for U256s)
    const MAX_NUM_LIMBS: u32 = 32;
    let mut rng = create_seeded_rng();

    let range_tuple_bus = RangeTupleCheckerBus::new(
        RANGE_TUPLE_CHECKER_BUS,
        [1 << RV32_CELL_BITS, MAX_NUM_LIMBS * (1 << RV32_CELL_BITS)],
    );
    let range_tuple_checker = SharedRangeTupleCheckerChip::new(range_tuple_bus);

    let mut tester = VmChipTestBuilder::default();
    let mut chip = Rv32MultiplicationChip::<F>::new(
        Rv32MultAdapterChip::new(
            tester.execution_bus(),
            tester.program_bus(),
            tester.memory_bridge(),
        ),
        MultiplicationCoreChip::new(range_tuple_checker.clone(), MulOpcode::CLASS_OFFSET),
        tester.offline_memory_mutex_arc(),
    );

    for _ in 0..num_ops {
        let b = generate_long_number::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(&mut rng);
        let c = generate_long_number::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(&mut rng);

        let (mut instruction, rd) = rv32_rand_write_register_or_imm(
            &mut tester,
            b,
            c,
            None,
            MulOpcode::MUL.global_opcode().as_usize(),
            &mut rng,
        );
        instruction.e = F::ZERO;
        tester.execute(&mut chip, &instruction);

        let (a, _) = run_mul::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(&b, &c);
        assert_eq!(
            a.map(F::from_canonical_u32),
            tester.read::<RV32_REGISTER_NUM_LIMBS>(1, rd)
        )
    }

    let tester = tester
        .build()
        .load(chip)
        .load(range_tuple_checker)
        .finalize();
    tester.simple_test().expect("Verification failed");
}

#[test]
fn rv32_mul_rand_test() {
    run_rv32_mul_rand_test(1);
}

//////////////////////////////////////////////////////////////////////////////////////
// NEGATIVE TESTS
//
// Given a fake trace of a single operation, setup a chip and run the test. We replace
// the write part of the trace and check that the core chip throws the expected error.
// A dummy adapter is used so memory interactions don't indirectly cause false passes.
//////////////////////////////////////////////////////////////////////////////////////

type Rv32MultiplicationTestChip<F> = VmChipWrapper<
    F,
    TestAdapterChip<F>,
    MultiplicationCoreChip<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>,
>;

#[allow(clippy::too_many_arguments)]
fn run_rv32_mul_negative_test(
    a: [u32; RV32_REGISTER_NUM_LIMBS],
    b: [u32; RV32_REGISTER_NUM_LIMBS],
    c: [u32; RV32_REGISTER_NUM_LIMBS],
    is_valid: bool,
    interaction_error: bool,
) {
    const MAX_NUM_LIMBS: u32 = 32;
    let range_tuple_bus = RangeTupleCheckerBus::new(
        RANGE_TUPLE_CHECKER_BUS,
        [1 << RV32_CELL_BITS, MAX_NUM_LIMBS * (1 << RV32_CELL_BITS)],
    );
    let range_tuple_chip = SharedRangeTupleCheckerChip::new(range_tuple_bus);

    let mut tester = VmChipTestBuilder::default();
    let mut chip = Rv32MultiplicationTestChip::<F>::new(
        TestAdapterChip::new(
            vec![[b.map(F::from_canonical_u32), c.map(F::from_canonical_u32)].concat()],
            vec![None],
            ExecutionBridge::new(tester.execution_bus(), tester.program_bus()),
        ),
        MultiplicationCoreChip::new(range_tuple_chip.clone(), MulOpcode::CLASS_OFFSET),
        tester.offline_memory_mutex_arc(),
    );

    tester.execute(
        &mut chip,
        &Instruction::from_usize(MulOpcode::MUL.global_opcode(), [0, 0, 0, 1, 0]),
    );

    let trace_width = chip.trace_width();
    let adapter_width = BaseAir::<F>::width(chip.adapter.air());
    let (_, carry) = run_mul::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(&b, &c);

    range_tuple_chip.clear();
    if is_valid {
        for (a, carry) in a.iter().zip(carry.iter()) {
            range_tuple_chip.add_count(&[*a, *carry]);
        }
    }

    let modify_trace = |trace: &mut DenseMatrix<BabyBear>| {
        let mut values = trace.row_slice(0).to_vec();
        let cols: &mut MultiplicationCoreCols<F, RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS> =
            values.split_at_mut(adapter_width).1.borrow_mut();
        cols.a = a.map(F::from_canonical_u32);
        cols.is_valid = F::from_bool(is_valid);
        *trace = RowMajorMatrix::new(values, trace_width);
    };

    disable_debug_builder();
    let tester = tester
        .build()
        .load_and_prank_trace(chip, modify_trace)
        .load(range_tuple_chip)
        .finalize();
    tester.simple_test_with_expected_error(if interaction_error {
        VerificationError::ChallengePhaseError
    } else {
        VerificationError::OodEvaluationMismatch
    });
}

#[test]
fn rv32_mul_wrong_negative_test() {
    run_rv32_mul_negative_test(
        [63, 247, 125, 234],
        [51, 109, 78, 142],
        [197, 85, 150, 32],
        true,
        true,
    );
}

#[test]
fn rv32_mul_is_valid_false_negative_test() {
    run_rv32_mul_negative_test(
        [63, 247, 125, 234],
        [51, 109, 78, 142],
        [197, 85, 150, 32],
        false,
        true,
    );
}

///////////////////////////////////////////////////////////////////////////////////////
/// SANITY TESTS
///
/// Ensure that solve functions produce the correct results.
///////////////////////////////////////////////////////////////////////////////////////

#[test]
fn run_mul_sanity_test() {
    let x: [u32; RV32_REGISTER_NUM_LIMBS] = [197, 85, 150, 32];
    let y: [u32; RV32_REGISTER_NUM_LIMBS] = [51, 109, 78, 142];
    let z: [u32; RV32_REGISTER_NUM_LIMBS] = [63, 247, 125, 232];
    let c: [u32; RV32_REGISTER_NUM_LIMBS] = [39, 100, 126, 205];
    let (result, carry) = run_mul::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(&x, &y);
    for i in 0..RV32_REGISTER_NUM_LIMBS {
        assert_eq!(z[i], result[i]);
        assert_eq!(c[i], carry[i]);
    }
}
