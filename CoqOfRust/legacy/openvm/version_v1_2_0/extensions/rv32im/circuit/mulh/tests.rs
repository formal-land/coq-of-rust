use std::borrow::BorrowMut;

use openvm_circuit::{
    arch::{
        testing::{
            memory::gen_pointer, TestAdapterChip, VmChipTestBuilder, BITWISE_OP_LOOKUP_BUS,
            RANGE_TUPLE_CHECKER_BUS,
        },
        ExecutionBridge, InstructionExecutor, VmAdapterChip, VmChipWrapper,
    },
    utils::generate_long_number,
};
use openvm_circuit_primitives::{
    bitwise_op_lookup::{BitwiseOperationLookupBus, SharedBitwiseOperationLookupChip},
    range_tuple::{RangeTupleCheckerBus, SharedRangeTupleCheckerChip},
};
use openvm_instructions::{instruction::Instruction, LocalOpcode};
use openvm_rv32im_transpiler::MulHOpcode;
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
use rand::rngs::StdRng;

use super::core::run_mulh;
use crate::{
    adapters::{Rv32MultAdapterChip, RV32_CELL_BITS, RV32_REGISTER_NUM_LIMBS},
    mulh::{MulHCoreChip, MulHCoreCols, Rv32MulHChip},
};

type F = BabyBear;

//////////////////////////////////////////////////////////////////////////////////////
// POSITIVE TESTS
//
// Randomly generate computations and execute, ensuring that the generated trace
// passes all constraints.
//////////////////////////////////////////////////////////////////////////////////////

#[allow(clippy::too_many_arguments)]
fn run_rv32_mulh_rand_write_execute<E: InstructionExecutor<F>>(
    opcode: MulHOpcode,
    tester: &mut VmChipTestBuilder<F>,
    chip: &mut E,
    b: [u32; RV32_REGISTER_NUM_LIMBS],
    c: [u32; RV32_REGISTER_NUM_LIMBS],
    rng: &mut StdRng,
) {
    let rs1 = gen_pointer(rng, 4);
    let rs2 = gen_pointer(rng, 4);
    let rd = gen_pointer(rng, 4);

    tester.write::<RV32_REGISTER_NUM_LIMBS>(1, rs1, b.map(F::from_canonical_u32));
    tester.write::<RV32_REGISTER_NUM_LIMBS>(1, rs2, c.map(F::from_canonical_u32));

    let (a, _, _, _, _) = run_mulh::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(opcode, &b, &c);
    tester.execute(
        chip,
        &Instruction::from_usize(opcode.global_opcode(), [rd, rs1, rs2, 1, 0]),
    );

    assert_eq!(
        a.map(F::from_canonical_u32),
        tester.read::<RV32_REGISTER_NUM_LIMBS>(1, rd)
    );
}

fn run_rv32_mulh_rand_test(opcode: MulHOpcode, num_ops: usize) {
    // the max number of limbs we currently support MUL for is 32 (i.e. for U256s)
    const MAX_NUM_LIMBS: u32 = 32;
    let mut rng = create_seeded_rng();

    let bitwise_bus = BitwiseOperationLookupBus::new(BITWISE_OP_LOOKUP_BUS);
    let range_tuple_bus = RangeTupleCheckerBus::new(
        RANGE_TUPLE_CHECKER_BUS,
        [1 << RV32_CELL_BITS, MAX_NUM_LIMBS * (1 << RV32_CELL_BITS)],
    );

    let bitwise_chip = SharedBitwiseOperationLookupChip::<RV32_CELL_BITS>::new(bitwise_bus);
    let range_tuple_checker = SharedRangeTupleCheckerChip::new(range_tuple_bus);

    let mut tester = VmChipTestBuilder::default();
    let mut chip = Rv32MulHChip::<F>::new(
        Rv32MultAdapterChip::new(
            tester.execution_bus(),
            tester.program_bus(),
            tester.memory_bridge(),
        ),
        MulHCoreChip::new(bitwise_chip.clone(), range_tuple_checker.clone()),
        tester.offline_memory_mutex_arc(),
    );

    for _ in 0..num_ops {
        let b = generate_long_number::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(&mut rng);
        let c = generate_long_number::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(&mut rng);
        run_rv32_mulh_rand_write_execute(opcode, &mut tester, &mut chip, b, c, &mut rng);
    }

    let tester = tester
        .build()
        .load(chip)
        .load(bitwise_chip)
        .load(range_tuple_checker)
        .finalize();
    tester.simple_test().expect("Verification failed");
}

#[test]
fn rv32_mulh_rand_test() {
    run_rv32_mulh_rand_test(MulHOpcode::MULH, 100);
}

#[test]
fn rv32_mulhsu_rand_test() {
    run_rv32_mulh_rand_test(MulHOpcode::MULHSU, 100);
}

#[test]
fn rv32_mulhu_rand_test() {
    run_rv32_mulh_rand_test(MulHOpcode::MULHU, 100);
}

//////////////////////////////////////////////////////////////////////////////////////
// NEGATIVE TESTS
//
// Given a fake trace of a single operation, setup a chip and run the test. We replace
// the write part of the trace and check that the core chip throws the expected error.
// A dummy adapter is used so memory interactions don't indirectly cause false passes.
//////////////////////////////////////////////////////////////////////////////////////

type Rv32MulHTestChip<F> =
    VmChipWrapper<F, TestAdapterChip<F>, MulHCoreChip<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>>;

#[allow(clippy::too_many_arguments)]
fn run_rv32_mulh_negative_test(
    opcode: MulHOpcode,
    a: [u32; RV32_REGISTER_NUM_LIMBS],
    b: [u32; RV32_REGISTER_NUM_LIMBS],
    c: [u32; RV32_REGISTER_NUM_LIMBS],
    a_mul: [u32; RV32_REGISTER_NUM_LIMBS],
    b_ext: u32,
    c_ext: u32,
    interaction_error: bool,
) {
    const MAX_NUM_LIMBS: u32 = 32;
    let bitwise_bus = BitwiseOperationLookupBus::new(BITWISE_OP_LOOKUP_BUS);
    let range_tuple_bus = RangeTupleCheckerBus::new(
        RANGE_TUPLE_CHECKER_BUS,
        [1 << RV32_CELL_BITS, MAX_NUM_LIMBS * (1 << RV32_CELL_BITS)],
    );

    let bitwise_chip = SharedBitwiseOperationLookupChip::<RV32_CELL_BITS>::new(bitwise_bus);
    let range_tuple_chip = SharedRangeTupleCheckerChip::new(range_tuple_bus);

    let mut tester = VmChipTestBuilder::default();
    let mut chip = Rv32MulHTestChip::<F>::new(
        TestAdapterChip::new(
            vec![[b.map(F::from_canonical_u32), c.map(F::from_canonical_u32)].concat()],
            vec![None],
            ExecutionBridge::new(tester.execution_bus(), tester.program_bus()),
        ),
        MulHCoreChip::new(bitwise_chip.clone(), range_tuple_chip.clone()),
        tester.offline_memory_mutex_arc(),
    );

    tester.execute(
        &mut chip,
        &Instruction::from_usize(opcode.global_opcode(), [0, 0, 0, 1, 0]),
    );

    let trace_width = chip.trace_width();
    let adapter_width = BaseAir::<F>::width(chip.adapter.air());
    let (_, _, carry, _, _) = run_mulh::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(opcode, &b, &c);

    range_tuple_chip.clear();
    for i in 0..RV32_REGISTER_NUM_LIMBS {
        range_tuple_chip.add_count(&[a_mul[i], carry[i]]);
        range_tuple_chip.add_count(&[a[i], carry[RV32_REGISTER_NUM_LIMBS + i]]);
    }

    let modify_trace = |trace: &mut DenseMatrix<BabyBear>| {
        let mut values = trace.row_slice(0).to_vec();
        let cols: &mut MulHCoreCols<F, RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS> =
            values.split_at_mut(adapter_width).1.borrow_mut();
        cols.a = a.map(F::from_canonical_u32);
        cols.a_mul = a_mul.map(F::from_canonical_u32);
        cols.b_ext = F::from_canonical_u32(b_ext);
        cols.c_ext = F::from_canonical_u32(c_ext);
        *trace = RowMajorMatrix::new(values, trace_width);
    };

    disable_debug_builder();
    let tester = tester
        .build()
        .load_and_prank_trace(chip, modify_trace)
        .load(bitwise_chip)
        .load(range_tuple_chip)
        .finalize();
    tester.simple_test_with_expected_error(if interaction_error {
        VerificationError::ChallengePhaseError
    } else {
        VerificationError::OodEvaluationMismatch
    });
}

#[test]
fn rv32_mulh_wrong_a_mul_negative_test() {
    run_rv32_mulh_negative_test(
        MulHOpcode::MULH,
        [130, 9, 135, 241],
        [197, 85, 150, 32],
        [51, 109, 78, 142],
        [63, 247, 125, 234],
        0,
        255,
        true,
    );
}

#[test]
fn rv32_mulh_wrong_a_negative_test() {
    run_rv32_mulh_negative_test(
        MulHOpcode::MULH,
        [130, 9, 135, 242],
        [197, 85, 150, 32],
        [51, 109, 78, 142],
        [63, 247, 125, 232],
        0,
        255,
        true,
    );
}

#[test]
fn rv32_mulh_wrong_ext_negative_test() {
    run_rv32_mulh_negative_test(
        MulHOpcode::MULH,
        [1, 0, 0, 0],
        [0, 0, 0, 128],
        [2, 0, 0, 0],
        [0, 0, 0, 0],
        0,
        0,
        true,
    );
}

#[test]
fn rv32_mulh_invalid_ext_negative_test() {
    run_rv32_mulh_negative_test(
        MulHOpcode::MULH,
        [3, 2, 2, 2],
        [0, 0, 0, 128],
        [2, 0, 0, 0],
        [0, 0, 0, 0],
        1,
        0,
        false,
    );
}

#[test]
fn rv32_mulhsu_wrong_a_mul_negative_test() {
    run_rv32_mulh_negative_test(
        MulHOpcode::MULHSU,
        [174, 40, 246, 202],
        [197, 85, 150, 160],
        [51, 109, 78, 142],
        [63, 247, 125, 105],
        255,
        0,
        true,
    );
}

#[test]
fn rv32_mulhsu_wrong_a_negative_test() {
    run_rv32_mulh_negative_test(
        MulHOpcode::MULHSU,
        [174, 40, 246, 201],
        [197, 85, 150, 160],
        [51, 109, 78, 142],
        [63, 247, 125, 104],
        255,
        0,
        true,
    );
}

#[test]
fn rv32_mulhsu_wrong_b_ext_negative_test() {
    run_rv32_mulh_negative_test(
        MulHOpcode::MULHSU,
        [1, 0, 0, 0],
        [0, 0, 0, 128],
        [2, 0, 0, 0],
        [0, 0, 0, 0],
        0,
        0,
        true,
    );
}

#[test]
fn rv32_mulhsu_wrong_c_ext_negative_test() {
    run_rv32_mulh_negative_test(
        MulHOpcode::MULHSU,
        [0, 0, 0, 64],
        [0, 0, 0, 128],
        [0, 0, 0, 128],
        [0, 0, 0, 0],
        255,
        255,
        false,
    );
}

#[test]
fn rv32_mulhu_wrong_a_mul_negative_test() {
    run_rv32_mulh_negative_test(
        MulHOpcode::MULHU,
        [130, 9, 135, 241],
        [197, 85, 150, 32],
        [51, 109, 78, 142],
        [63, 247, 125, 234],
        0,
        0,
        true,
    );
}

#[test]
fn rv32_mulhu_wrong_a_negative_test() {
    run_rv32_mulh_negative_test(
        MulHOpcode::MULHU,
        [130, 9, 135, 240],
        [197, 85, 150, 32],
        [51, 109, 78, 142],
        [63, 247, 125, 232],
        0,
        0,
        true,
    );
}

#[test]
fn rv32_mulhu_wrong_ext_negative_test() {
    run_rv32_mulh_negative_test(
        MulHOpcode::MULHU,
        [255, 255, 255, 255],
        [0, 0, 0, 128],
        [2, 0, 0, 0],
        [0, 0, 0, 0],
        255,
        0,
        false,
    );
}

///////////////////////////////////////////////////////////////////////////////////////
/// SANITY TESTS
///
/// Ensure that solve functions produce the correct results.
///////////////////////////////////////////////////////////////////////////////////////

#[test]
fn run_mulh_sanity_test() {
    let x: [u32; RV32_REGISTER_NUM_LIMBS] = [197, 85, 150, 32];
    let y: [u32; RV32_REGISTER_NUM_LIMBS] = [51, 109, 78, 142];
    let z: [u32; RV32_REGISTER_NUM_LIMBS] = [130, 9, 135, 241];
    let z_mul: [u32; RV32_REGISTER_NUM_LIMBS] = [63, 247, 125, 232];
    let c: [u32; RV32_REGISTER_NUM_LIMBS] = [303, 375, 449, 463];
    let c_mul: [u32; RV32_REGISTER_NUM_LIMBS] = [39, 100, 126, 205];
    let (res, res_mul, carry, x_ext, y_ext) =
        run_mulh::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(MulHOpcode::MULH, &x, &y);
    for i in 0..RV32_REGISTER_NUM_LIMBS {
        assert_eq!(z[i], res[i]);
        assert_eq!(z_mul[i], res_mul[i]);
        assert_eq!(c[i], carry[i + RV32_REGISTER_NUM_LIMBS]);
        assert_eq!(c_mul[i], carry[i]);
    }
    assert_eq!(x_ext, 0);
    assert_eq!(y_ext, 255);
}

#[test]
fn run_mulhu_sanity_test() {
    let x: [u32; RV32_REGISTER_NUM_LIMBS] = [197, 85, 150, 32];
    let y: [u32; RV32_REGISTER_NUM_LIMBS] = [51, 109, 78, 142];
    let z: [u32; RV32_REGISTER_NUM_LIMBS] = [71, 95, 29, 18];
    let z_mul: [u32; RV32_REGISTER_NUM_LIMBS] = [63, 247, 125, 232];
    let c: [u32; RV32_REGISTER_NUM_LIMBS] = [107, 93, 18, 0];
    let c_mul: [u32; RV32_REGISTER_NUM_LIMBS] = [39, 100, 126, 205];
    let (res, res_mul, carry, x_ext, y_ext) =
        run_mulh::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(MulHOpcode::MULHU, &x, &y);
    for i in 0..RV32_REGISTER_NUM_LIMBS {
        assert_eq!(z[i], res[i]);
        assert_eq!(z_mul[i], res_mul[i]);
        assert_eq!(c[i], carry[i + RV32_REGISTER_NUM_LIMBS]);
        assert_eq!(c_mul[i], carry[i]);
    }
    assert_eq!(x_ext, 0);
    assert_eq!(y_ext, 0);
}

#[test]
fn run_mulhsu_pos_sanity_test() {
    let x: [u32; RV32_REGISTER_NUM_LIMBS] = [197, 85, 150, 32];
    let y: [u32; RV32_REGISTER_NUM_LIMBS] = [51, 109, 78, 142];
    let z: [u32; RV32_REGISTER_NUM_LIMBS] = [71, 95, 29, 18];
    let z_mul: [u32; RV32_REGISTER_NUM_LIMBS] = [63, 247, 125, 232];
    let c: [u32; RV32_REGISTER_NUM_LIMBS] = [107, 93, 18, 0];
    let c_mul: [u32; RV32_REGISTER_NUM_LIMBS] = [39, 100, 126, 205];
    let (res, res_mul, carry, x_ext, y_ext) =
        run_mulh::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(MulHOpcode::MULHSU, &x, &y);
    for i in 0..RV32_REGISTER_NUM_LIMBS {
        assert_eq!(z[i], res[i]);
        assert_eq!(z_mul[i], res_mul[i]);
        assert_eq!(c[i], carry[i + RV32_REGISTER_NUM_LIMBS]);
        assert_eq!(c_mul[i], carry[i]);
    }
    assert_eq!(x_ext, 0);
    assert_eq!(y_ext, 0);
}

#[test]
fn run_mulhsu_neg_sanity_test() {
    let x: [u32; RV32_REGISTER_NUM_LIMBS] = [197, 85, 150, 160];
    let y: [u32; RV32_REGISTER_NUM_LIMBS] = [51, 109, 78, 142];
    let z: [u32; RV32_REGISTER_NUM_LIMBS] = [174, 40, 246, 202];
    let z_mul: [u32; RV32_REGISTER_NUM_LIMBS] = [63, 247, 125, 104];
    let c: [u32; RV32_REGISTER_NUM_LIMBS] = [212, 292, 326, 379];
    let c_mul: [u32; RV32_REGISTER_NUM_LIMBS] = [39, 100, 126, 231];
    let (res, res_mul, carry, x_ext, y_ext) =
        run_mulh::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(MulHOpcode::MULHSU, &x, &y);
    for i in 0..RV32_REGISTER_NUM_LIMBS {
        assert_eq!(z[i], res[i]);
        assert_eq!(z_mul[i], res_mul[i]);
        assert_eq!(c[i], carry[i + RV32_REGISTER_NUM_LIMBS]);
        assert_eq!(c_mul[i], carry[i]);
    }
    assert_eq!(x_ext, 255);
    assert_eq!(y_ext, 0);
}
