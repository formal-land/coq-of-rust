use std::{array, borrow::BorrowMut};

use openvm_circuit::arch::{
    testing::{memory::gen_pointer, TestAdapterChip, VmChipTestBuilder},
    BasicAdapterInterface, ExecutionBridge, ImmInstruction, InstructionExecutor, VmAdapterChip,
    VmChipWrapper, VmCoreChip,
};
use openvm_instructions::{instruction::Instruction, program::PC_BITS, LocalOpcode};
use openvm_rv32im_transpiler::BranchEqualOpcode;
use openvm_stark_backend::{
    p3_air::BaseAir,
    p3_field::{FieldAlgebra, PrimeField32},
    p3_matrix::{
        dense::{DenseMatrix, RowMajorMatrix},
        Matrix,
    },
    utils::disable_debug_builder,
    verifier::VerificationError,
    ChipUsageGetter,
};
use openvm_stark_sdk::{p3_baby_bear::BabyBear, utils::create_seeded_rng};
use rand::{rngs::StdRng, Rng};

use super::{
    core::{run_eq, BranchEqualCoreChip},
    BranchEqualCoreCols, Rv32BranchEqualChip,
};
use crate::adapters::{Rv32BranchAdapterChip, RV32_REGISTER_NUM_LIMBS, RV_B_TYPE_IMM_BITS};

type F = BabyBear;

//////////////////////////////////////////////////////////////////////////////////////
// POSITIVE TESTS
//
// Randomly generate computations and execute, ensuring that the generated trace
// passes all constraints.
//////////////////////////////////////////////////////////////////////////////////////

#[allow(clippy::too_many_arguments)]
fn run_rv32_branch_eq_rand_execute<E: InstructionExecutor<F>>(
    tester: &mut VmChipTestBuilder<F>,
    chip: &mut E,
    opcode: BranchEqualOpcode,
    a: [u32; RV32_REGISTER_NUM_LIMBS],
    b: [u32; RV32_REGISTER_NUM_LIMBS],
    imm: i32,
    rng: &mut StdRng,
) {
    let rs1 = gen_pointer(rng, 4);
    let rs2 = gen_pointer(rng, 4);
    tester.write::<RV32_REGISTER_NUM_LIMBS>(1, rs1, a.map(F::from_canonical_u32));
    tester.write::<RV32_REGISTER_NUM_LIMBS>(1, rs2, b.map(F::from_canonical_u32));

    tester.execute_with_pc(
        chip,
        &Instruction::from_isize(
            opcode.global_opcode(),
            rs1 as isize,
            rs2 as isize,
            imm as isize,
            1,
            1,
        ),
        rng.gen_range(imm.unsigned_abs()..(1 << (PC_BITS - 1))),
    );

    let (cmp_result, _, _) = run_eq::<F, RV32_REGISTER_NUM_LIMBS>(opcode, &a, &b);
    let from_pc = tester.execution.last_from_pc().as_canonical_u32() as i32;
    let to_pc = tester.execution.last_to_pc().as_canonical_u32() as i32;
    let pc_inc = if cmp_result { imm } else { 4 };

    assert_eq!(to_pc, from_pc + pc_inc);
}

fn run_rv32_branch_eq_rand_test(opcode: BranchEqualOpcode, num_ops: usize) {
    let mut rng = create_seeded_rng();
    const ABS_MAX_BRANCH: i32 = 1 << (RV_B_TYPE_IMM_BITS - 1);

    let mut tester = VmChipTestBuilder::default();
    let mut chip = Rv32BranchEqualChip::<F>::new(
        Rv32BranchAdapterChip::new(
            tester.execution_bus(),
            tester.program_bus(),
            tester.memory_bridge(),
        ),
        BranchEqualCoreChip::new(BranchEqualOpcode::CLASS_OFFSET, 4),
        tester.offline_memory_mutex_arc(),
    );

    for _ in 0..num_ops {
        let a = array::from_fn(|_| rng.gen_range(0..F::ORDER_U32));
        let b = if rng.gen_bool(0.5) {
            a
        } else {
            array::from_fn(|_| rng.gen_range(0..F::ORDER_U32))
        };
        let imm = rng.gen_range((-ABS_MAX_BRANCH)..ABS_MAX_BRANCH);
        run_rv32_branch_eq_rand_execute(&mut tester, &mut chip, opcode, a, b, imm, &mut rng);
    }

    let tester = tester.build().load(chip).finalize();
    tester.simple_test().expect("Verification failed");
}

#[test]
fn rv32_beq_rand_test() {
    run_rv32_branch_eq_rand_test(BranchEqualOpcode::BEQ, 100);
}

#[test]
fn rv32_bne_rand_test() {
    run_rv32_branch_eq_rand_test(BranchEqualOpcode::BNE, 100);
}

//////////////////////////////////////////////////////////////////////////////////////
// NEGATIVE TESTS
//
// Given a fake trace of a single operation, setup a chip and run the test. We replace
// the write part of the trace and check that the core chip throws the expected error.
// A dummy adapter is used so memory interactions don't indirectly cause false passes.
//////////////////////////////////////////////////////////////////////////////////////

type Rv32BranchEqualTestChip<F> =
    VmChipWrapper<F, TestAdapterChip<F>, BranchEqualCoreChip<RV32_REGISTER_NUM_LIMBS>>;

#[allow(clippy::too_many_arguments)]
fn run_rv32_beq_negative_test(
    opcode: BranchEqualOpcode,
    a: [u32; RV32_REGISTER_NUM_LIMBS],
    b: [u32; RV32_REGISTER_NUM_LIMBS],
    cmp_result: bool,
    diff_inv_marker: Option<[u32; RV32_REGISTER_NUM_LIMBS]>,
) {
    let imm = 16u32;
    let mut tester = VmChipTestBuilder::default();
    let mut chip = Rv32BranchEqualTestChip::<F>::new(
        TestAdapterChip::new(
            vec![[a.map(F::from_canonical_u32), b.map(F::from_canonical_u32)].concat()],
            vec![if cmp_result { Some(imm) } else { None }],
            ExecutionBridge::new(tester.execution_bus(), tester.program_bus()),
        ),
        BranchEqualCoreChip::new(BranchEqualOpcode::CLASS_OFFSET, 4),
        tester.offline_memory_mutex_arc(),
    );

    tester.execute(
        &mut chip,
        &Instruction::from_usize(opcode.global_opcode(), [0, 0, imm as usize, 1, 1]),
    );

    let trace_width = chip.trace_width();
    let adapter_width = BaseAir::<F>::width(chip.adapter.air());

    let modify_trace = |trace: &mut DenseMatrix<BabyBear>| {
        let mut values = trace.row_slice(0).to_vec();
        let cols: &mut BranchEqualCoreCols<F, RV32_REGISTER_NUM_LIMBS> =
            values.split_at_mut(adapter_width).1.borrow_mut();
        cols.cmp_result = F::from_bool(cmp_result);
        if let Some(diff_inv_marker) = diff_inv_marker {
            cols.diff_inv_marker = diff_inv_marker.map(F::from_canonical_u32);
        }
        *trace = RowMajorMatrix::new(values, trace_width);
    };

    disable_debug_builder();
    let tester = tester
        .build()
        .load_and_prank_trace(chip, modify_trace)
        .finalize();
    tester.simple_test_with_expected_error(VerificationError::OodEvaluationMismatch);
}

#[test]
fn rv32_beq_wrong_cmp_negative_test() {
    run_rv32_beq_negative_test(
        BranchEqualOpcode::BEQ,
        [0, 0, 7, 0],
        [0, 0, 0, 7],
        true,
        None,
    );

    run_rv32_beq_negative_test(
        BranchEqualOpcode::BEQ,
        [0, 0, 7, 0],
        [0, 0, 7, 0],
        false,
        None,
    );
}

#[test]
fn rv32_beq_zero_inv_marker_negative_test() {
    run_rv32_beq_negative_test(
        BranchEqualOpcode::BEQ,
        [0, 0, 7, 0],
        [0, 0, 0, 7],
        true,
        Some([0, 0, 0, 0]),
    );
}

#[test]
fn rv32_beq_invalid_inv_marker_negative_test() {
    run_rv32_beq_negative_test(
        BranchEqualOpcode::BEQ,
        [0, 0, 7, 0],
        [0, 0, 7, 0],
        false,
        Some([0, 0, 1, 0]),
    );
}

#[test]
fn rv32_bne_wrong_cmp_negative_test() {
    run_rv32_beq_negative_test(
        BranchEqualOpcode::BNE,
        [0, 0, 7, 0],
        [0, 0, 0, 7],
        false,
        None,
    );

    run_rv32_beq_negative_test(
        BranchEqualOpcode::BNE,
        [0, 0, 7, 0],
        [0, 0, 7, 0],
        true,
        None,
    );
}

#[test]
fn rv32_bne_zero_inv_marker_negative_test() {
    run_rv32_beq_negative_test(
        BranchEqualOpcode::BNE,
        [0, 0, 7, 0],
        [0, 0, 0, 7],
        false,
        Some([0, 0, 0, 0]),
    );
}

#[test]
fn rv32_bne_invalid_inv_marker_negative_test() {
    run_rv32_beq_negative_test(
        BranchEqualOpcode::BNE,
        [0, 0, 7, 0],
        [0, 0, 7, 0],
        true,
        Some([0, 0, 1, 0]),
    );
}

///////////////////////////////////////////////////////////////////////////////////////
/// SANITY TESTS
///
/// Ensure that solve functions produce the correct results.
///////////////////////////////////////////////////////////////////////////////////////

#[test]
fn execute_pc_increment_sanity_test() {
    let core =
        BranchEqualCoreChip::<RV32_REGISTER_NUM_LIMBS>::new(BranchEqualOpcode::CLASS_OFFSET, 4);

    let mut instruction = Instruction::<F> {
        opcode: BranchEqualOpcode::BEQ.global_opcode(),
        c: F::from_canonical_u8(8),
        ..Default::default()
    };
    let x: [F; RV32_REGISTER_NUM_LIMBS] = [19, 4, 1790, 60].map(F::from_canonical_u32);
    let y: [F; RV32_REGISTER_NUM_LIMBS] = [19, 32, 1804, 60].map(F::from_canonical_u32);

    let result = <BranchEqualCoreChip<RV32_REGISTER_NUM_LIMBS> as VmCoreChip<
        F,
        BasicAdapterInterface<F, ImmInstruction<F>, 2, 0, RV32_REGISTER_NUM_LIMBS, 0>,
    >>::execute_instruction(&core, &instruction, 0, [x, y]);
    let (output, _) = result.expect("execute_instruction failed");
    assert!(output.to_pc.is_none());

    instruction.opcode = BranchEqualOpcode::BNE.global_opcode();
    let result = <BranchEqualCoreChip<RV32_REGISTER_NUM_LIMBS> as VmCoreChip<
        F,
        BasicAdapterInterface<F, ImmInstruction<F>, 2, 0, RV32_REGISTER_NUM_LIMBS, 0>,
    >>::execute_instruction(&core, &instruction, 0, [x, y]);
    let (output, _) = result.expect("execute_instruction failed");
    assert!(output.to_pc.is_some());
    assert_eq!(output.to_pc.unwrap(), 8);
}

#[test]
fn run_eq_sanity_test() {
    let x: [u32; RV32_REGISTER_NUM_LIMBS] = [19, 4, 1790, 60];
    let (cmp_result, _, diff_val) =
        run_eq::<F, RV32_REGISTER_NUM_LIMBS>(BranchEqualOpcode::BEQ, &x, &x);
    assert!(cmp_result);
    assert_eq!(diff_val, F::ZERO);

    let (cmp_result, _, diff_val) =
        run_eq::<F, RV32_REGISTER_NUM_LIMBS>(BranchEqualOpcode::BNE, &x, &x);
    assert!(!cmp_result);
    assert_eq!(diff_val, F::ZERO);
}

#[test]
fn run_ne_sanity_test() {
    let x: [u32; RV32_REGISTER_NUM_LIMBS] = [19, 4, 1790, 60];
    let y: [u32; RV32_REGISTER_NUM_LIMBS] = [19, 32, 1804, 60];
    let (cmp_result, diff_idx, diff_val) =
        run_eq::<F, RV32_REGISTER_NUM_LIMBS>(BranchEqualOpcode::BEQ, &x, &y);
    assert!(!cmp_result);
    assert_eq!(
        diff_val * (F::from_canonical_u32(x[diff_idx]) - F::from_canonical_u32(y[diff_idx])),
        F::ONE
    );

    let (cmp_result, diff_idx, diff_val) =
        run_eq::<F, RV32_REGISTER_NUM_LIMBS>(BranchEqualOpcode::BNE, &x, &y);
    assert!(cmp_result);
    assert_eq!(
        diff_val * (F::from_canonical_u32(x[diff_idx]) - F::from_canonical_u32(y[diff_idx])),
        F::ONE
    );
}
