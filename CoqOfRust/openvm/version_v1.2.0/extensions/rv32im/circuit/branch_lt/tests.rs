use std::borrow::BorrowMut;

use openvm_circuit::{
    arch::{
        testing::{memory::gen_pointer, TestAdapterChip, VmChipTestBuilder, BITWISE_OP_LOOKUP_BUS},
        BasicAdapterInterface, ExecutionBridge, ImmInstruction, InstructionExecutor, VmAdapterChip,
        VmChipWrapper, VmCoreChip,
    },
    utils::{generate_long_number, i32_to_f},
};
use openvm_circuit_primitives::bitwise_op_lookup::{
    BitwiseOperationLookupBus, SharedBitwiseOperationLookupChip,
};
use openvm_instructions::{instruction::Instruction, program::PC_BITS, LocalOpcode};
use openvm_rv32im_transpiler::BranchLessThanOpcode;
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
    core::{run_cmp, BranchLessThanCoreChip},
    Rv32BranchLessThanChip,
};
use crate::{
    adapters::{
        Rv32BranchAdapterChip, RV32_CELL_BITS, RV32_REGISTER_NUM_LIMBS, RV_B_TYPE_IMM_BITS,
    },
    branch_lt::BranchLessThanCoreCols,
};

type F = BabyBear;

//////////////////////////////////////////////////////////////////////////////////////
// POSITIVE TESTS
//
// Randomly generate computations and execute, ensuring that the generated trace
// passes all constraints.
//////////////////////////////////////////////////////////////////////////////////////

#[allow(clippy::too_many_arguments)]
fn run_rv32_branch_lt_rand_execute<E: InstructionExecutor<F>>(
    tester: &mut VmChipTestBuilder<F>,
    chip: &mut E,
    opcode: BranchLessThanOpcode,
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

    let (cmp_result, _, _, _) = run_cmp::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(opcode, &a, &b);
    let from_pc = tester.execution.last_from_pc().as_canonical_u32() as i32;
    let to_pc = tester.execution.last_to_pc().as_canonical_u32() as i32;
    let pc_inc = if cmp_result { imm } else { 4 };

    assert_eq!(to_pc, from_pc + pc_inc);
}

fn run_rv32_branch_lt_rand_test(opcode: BranchLessThanOpcode, num_ops: usize) {
    let mut rng = create_seeded_rng();
    const ABS_MAX_BRANCH: i32 = 1 << (RV_B_TYPE_IMM_BITS - 1);

    let bitwise_bus = BitwiseOperationLookupBus::new(BITWISE_OP_LOOKUP_BUS);
    let bitwise_chip = SharedBitwiseOperationLookupChip::<RV32_CELL_BITS>::new(bitwise_bus);

    let mut tester = VmChipTestBuilder::default();
    let mut chip = Rv32BranchLessThanChip::<F>::new(
        Rv32BranchAdapterChip::new(
            tester.execution_bus(),
            tester.program_bus(),
            tester.memory_bridge(),
        ),
        BranchLessThanCoreChip::new(bitwise_chip.clone(), BranchLessThanOpcode::CLASS_OFFSET),
        tester.offline_memory_mutex_arc(),
    );

    for _ in 0..num_ops {
        let a = generate_long_number::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(&mut rng);
        let b = if rng.gen_bool(0.5) {
            a
        } else {
            generate_long_number::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(&mut rng)
        };
        let imm = rng.gen_range((-ABS_MAX_BRANCH)..ABS_MAX_BRANCH);
        run_rv32_branch_lt_rand_execute(&mut tester, &mut chip, opcode, a, b, imm, &mut rng);
    }

    // Test special case where b = c
    run_rv32_branch_lt_rand_execute(
        &mut tester,
        &mut chip,
        opcode,
        [101, 128, 202, 255],
        [101, 128, 202, 255],
        24,
        &mut rng,
    );
    run_rv32_branch_lt_rand_execute(
        &mut tester,
        &mut chip,
        opcode,
        [36, 0, 0, 0],
        [36, 0, 0, 0],
        24,
        &mut rng,
    );

    let tester = tester.build().load(chip).load(bitwise_chip).finalize();
    tester.simple_test().expect("Verification failed");
}

#[test]
fn rv32_blt_rand_test() {
    run_rv32_branch_lt_rand_test(BranchLessThanOpcode::BLT, 10);
}

#[test]
fn rv32_bltu_rand_test() {
    run_rv32_branch_lt_rand_test(BranchLessThanOpcode::BLTU, 12);
}

#[test]
fn rv32_bge_rand_test() {
    run_rv32_branch_lt_rand_test(BranchLessThanOpcode::BGE, 12);
}

#[test]
fn rv32_bgeu_rand_test() {
    run_rv32_branch_lt_rand_test(BranchLessThanOpcode::BGEU, 12);
}

//////////////////////////////////////////////////////////////////////////////////////
// NEGATIVE TESTS
//
// Given a fake trace of a single operation, setup a chip and run the test. We replace
// the write part of the trace and check that the core chip throws the expected error.
// A dummy adapter is used so memory interactions don't indirectly cause false passes.
//////////////////////////////////////////////////////////////////////////////////////

type Rv32BranchLessThanTestChip<F> = VmChipWrapper<
    F,
    TestAdapterChip<F>,
    BranchLessThanCoreChip<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>,
>;

#[derive(Clone, Copy, Default, PartialEq)]
struct BranchLessThanPrankValues<const NUM_LIMBS: usize> {
    pub a_msb: Option<i32>,
    pub b_msb: Option<i32>,
    pub diff_marker: Option<[u32; NUM_LIMBS]>,
    pub diff_val: Option<u32>,
}

#[allow(clippy::too_many_arguments)]
fn run_rv32_blt_negative_test(
    opcode: BranchLessThanOpcode,
    a: [u32; RV32_REGISTER_NUM_LIMBS],
    b: [u32; RV32_REGISTER_NUM_LIMBS],
    cmp_result: bool,
    prank_vals: BranchLessThanPrankValues<RV32_REGISTER_NUM_LIMBS>,
    interaction_error: bool,
) {
    let imm = 16u32;
    let bitwise_bus = BitwiseOperationLookupBus::new(BITWISE_OP_LOOKUP_BUS);
    let bitwise_chip = SharedBitwiseOperationLookupChip::<RV32_CELL_BITS>::new(bitwise_bus);

    let mut tester: VmChipTestBuilder<BabyBear> = VmChipTestBuilder::default();
    let mut chip = Rv32BranchLessThanTestChip::<F>::new(
        TestAdapterChip::new(
            vec![[a.map(F::from_canonical_u32), b.map(F::from_canonical_u32)].concat()],
            vec![if cmp_result { Some(imm) } else { None }],
            ExecutionBridge::new(tester.execution_bus(), tester.program_bus()),
        ),
        BranchLessThanCoreChip::new(bitwise_chip.clone(), BranchLessThanOpcode::CLASS_OFFSET),
        tester.offline_memory_mutex_arc(),
    );

    tester.execute(
        &mut chip,
        &Instruction::from_usize(opcode.global_opcode(), [0, 0, imm as usize, 1, 1]),
    );

    let trace_width = chip.trace_width();
    let adapter_width = BaseAir::<F>::width(chip.adapter.air());
    let ge_opcode = opcode == BranchLessThanOpcode::BGE || opcode == BranchLessThanOpcode::BGEU;
    let (_, _, a_sign, b_sign) = run_cmp::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(opcode, &a, &b);

    if prank_vals != BranchLessThanPrankValues::default() {
        debug_assert!(prank_vals.diff_val.is_some());
        let a_msb = prank_vals.a_msb.unwrap_or(
            a[RV32_REGISTER_NUM_LIMBS - 1] as i32 - if a_sign { 1 << RV32_CELL_BITS } else { 0 },
        );
        let b_msb = prank_vals.b_msb.unwrap_or(
            b[RV32_REGISTER_NUM_LIMBS - 1] as i32 - if b_sign { 1 << RV32_CELL_BITS } else { 0 },
        );
        let signed_offset = match opcode {
            BranchLessThanOpcode::BLT | BranchLessThanOpcode::BGE => 1 << (RV32_CELL_BITS - 1),
            _ => 0,
        };

        bitwise_chip.clear();
        bitwise_chip.request_range(
            (a_msb + signed_offset) as u8 as u32,
            (b_msb + signed_offset) as u8 as u32,
        );

        let diff_val = prank_vals
            .diff_val
            .unwrap()
            .clamp(0, (1 << RV32_CELL_BITS) - 1);
        if diff_val > 0 {
            bitwise_chip.request_range(diff_val - 1, 0);
        }
    }

    let modify_trace = |trace: &mut DenseMatrix<BabyBear>| {
        let mut values = trace.row_slice(0).to_vec();
        let cols: &mut BranchLessThanCoreCols<F, RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS> =
            values.split_at_mut(adapter_width).1.borrow_mut();

        if let Some(a_msb) = prank_vals.a_msb {
            cols.a_msb_f = i32_to_f(a_msb);
        }
        if let Some(b_msb) = prank_vals.b_msb {
            cols.b_msb_f = i32_to_f(b_msb);
        }
        if let Some(diff_marker) = prank_vals.diff_marker {
            cols.diff_marker = diff_marker.map(F::from_canonical_u32);
        }
        if let Some(diff_val) = prank_vals.diff_val {
            cols.diff_val = F::from_canonical_u32(diff_val);
        }
        cols.cmp_result = F::from_bool(cmp_result);
        cols.cmp_lt = F::from_bool(ge_opcode ^ cmp_result);

        *trace = RowMajorMatrix::new(values, trace_width);
    };

    disable_debug_builder();
    let tester = tester
        .build()
        .load_and_prank_trace(chip, modify_trace)
        .load(bitwise_chip)
        .finalize();
    tester.simple_test_with_expected_error(if interaction_error {
        VerificationError::ChallengePhaseError
    } else {
        VerificationError::OodEvaluationMismatch
    });
}

#[test]
fn rv32_blt_wrong_lt_cmp_negative_test() {
    let a = [145, 34, 25, 205];
    let b = [73, 35, 25, 205];
    let prank_vals = Default::default();
    run_rv32_blt_negative_test(BranchLessThanOpcode::BLT, a, b, false, prank_vals, false);
    run_rv32_blt_negative_test(BranchLessThanOpcode::BLTU, a, b, false, prank_vals, false);
    run_rv32_blt_negative_test(BranchLessThanOpcode::BGE, a, b, true, prank_vals, false);
    run_rv32_blt_negative_test(BranchLessThanOpcode::BGEU, a, b, true, prank_vals, false);
}

#[test]
fn rv32_blt_wrong_ge_cmp_negative_test() {
    let a = [73, 35, 25, 205];
    let b = [145, 34, 25, 205];
    let prank_vals = Default::default();
    run_rv32_blt_negative_test(BranchLessThanOpcode::BLT, a, b, true, prank_vals, false);
    run_rv32_blt_negative_test(BranchLessThanOpcode::BLTU, a, b, true, prank_vals, false);
    run_rv32_blt_negative_test(BranchLessThanOpcode::BGE, a, b, false, prank_vals, false);
    run_rv32_blt_negative_test(BranchLessThanOpcode::BGEU, a, b, false, prank_vals, false);
}

#[test]
fn rv32_blt_wrong_eq_cmp_negative_test() {
    let a = [73, 35, 25, 205];
    let b = [73, 35, 25, 205];
    let prank_vals = Default::default();
    run_rv32_blt_negative_test(BranchLessThanOpcode::BLT, a, b, true, prank_vals, false);
    run_rv32_blt_negative_test(BranchLessThanOpcode::BLTU, a, b, true, prank_vals, false);
    run_rv32_blt_negative_test(BranchLessThanOpcode::BGE, a, b, false, prank_vals, false);
    run_rv32_blt_negative_test(BranchLessThanOpcode::BGEU, a, b, false, prank_vals, false);
}

#[test]
fn rv32_blt_fake_diff_val_negative_test() {
    let a = [145, 34, 25, 205];
    let b = [73, 35, 25, 205];
    let prank_vals = BranchLessThanPrankValues {
        diff_val: Some(F::NEG_ONE.as_canonical_u32()),
        ..Default::default()
    };
    run_rv32_blt_negative_test(BranchLessThanOpcode::BLT, a, b, false, prank_vals, true);
    run_rv32_blt_negative_test(BranchLessThanOpcode::BLTU, a, b, false, prank_vals, true);
    run_rv32_blt_negative_test(BranchLessThanOpcode::BGE, a, b, true, prank_vals, true);
    run_rv32_blt_negative_test(BranchLessThanOpcode::BGEU, a, b, true, prank_vals, true);
}

#[test]
fn rv32_blt_zero_diff_val_negative_test() {
    let a = [145, 34, 25, 205];
    let b = [73, 35, 25, 205];
    let prank_vals = BranchLessThanPrankValues {
        diff_marker: Some([0, 0, 1, 0]),
        diff_val: Some(0),
        ..Default::default()
    };
    run_rv32_blt_negative_test(BranchLessThanOpcode::BLT, a, b, false, prank_vals, true);
    run_rv32_blt_negative_test(BranchLessThanOpcode::BLTU, a, b, false, prank_vals, true);
    run_rv32_blt_negative_test(BranchLessThanOpcode::BGE, a, b, true, prank_vals, true);
    run_rv32_blt_negative_test(BranchLessThanOpcode::BGEU, a, b, true, prank_vals, true);
}

#[test]
fn rv32_blt_fake_diff_marker_negative_test() {
    let a = [145, 34, 25, 205];
    let b = [73, 35, 25, 205];
    let prank_vals = BranchLessThanPrankValues {
        diff_marker: Some([1, 0, 0, 0]),
        diff_val: Some(72),
        ..Default::default()
    };
    run_rv32_blt_negative_test(BranchLessThanOpcode::BLT, a, b, false, prank_vals, false);
    run_rv32_blt_negative_test(BranchLessThanOpcode::BLTU, a, b, false, prank_vals, false);
    run_rv32_blt_negative_test(BranchLessThanOpcode::BGE, a, b, true, prank_vals, false);
    run_rv32_blt_negative_test(BranchLessThanOpcode::BGEU, a, b, true, prank_vals, false);
}

#[test]
fn rv32_blt_zero_diff_marker_negative_test() {
    let a = [145, 34, 25, 205];
    let b = [73, 35, 25, 205];
    let prank_vals = BranchLessThanPrankValues {
        diff_marker: Some([0, 0, 0, 0]),
        diff_val: Some(0),
        ..Default::default()
    };
    run_rv32_blt_negative_test(BranchLessThanOpcode::BLT, a, b, false, prank_vals, false);
    run_rv32_blt_negative_test(BranchLessThanOpcode::BLTU, a, b, false, prank_vals, false);
    run_rv32_blt_negative_test(BranchLessThanOpcode::BGE, a, b, true, prank_vals, false);
    run_rv32_blt_negative_test(BranchLessThanOpcode::BGEU, a, b, true, prank_vals, false);
}

#[test]
fn rv32_blt_signed_wrong_a_msb_negative_test() {
    let a = [145, 34, 25, 205];
    let b = [73, 35, 25, 205];
    let prank_vals = BranchLessThanPrankValues {
        a_msb: Some(206),
        diff_marker: Some([0, 0, 0, 1]),
        diff_val: Some(1),
        ..Default::default()
    };
    run_rv32_blt_negative_test(BranchLessThanOpcode::BLT, a, b, false, prank_vals, false);
    run_rv32_blt_negative_test(BranchLessThanOpcode::BGE, a, b, true, prank_vals, false);
}

#[test]
fn rv32_blt_signed_wrong_a_msb_sign_negative_test() {
    let a = [145, 34, 25, 205];
    let b = [73, 35, 25, 205];
    let prank_vals = BranchLessThanPrankValues {
        a_msb: Some(205),
        diff_marker: Some([0, 0, 0, 1]),
        diff_val: Some(256),
        ..Default::default()
    };
    run_rv32_blt_negative_test(BranchLessThanOpcode::BLT, a, b, false, prank_vals, true);
    run_rv32_blt_negative_test(BranchLessThanOpcode::BGE, a, b, true, prank_vals, true);
}

#[test]
fn rv32_blt_signed_wrong_b_msb_negative_test() {
    let a = [145, 36, 25, 205];
    let b = [73, 35, 25, 205];
    let prank_vals = BranchLessThanPrankValues {
        b_msb: Some(206),
        diff_marker: Some([0, 0, 0, 1]),
        diff_val: Some(1),
        ..Default::default()
    };
    run_rv32_blt_negative_test(BranchLessThanOpcode::BLT, a, b, true, prank_vals, false);
    run_rv32_blt_negative_test(BranchLessThanOpcode::BGE, a, b, false, prank_vals, false);
}

#[test]
fn rv32_blt_signed_wrong_b_msb_sign_negative_test() {
    let a = [145, 36, 25, 205];
    let b = [73, 35, 25, 205];
    let prank_vals = BranchLessThanPrankValues {
        b_msb: Some(205),
        diff_marker: Some([0, 0, 0, 1]),
        diff_val: Some(256),
        ..Default::default()
    };
    run_rv32_blt_negative_test(BranchLessThanOpcode::BLT, a, b, true, prank_vals, true);
    run_rv32_blt_negative_test(BranchLessThanOpcode::BGE, a, b, false, prank_vals, true);
}

#[test]
fn rv32_blt_unsigned_wrong_a_msb_negative_test() {
    let a = [145, 36, 25, 205];
    let b = [73, 35, 25, 205];
    let prank_vals = BranchLessThanPrankValues {
        a_msb: Some(204),
        diff_marker: Some([0, 0, 0, 1]),
        diff_val: Some(1),
        ..Default::default()
    };
    run_rv32_blt_negative_test(BranchLessThanOpcode::BLTU, a, b, true, prank_vals, false);
    run_rv32_blt_negative_test(BranchLessThanOpcode::BGEU, a, b, false, prank_vals, false);
}

#[test]
fn rv32_blt_unsigned_wrong_a_msb_sign_negative_test() {
    let a = [145, 36, 25, 205];
    let b = [73, 35, 25, 205];
    let prank_vals = BranchLessThanPrankValues {
        a_msb: Some(-51),
        diff_marker: Some([0, 0, 0, 1]),
        diff_val: Some(256),
        ..Default::default()
    };
    run_rv32_blt_negative_test(BranchLessThanOpcode::BLTU, a, b, true, prank_vals, true);
    run_rv32_blt_negative_test(BranchLessThanOpcode::BGEU, a, b, false, prank_vals, true);
}

#[test]
fn rv32_blt_unsigned_wrong_b_msb_negative_test() {
    let a = [145, 34, 25, 205];
    let b = [73, 35, 25, 205];
    let prank_vals = BranchLessThanPrankValues {
        b_msb: Some(206),
        diff_marker: Some([0, 0, 0, 1]),
        diff_val: Some(1),
        ..Default::default()
    };
    run_rv32_blt_negative_test(BranchLessThanOpcode::BLTU, a, b, false, prank_vals, false);
    run_rv32_blt_negative_test(BranchLessThanOpcode::BGEU, a, b, true, prank_vals, false);
}

#[test]
fn rv32_blt_unsigned_wrong_b_msb_sign_negative_test() {
    let a = [145, 34, 25, 205];
    let b = [73, 35, 25, 205];
    let prank_vals = BranchLessThanPrankValues {
        b_msb: Some(-51),
        diff_marker: Some([0, 0, 0, 1]),
        diff_val: Some(256),
        ..Default::default()
    };
    run_rv32_blt_negative_test(BranchLessThanOpcode::BLTU, a, b, false, prank_vals, true);
    run_rv32_blt_negative_test(BranchLessThanOpcode::BGEU, a, b, true, prank_vals, true);
}

///////////////////////////////////////////////////////////////////////////////////////
/// SANITY TESTS
///
/// Ensure that solve functions produce the correct results.
///////////////////////////////////////////////////////////////////////////////////////

#[test]
fn execute_pc_increment_sanity_test() {
    let bitwise_bus = BitwiseOperationLookupBus::new(BITWISE_OP_LOOKUP_BUS);
    let bitwise_chip = SharedBitwiseOperationLookupChip::<RV32_CELL_BITS>::new(bitwise_bus);
    let core = BranchLessThanCoreChip::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>::new(
        bitwise_chip,
        BranchLessThanOpcode::CLASS_OFFSET,
    );

    let mut instruction = Instruction::<F> {
        opcode: BranchLessThanOpcode::BLT.global_opcode(),
        c: F::from_canonical_u8(8),
        ..Default::default()
    };
    let x: [F; RV32_REGISTER_NUM_LIMBS] = [145, 34, 25, 205].map(F::from_canonical_u32);

    let result = <BranchLessThanCoreChip<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS> as VmCoreChip<
        F,
        BasicAdapterInterface<F, ImmInstruction<F>, 2, 0, RV32_REGISTER_NUM_LIMBS, 0>,
    >>::execute_instruction(&core, &instruction, 0, [x, x]);
    let (output, _) = result.expect("execute_instruction failed");
    assert!(output.to_pc.is_none());

    instruction.opcode = BranchLessThanOpcode::BGE.global_opcode();
    let result = <BranchLessThanCoreChip<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS> as VmCoreChip<
        F,
        BasicAdapterInterface<F, ImmInstruction<F>, 2, 0, RV32_REGISTER_NUM_LIMBS, 0>,
    >>::execute_instruction(&core, &instruction, 0, [x, x]);
    let (output, _) = result.expect("execute_instruction failed");
    assert!(output.to_pc.is_some());
    assert_eq!(output.to_pc.unwrap(), 8);
}

#[test]
fn run_cmp_unsigned_sanity_test() {
    let x: [u32; RV32_REGISTER_NUM_LIMBS] = [145, 34, 25, 205];
    let y: [u32; RV32_REGISTER_NUM_LIMBS] = [73, 35, 25, 205];
    let (cmp_result, diff_idx, x_sign, y_sign) =
        run_cmp::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(BranchLessThanOpcode::BLTU, &x, &y);
    assert!(cmp_result);
    assert_eq!(diff_idx, 1);
    assert!(!x_sign); // unsigned
    assert!(!y_sign); // unsigned

    let (cmp_result, diff_idx, x_sign, y_sign) =
        run_cmp::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(BranchLessThanOpcode::BGEU, &x, &y);
    assert!(!cmp_result);
    assert_eq!(diff_idx, 1);
    assert!(!x_sign); // unsigned
    assert!(!y_sign); // unsigned
}

#[test]
fn run_cmp_same_sign_sanity_test() {
    let x: [u32; RV32_REGISTER_NUM_LIMBS] = [145, 34, 25, 205];
    let y: [u32; RV32_REGISTER_NUM_LIMBS] = [73, 35, 25, 205];
    let (cmp_result, diff_idx, x_sign, y_sign) =
        run_cmp::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(BranchLessThanOpcode::BLT, &x, &y);
    assert!(cmp_result);
    assert_eq!(diff_idx, 1);
    assert!(x_sign); // negative
    assert!(y_sign); // negative

    let (cmp_result, diff_idx, x_sign, y_sign) =
        run_cmp::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(BranchLessThanOpcode::BGE, &x, &y);
    assert!(!cmp_result);
    assert_eq!(diff_idx, 1);
    assert!(x_sign); // negative
    assert!(y_sign); // negative
}

#[test]
fn run_cmp_diff_sign_sanity_test() {
    let x: [u32; RV32_REGISTER_NUM_LIMBS] = [45, 35, 25, 55];
    let y: [u32; RV32_REGISTER_NUM_LIMBS] = [173, 34, 25, 205];
    let (cmp_result, diff_idx, x_sign, y_sign) =
        run_cmp::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(BranchLessThanOpcode::BLT, &x, &y);
    assert!(!cmp_result);
    assert_eq!(diff_idx, 3);
    assert!(!x_sign); // positive
    assert!(y_sign); // negative

    let (cmp_result, diff_idx, x_sign, y_sign) =
        run_cmp::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(BranchLessThanOpcode::BGE, &x, &y);
    assert!(cmp_result);
    assert_eq!(diff_idx, 3);
    assert!(!x_sign); // positive
    assert!(y_sign); // negative
}

#[test]
fn run_cmp_eq_sanity_test() {
    let x: [u32; RV32_REGISTER_NUM_LIMBS] = [45, 35, 25, 55];
    let (cmp_result, diff_idx, x_sign, y_sign) =
        run_cmp::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(BranchLessThanOpcode::BLT, &x, &x);
    assert!(!cmp_result);
    assert_eq!(diff_idx, RV32_REGISTER_NUM_LIMBS);
    assert_eq!(x_sign, y_sign);

    let (cmp_result, diff_idx, x_sign, y_sign) =
        run_cmp::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(BranchLessThanOpcode::BLTU, &x, &x);
    assert!(!cmp_result);
    assert_eq!(diff_idx, RV32_REGISTER_NUM_LIMBS);
    assert_eq!(x_sign, y_sign);

    let (cmp_result, diff_idx, x_sign, y_sign) =
        run_cmp::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(BranchLessThanOpcode::BGE, &x, &x);
    assert!(cmp_result);
    assert_eq!(diff_idx, RV32_REGISTER_NUM_LIMBS);
    assert_eq!(x_sign, y_sign);

    let (cmp_result, diff_idx, x_sign, y_sign) =
        run_cmp::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(BranchLessThanOpcode::BGEU, &x, &x);
    assert!(cmp_result);
    assert_eq!(diff_idx, RV32_REGISTER_NUM_LIMBS);
    assert_eq!(x_sign, y_sign);
}
