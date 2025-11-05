use std::{array, borrow::BorrowMut};

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
use openvm_rv32im_transpiler::DivRemOpcode;
use openvm_stark_backend::{
    p3_air::BaseAir,
    p3_field::{Field, FieldAlgebra},
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

use super::core::run_divrem;
use crate::{
    adapters::{Rv32MultAdapterChip, RV32_CELL_BITS, RV32_REGISTER_NUM_LIMBS},
    divrem::{
        run_mul_carries, run_sltu_diff_idx, DivRemCoreChip, DivRemCoreCols, DivRemCoreSpecialCase,
        Rv32DivRemChip,
    },
};

type F = BabyBear;

//////////////////////////////////////////////////////////////////////////////////////
// POSITIVE TESTS
//
// Randomly generate computations and execute, ensuring that the generated trace
// passes all constraints.
//////////////////////////////////////////////////////////////////////////////////////

fn limb_sra<const NUM_LIMBS: usize, const LIMB_BITS: usize>(
    x: [u32; NUM_LIMBS],
    shift: usize,
) -> [u32; NUM_LIMBS] {
    assert!(shift < NUM_LIMBS);
    let ext = (x[NUM_LIMBS - 1] >> (LIMB_BITS - 1)) * ((1 << LIMB_BITS) - 1);
    array::from_fn(|i| if i + shift < NUM_LIMBS { x[i] } else { ext })
}

#[allow(clippy::too_many_arguments)]
fn run_rv32_divrem_rand_write_execute<E: InstructionExecutor<F>>(
    opcode: DivRemOpcode,
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

    let is_div = opcode == DivRemOpcode::DIV || opcode == DivRemOpcode::DIVU;
    let is_signed = opcode == DivRemOpcode::DIV || opcode == DivRemOpcode::REM;

    let (q, r, _, _, _, _) =
        run_divrem::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(is_signed, &b, &c);
    tester.execute(
        chip,
        &Instruction::from_usize(opcode.global_opcode(), [rd, rs1, rs2, 1, 0]),
    );

    assert_eq!(
        (if is_div { q } else { r }).map(F::from_canonical_u32),
        tester.read::<RV32_REGISTER_NUM_LIMBS>(1, rd)
    );
}

fn run_rv32_divrem_rand_test(opcode: DivRemOpcode, num_ops: usize) {
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
    let mut chip = Rv32DivRemChip::<F>::new(
        Rv32MultAdapterChip::new(
            tester.execution_bus(),
            tester.program_bus(),
            tester.memory_bridge(),
        ),
        DivRemCoreChip::new(
            bitwise_chip.clone(),
            range_tuple_checker.clone(),
            DivRemOpcode::CLASS_OFFSET,
        ),
        tester.offline_memory_mutex_arc(),
    );

    for _ in 0..num_ops {
        let b = generate_long_number::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(&mut rng);
        let leading_zeros = rng.gen_range(0..(RV32_REGISTER_NUM_LIMBS - 1));
        let c = limb_sra::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(
            generate_long_number::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(&mut rng),
            leading_zeros,
        );
        run_rv32_divrem_rand_write_execute(opcode, &mut tester, &mut chip, b, c, &mut rng);
    }

    // Test special cases in addition to random cases (i.e. zero divisor with b > 0,
    // zero divisor with b < 0, r = 0 (3 cases), and signed overflow).
    run_rv32_divrem_rand_write_execute(
        opcode,
        &mut tester,
        &mut chip,
        [98, 188, 163, 127],
        [0, 0, 0, 0],
        &mut rng,
    );
    run_rv32_divrem_rand_write_execute(
        opcode,
        &mut tester,
        &mut chip,
        [98, 188, 163, 229],
        [0, 0, 0, 0],
        &mut rng,
    );
    run_rv32_divrem_rand_write_execute(
        opcode,
        &mut tester,
        &mut chip,
        [0, 0, 0, 128],
        [0, 1, 0, 0],
        &mut rng,
    );
    run_rv32_divrem_rand_write_execute(
        opcode,
        &mut tester,
        &mut chip,
        [0, 0, 0, 127],
        [0, 1, 0, 0],
        &mut rng,
    );
    run_rv32_divrem_rand_write_execute(
        opcode,
        &mut tester,
        &mut chip,
        [0, 0, 0, 0],
        [0, 0, 0, 0],
        &mut rng,
    );
    run_rv32_divrem_rand_write_execute(
        opcode,
        &mut tester,
        &mut chip,
        [0, 0, 0, 128],
        [255, 255, 255, 255],
        &mut rng,
    );

    let tester = tester
        .build()
        .load(chip)
        .load(bitwise_chip)
        .load(range_tuple_checker)
        .finalize();
    tester.simple_test().expect("Verification failed");
}

#[test]
fn rv32_div_rand_test() {
    run_rv32_divrem_rand_test(DivRemOpcode::DIV, 100);
}

#[test]
fn rv32_divu_rand_test() {
    run_rv32_divrem_rand_test(DivRemOpcode::DIVU, 100);
}

#[test]
fn rv32_rem_rand_test() {
    run_rv32_divrem_rand_test(DivRemOpcode::REM, 100);
}

#[test]
fn rv32_remu_rand_test() {
    run_rv32_divrem_rand_test(DivRemOpcode::REMU, 100);
}

//////////////////////////////////////////////////////////////////////////////////////
// NEGATIVE TESTS
//
// Given a fake trace of a single operation, setup a chip and run the test. We replace
// the write part of the trace and check that the core chip throws the expected error.
// A dummy adapter is used so memory interactions don't indirectly cause false passes.
//////////////////////////////////////////////////////////////////////////////////////

type Rv32DivRemTestChip<F> =
    VmChipWrapper<F, TestAdapterChip<F>, DivRemCoreChip<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>>;

#[derive(Default, Clone, Copy)]
struct DivRemPrankValues<const NUM_LIMBS: usize> {
    pub q: Option<[u32; NUM_LIMBS]>,
    pub r: Option<[u32; NUM_LIMBS]>,
    pub r_prime: Option<[u32; NUM_LIMBS]>,
    pub diff_val: Option<u32>,
    pub zero_divisor: Option<bool>,
    pub r_zero: Option<bool>,
}

fn run_rv32_divrem_negative_test(
    signed: bool,
    b: [u32; RV32_REGISTER_NUM_LIMBS],
    c: [u32; RV32_REGISTER_NUM_LIMBS],
    prank_vals: &DivRemPrankValues<RV32_REGISTER_NUM_LIMBS>,
    interaction_error: bool,
) {
    // the max number of limbs we currently support MUL for is 32 (i.e. for U256s)
    const MAX_NUM_LIMBS: u32 = 32;
    let bitwise_bus = BitwiseOperationLookupBus::new(BITWISE_OP_LOOKUP_BUS);
    let range_tuple_bus = RangeTupleCheckerBus::new(
        RANGE_TUPLE_CHECKER_BUS,
        [1 << RV32_CELL_BITS, MAX_NUM_LIMBS * (1 << RV32_CELL_BITS)],
    );

    let bitwise_chip = SharedBitwiseOperationLookupChip::<RV32_CELL_BITS>::new(bitwise_bus);
    let range_tuple_chip = SharedRangeTupleCheckerChip::new(range_tuple_bus);

    let mut tester = VmChipTestBuilder::default();
    let mut chip = Rv32DivRemTestChip::<F>::new(
        TestAdapterChip::new(
            vec![[b.map(F::from_canonical_u32), c.map(F::from_canonical_u32)].concat(); 2],
            vec![None],
            ExecutionBridge::new(tester.execution_bus(), tester.program_bus()),
        ),
        DivRemCoreChip::new(
            bitwise_chip.clone(),
            range_tuple_chip.clone(),
            DivRemOpcode::CLASS_OFFSET,
        ),
        tester.offline_memory_mutex_arc(),
    );

    let (div_opcode, rem_opcode) = if signed {
        (DivRemOpcode::DIV, DivRemOpcode::REM)
    } else {
        (DivRemOpcode::DIVU, DivRemOpcode::REMU)
    };
    tester.execute(
        &mut chip,
        &Instruction::from_usize(div_opcode.global_opcode(), [0, 0, 0, 1, 1]),
    );
    tester.execute(
        &mut chip,
        &Instruction::from_usize(rem_opcode.global_opcode(), [0, 0, 0, 1, 1]),
    );

    let (q, r, b_sign, c_sign, q_sign, case) =
        run_divrem::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(signed, &b, &c);
    let q = prank_vals.q.unwrap_or(q);
    let r = prank_vals.r.unwrap_or(r);
    let carries =
        run_mul_carries::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(signed, &c, &q, &r, q_sign);

    range_tuple_chip.clear();
    for i in 0..RV32_REGISTER_NUM_LIMBS {
        range_tuple_chip.add_count(&[q[i], carries[i]]);
        range_tuple_chip.add_count(&[r[i], carries[i + RV32_REGISTER_NUM_LIMBS]]);
    }

    if let Some(diff_val) = prank_vals.diff_val {
        bitwise_chip.clear();
        if signed {
            let b_sign_mask = if b_sign { 1 << (RV32_CELL_BITS - 1) } else { 0 };
            let c_sign_mask = if c_sign { 1 << (RV32_CELL_BITS - 1) } else { 0 };
            bitwise_chip.request_range(
                (b[RV32_REGISTER_NUM_LIMBS - 1] - b_sign_mask) << 1,
                (c[RV32_REGISTER_NUM_LIMBS - 1] - c_sign_mask) << 1,
            );
        }
        if case == DivRemCoreSpecialCase::None {
            bitwise_chip.request_range(diff_val - 1, 0);
        }
    }

    let trace_width = chip.trace_width();
    let adapter_width = BaseAir::<F>::width(chip.adapter.air());

    let modify_trace = |trace: &mut DenseMatrix<BabyBear>| {
        let mut values = trace.row_slice(0).to_vec();
        let cols: &mut DivRemCoreCols<F, RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS> =
            values.split_at_mut(adapter_width).1.borrow_mut();

        if let Some(q) = prank_vals.q {
            cols.q = q.map(F::from_canonical_u32);
        }
        if let Some(r) = prank_vals.r {
            cols.r = r.map(F::from_canonical_u32);
            let r_sum = r.iter().sum::<u32>();
            cols.r_sum_inv = F::from_canonical_u32(r_sum)
                .try_inverse()
                .unwrap_or(F::ZERO);
        }
        if let Some(r_prime) = prank_vals.r_prime {
            cols.r_prime = r_prime.map(F::from_canonical_u32);
            cols.r_inv = cols
                .r_prime
                .map(|r| (r - F::from_canonical_u32(256)).inverse());
        }
        if let Some(diff_val) = prank_vals.diff_val {
            cols.lt_diff = F::from_canonical_u32(diff_val);
        }
        if let Some(zero_divisor) = prank_vals.zero_divisor {
            cols.zero_divisor = F::from_bool(zero_divisor);
        }
        if let Some(r_zero) = prank_vals.r_zero {
            cols.r_zero = F::from_bool(r_zero);
        }

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
fn rv32_divrem_unsigned_wrong_q_negative_test() {
    let b: [u32; RV32_REGISTER_NUM_LIMBS] = [98, 188, 163, 229];
    let c: [u32; RV32_REGISTER_NUM_LIMBS] = [123, 34, 0, 0];
    let prank_vals = DivRemPrankValues {
        q: Some([245, 168, 7, 0]),
        ..Default::default()
    };
    run_rv32_divrem_negative_test(false, b, c, &prank_vals, true);
}

#[test]
fn rv32_divrem_unsigned_wrong_r_negative_test() {
    let b: [u32; RV32_REGISTER_NUM_LIMBS] = [98, 188, 163, 229];
    let c: [u32; RV32_REGISTER_NUM_LIMBS] = [123, 34, 0, 0];
    let prank_vals = DivRemPrankValues {
        r: Some([171, 3, 0, 0]),
        r_prime: Some([171, 3, 0, 0]),
        diff_val: Some(31),
        ..Default::default()
    };
    run_rv32_divrem_negative_test(false, b, c, &prank_vals, true);
}

#[test]
fn rv32_divrem_unsigned_high_mult_negative_test() {
    let b: [u32; RV32_REGISTER_NUM_LIMBS] = [0, 0, 1, 0];
    let c: [u32; RV32_REGISTER_NUM_LIMBS] = [0, 2, 0, 0];
    let prank_vals = DivRemPrankValues {
        q: Some([128, 0, 0, 1]),
        ..Default::default()
    };
    run_rv32_divrem_negative_test(false, b, c, &prank_vals, true);
}

#[test]
fn rv32_divrem_unsigned_zero_divisor_wrong_r_negative_test() {
    let b: [u32; RV32_REGISTER_NUM_LIMBS] = [254, 255, 255, 255];
    let c: [u32; RV32_REGISTER_NUM_LIMBS] = [0, 0, 0, 0];
    let prank_vals = DivRemPrankValues {
        r: Some([255, 255, 255, 255]),
        r_prime: Some([255, 255, 255, 255]),
        diff_val: Some(255),
        ..Default::default()
    };
    run_rv32_divrem_negative_test(false, b, c, &prank_vals, true);
}

#[test]
fn rv32_divrem_signed_wrong_q_negative_test() {
    let b: [u32; RV32_REGISTER_NUM_LIMBS] = [98, 188, 163, 229];
    let c: [u32; RV32_REGISTER_NUM_LIMBS] = [123, 34, 0, 0];
    let prank_vals = DivRemPrankValues {
        q: Some([74, 61, 255, 255]),
        ..Default::default()
    };
    run_rv32_divrem_negative_test(true, b, c, &prank_vals, true);
}

#[test]
fn rv32_divrem_signed_wrong_r_negative_test() {
    let b: [u32; RV32_REGISTER_NUM_LIMBS] = [98, 188, 163, 229];
    let c: [u32; RV32_REGISTER_NUM_LIMBS] = [123, 34, 0, 0];
    let prank_vals = DivRemPrankValues {
        r: Some([212, 241, 255, 255]),
        r_prime: Some([44, 14, 0, 0]),
        diff_val: Some(20),
        ..Default::default()
    };
    run_rv32_divrem_negative_test(true, b, c, &prank_vals, true);
}

#[test]
fn rv32_divrem_signed_high_mult_negative_test() {
    let b: [u32; RV32_REGISTER_NUM_LIMBS] = [0, 0, 0, 255];
    let c: [u32; RV32_REGISTER_NUM_LIMBS] = [0, 0, 0, 255];
    let prank_vals = DivRemPrankValues {
        q: Some([1, 0, 0, 1]),
        ..Default::default()
    };
    run_rv32_divrem_negative_test(true, b, c, &prank_vals, true);
}

#[test]
fn rv32_divrem_signed_r_wrong_sign_negative_test() {
    let b: [u32; RV32_REGISTER_NUM_LIMBS] = [0, 0, 1, 0];
    let c: [u32; RV32_REGISTER_NUM_LIMBS] = [50, 0, 0, 0];
    let prank_vals = DivRemPrankValues {
        q: Some([31, 5, 0, 0]),
        r: Some([242, 255, 255, 255]),
        r_prime: Some([242, 255, 255, 255]),
        diff_val: Some(192),
        ..Default::default()
    };
    run_rv32_divrem_negative_test(true, b, c, &prank_vals, false);
}

#[test]
fn rv32_divrem_signed_r_wrong_prime_negative_test() {
    let b: [u32; RV32_REGISTER_NUM_LIMBS] = [0, 0, 1, 0];
    let c: [u32; RV32_REGISTER_NUM_LIMBS] = [50, 0, 0, 0];
    let prank_vals = DivRemPrankValues {
        q: Some([31, 5, 0, 0]),
        r: Some([242, 255, 255, 255]),
        r_prime: Some([14, 0, 0, 0]),
        diff_val: Some(36),
        ..Default::default()
    };
    run_rv32_divrem_negative_test(true, b, c, &prank_vals, false);
}

#[test]
fn rv32_divrem_signed_zero_divisor_wrong_r_negative_test() {
    let b: [u32; RV32_REGISTER_NUM_LIMBS] = [254, 255, 255, 255];
    let c: [u32; RV32_REGISTER_NUM_LIMBS] = [0, 0, 0, 0];
    let prank_vals = DivRemPrankValues {
        r: Some([255, 255, 255, 255]),
        r_prime: Some([1, 0, 0, 0]),
        diff_val: Some(1),
        ..Default::default()
    };
    run_rv32_divrem_negative_test(true, b, c, &prank_vals, true);
}

#[test]
fn rv32_divrem_false_zero_divisor_flag_negative_test() {
    let b: [u32; RV32_REGISTER_NUM_LIMBS] = [0, 0, 1, 0];
    let c: [u32; RV32_REGISTER_NUM_LIMBS] = [50, 0, 0, 0];
    let prank_vals = DivRemPrankValues {
        q: Some([29, 5, 0, 0]),
        r: Some([86, 0, 0, 0]),
        r_prime: Some([86, 0, 0, 0]),
        diff_val: Some(36),
        zero_divisor: Some(true),
        ..Default::default()
    };
    run_rv32_divrem_negative_test(true, b, c, &prank_vals, false);
    run_rv32_divrem_negative_test(false, b, c, &prank_vals, false);
}

#[test]
fn rv32_divrem_false_r_zero_flag_negative_test() {
    let b: [u32; RV32_REGISTER_NUM_LIMBS] = [0, 0, 1, 0];
    let c: [u32; RV32_REGISTER_NUM_LIMBS] = [50, 0, 0, 0];
    let prank_vals = DivRemPrankValues {
        q: Some([29, 5, 0, 0]),
        r: Some([86, 0, 0, 0]),
        r_prime: Some([86, 0, 0, 0]),
        diff_val: Some(36),
        r_zero: Some(true),
        ..Default::default()
    };
    run_rv32_divrem_negative_test(true, b, c, &prank_vals, false);
    run_rv32_divrem_negative_test(false, b, c, &prank_vals, false);
}

#[test]
fn rv32_divrem_unset_zero_divisor_flag_negative_test() {
    let b: [u32; RV32_REGISTER_NUM_LIMBS] = [0, 0, 1, 0];
    let c: [u32; RV32_REGISTER_NUM_LIMBS] = [0, 0, 0, 0];
    let prank_vals = DivRemPrankValues {
        zero_divisor: Some(false),
        ..Default::default()
    };
    run_rv32_divrem_negative_test(true, b, c, &prank_vals, false);
    run_rv32_divrem_negative_test(false, b, c, &prank_vals, false);
}

#[test]
fn rv32_divrem_wrong_r_zero_flag_negative_test() {
    let b: [u32; RV32_REGISTER_NUM_LIMBS] = [0, 0, 0, 0];
    let c: [u32; RV32_REGISTER_NUM_LIMBS] = [0, 0, 0, 0];
    let prank_vals = DivRemPrankValues {
        zero_divisor: Some(false),
        r_zero: Some(true),
        ..Default::default()
    };
    run_rv32_divrem_negative_test(true, b, c, &prank_vals, false);
    run_rv32_divrem_negative_test(false, b, c, &prank_vals, false);
}

#[test]
fn rv32_divrem_unset_r_zero_flag_negative_test() {
    let b: [u32; RV32_REGISTER_NUM_LIMBS] = [0, 0, 1, 0];
    let c: [u32; RV32_REGISTER_NUM_LIMBS] = [0, 0, 1, 0];
    let prank_vals = DivRemPrankValues {
        r_zero: Some(false),
        ..Default::default()
    };
    run_rv32_divrem_negative_test(true, b, c, &prank_vals, false);
    run_rv32_divrem_negative_test(false, b, c, &prank_vals, false);
}

///////////////////////////////////////////////////////////////////////////////////////
/// SANITY TESTS
///
/// Ensure that solve functions produce the correct results.
///////////////////////////////////////////////////////////////////////////////////////

#[test]
fn run_divrem_unsigned_sanity_test() {
    let x: [u32; RV32_REGISTER_NUM_LIMBS] = [98, 188, 163, 229];
    let y: [u32; RV32_REGISTER_NUM_LIMBS] = [123, 34, 0, 0];
    let q: [u32; RV32_REGISTER_NUM_LIMBS] = [245, 168, 6, 0];
    let r: [u32; RV32_REGISTER_NUM_LIMBS] = [171, 4, 0, 0];

    let (res_q, res_r, x_sign, y_sign, q_sign, case) =
        run_divrem::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(false, &x, &y);
    for i in 0..RV32_REGISTER_NUM_LIMBS {
        assert_eq!(q[i], res_q[i]);
        assert_eq!(r[i], res_r[i]);
    }
    assert!(!x_sign);
    assert!(!y_sign);
    assert!(!q_sign);
    assert_eq!(case, DivRemCoreSpecialCase::None);
}

#[test]
fn run_divrem_unsigned_zero_divisor_test() {
    let x: [u32; RV32_REGISTER_NUM_LIMBS] = [98, 188, 163, 229];
    let y: [u32; RV32_REGISTER_NUM_LIMBS] = [0, 0, 0, 0];
    let q: [u32; RV32_REGISTER_NUM_LIMBS] = [255, 255, 255, 255];

    let (res_q, res_r, x_sign, y_sign, q_sign, case) =
        run_divrem::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(false, &x, &y);
    for i in 0..RV32_REGISTER_NUM_LIMBS {
        assert_eq!(q[i], res_q[i]);
        assert_eq!(x[i], res_r[i]);
    }
    assert!(!x_sign);
    assert!(!y_sign);
    assert!(!q_sign);
    assert_eq!(case, DivRemCoreSpecialCase::ZeroDivisor);
}

#[test]
fn run_divrem_signed_sanity_test() {
    let x: [u32; RV32_REGISTER_NUM_LIMBS] = [98, 188, 163, 229];
    let y: [u32; RV32_REGISTER_NUM_LIMBS] = [123, 34, 0, 0];
    let q: [u32; RV32_REGISTER_NUM_LIMBS] = [74, 60, 255, 255];
    let r: [u32; RV32_REGISTER_NUM_LIMBS] = [212, 240, 255, 255];

    let (res_q, res_r, x_sign, y_sign, q_sign, case) =
        run_divrem::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(true, &x, &y);
    for i in 0..RV32_REGISTER_NUM_LIMBS {
        assert_eq!(q[i], res_q[i]);
        assert_eq!(r[i], res_r[i]);
    }
    assert!(x_sign);
    assert!(!y_sign);
    assert!(q_sign);
    assert_eq!(case, DivRemCoreSpecialCase::None);
}

#[test]
fn run_divrem_signed_zero_divisor_test() {
    let x: [u32; RV32_REGISTER_NUM_LIMBS] = [98, 188, 163, 229];
    let y: [u32; RV32_REGISTER_NUM_LIMBS] = [0, 0, 0, 0];
    let q: [u32; RV32_REGISTER_NUM_LIMBS] = [255, 255, 255, 255];

    let (res_q, res_r, x_sign, y_sign, q_sign, case) =
        run_divrem::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(true, &x, &y);
    for i in 0..RV32_REGISTER_NUM_LIMBS {
        assert_eq!(q[i], res_q[i]);
        assert_eq!(x[i], res_r[i]);
    }
    assert!(x_sign);
    assert!(!y_sign);
    assert!(q_sign);
    assert_eq!(case, DivRemCoreSpecialCase::ZeroDivisor);
}

#[test]
fn run_divrem_signed_overflow_test() {
    let x: [u32; RV32_REGISTER_NUM_LIMBS] = [0, 0, 0, 128];
    let y: [u32; RV32_REGISTER_NUM_LIMBS] = [255, 255, 255, 255];
    let r: [u32; RV32_REGISTER_NUM_LIMBS] = [0, 0, 0, 0];

    let (res_q, res_r, x_sign, y_sign, q_sign, case) =
        run_divrem::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(true, &x, &y);
    for i in 0..RV32_REGISTER_NUM_LIMBS {
        assert_eq!(x[i], res_q[i]);
        assert_eq!(r[i], res_r[i]);
    }
    assert!(x_sign);
    assert!(y_sign);
    assert!(!q_sign);
    assert_eq!(case, DivRemCoreSpecialCase::SignedOverflow);
}

#[test]
fn run_divrem_signed_min_dividend_test() {
    let x: [u32; RV32_REGISTER_NUM_LIMBS] = [0, 0, 0, 128];
    let y: [u32; RV32_REGISTER_NUM_LIMBS] = [123, 34, 255, 255];
    let q: [u32; RV32_REGISTER_NUM_LIMBS] = [236, 147, 0, 0];
    let r: [u32; RV32_REGISTER_NUM_LIMBS] = [156, 149, 255, 255];

    let (res_q, res_r, x_sign, y_sign, q_sign, case) =
        run_divrem::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(true, &x, &y);
    for i in 0..RV32_REGISTER_NUM_LIMBS {
        assert_eq!(q[i], res_q[i]);
        assert_eq!(r[i], res_r[i]);
    }
    assert!(x_sign);
    assert!(y_sign);
    assert!(!q_sign);
    assert_eq!(case, DivRemCoreSpecialCase::None);
}

#[test]
fn run_divrem_zero_quotient_test() {
    let x: [u32; RV32_REGISTER_NUM_LIMBS] = [255, 255, 255, 255];
    let y: [u32; RV32_REGISTER_NUM_LIMBS] = [0, 0, 0, 1];
    let q: [u32; RV32_REGISTER_NUM_LIMBS] = [0, 0, 0, 0];

    let (res_q, res_r, x_sign, y_sign, q_sign, case) =
        run_divrem::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(true, &x, &y);
    for i in 0..RV32_REGISTER_NUM_LIMBS {
        assert_eq!(q[i], res_q[i]);
        assert_eq!(x[i], res_r[i]);
    }
    assert!(x_sign);
    assert!(!y_sign);
    assert!(!q_sign);
    assert_eq!(case, DivRemCoreSpecialCase::None);
}

#[test]
fn run_sltu_diff_idx_test() {
    let x: [u32; RV32_REGISTER_NUM_LIMBS] = [123, 34, 254, 67];
    let y: [u32; RV32_REGISTER_NUM_LIMBS] = [123, 34, 255, 67];
    assert_eq!(run_sltu_diff_idx(&x, &y, true), 2);
    assert_eq!(run_sltu_diff_idx(&y, &x, false), 2);
    assert_eq!(run_sltu_diff_idx(&x, &x, false), RV32_REGISTER_NUM_LIMBS);
}

#[test]
fn run_mul_carries_signed_sanity_test() {
    let d: [u32; RV32_REGISTER_NUM_LIMBS] = [197, 85, 150, 32];
    let q: [u32; RV32_REGISTER_NUM_LIMBS] = [51, 109, 78, 142];
    let r: [u32; RV32_REGISTER_NUM_LIMBS] = [200, 8, 68, 255];
    let c = [40, 101, 126, 206, 304, 376, 450, 464];
    let carry = run_mul_carries::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(true, &d, &q, &r, true);
    for (expected_c, actual_c) in c.iter().zip(carry.iter()) {
        assert_eq!(*expected_c, *actual_c)
    }
}

#[test]
fn run_mul_unsigned_sanity_test() {
    let d: [u32; RV32_REGISTER_NUM_LIMBS] = [197, 85, 150, 32];
    let q: [u32; RV32_REGISTER_NUM_LIMBS] = [51, 109, 78, 142];
    let r: [u32; RV32_REGISTER_NUM_LIMBS] = [200, 8, 68, 255];
    let c = [40, 101, 126, 206, 107, 93, 18, 0];
    let carry = run_mul_carries::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(false, &d, &q, &r, true);
    for (expected_c, actual_c) in c.iter().zip(carry.iter()) {
        assert_eq!(*expected_c, *actual_c)
    }
}
