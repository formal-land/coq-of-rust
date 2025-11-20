use std::{array, borrow::BorrowMut};

use openvm_circuit::{
    arch::{
        testing::{TestAdapterChip, VmChipTestBuilder, BITWISE_OP_LOOKUP_BUS},
        ExecutionBridge, VmAdapterChip, VmChipWrapper,
    },
    utils::generate_long_number,
};
use openvm_circuit_primitives::bitwise_op_lookup::{
    BitwiseOperationLookupBus, SharedBitwiseOperationLookupChip,
};
use openvm_instructions::{instruction::Instruction, LocalOpcode};
use openvm_rv32im_transpiler::ShiftOpcode;
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
use rand::Rng;

use super::{core::run_shift, Rv32ShiftChip, ShiftCoreChip};
use crate::{
    adapters::{Rv32BaseAluAdapterChip, RV32_CELL_BITS, RV32_REGISTER_NUM_LIMBS},
    shift::ShiftCoreCols,
    test_utils::{generate_rv32_is_type_immediate, rv32_rand_write_register_or_imm},
};

type F = BabyBear;

//////////////////////////////////////////////////////////////////////////////////////
// POSITIVE TESTS
//
// Randomly generate computations and execute, ensuring that the generated trace
// passes all constraints.
//////////////////////////////////////////////////////////////////////////////////////

fn run_rv32_shift_rand_test(opcode: ShiftOpcode, num_ops: usize) {
    let mut rng = create_seeded_rng();
    let bitwise_bus = BitwiseOperationLookupBus::new(BITWISE_OP_LOOKUP_BUS);
    let bitwise_chip = SharedBitwiseOperationLookupChip::<RV32_CELL_BITS>::new(bitwise_bus);

    let mut tester = VmChipTestBuilder::default();
    let mut chip = Rv32ShiftChip::<F>::new(
        Rv32BaseAluAdapterChip::new(
            tester.execution_bus(),
            tester.program_bus(),
            tester.memory_bridge(),
            bitwise_chip.clone(),
        ),
        ShiftCoreChip::new(
            bitwise_chip.clone(),
            tester.memory_controller().borrow().range_checker.clone(),
            ShiftOpcode::CLASS_OFFSET,
        ),
        tester.offline_memory_mutex_arc(),
    );

    for _ in 0..num_ops {
        let b = generate_long_number::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(&mut rng);
        let (c_imm, c) = if rng.gen_bool(0.5) {
            (
                None,
                generate_long_number::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(&mut rng),
            )
        } else {
            let (imm, c) = generate_rv32_is_type_immediate(&mut rng);
            (Some(imm), c)
        };

        let (instruction, rd) = rv32_rand_write_register_or_imm(
            &mut tester,
            b,
            c,
            c_imm,
            opcode.global_opcode().as_usize(),
            &mut rng,
        );
        tester.execute(&mut chip, &instruction);

        let (a, _, _) = run_shift::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(opcode, &b, &c);
        assert_eq!(
            a.map(F::from_canonical_u32),
            tester.read::<RV32_REGISTER_NUM_LIMBS>(1, rd)
        )
    }

    let tester = tester.build().load(chip).load(bitwise_chip).finalize();
    tester.simple_test().expect("Verification failed");
}

#[test]
fn rv32_shift_sll_rand_test() {
    run_rv32_shift_rand_test(ShiftOpcode::SLL, 100);
}

#[test]
fn rv32_shift_srl_rand_test() {
    run_rv32_shift_rand_test(ShiftOpcode::SRL, 100);
}

#[test]
fn rv32_shift_sra_rand_test() {
    run_rv32_shift_rand_test(ShiftOpcode::SRA, 100);
}

//////////////////////////////////////////////////////////////////////////////////////
// NEGATIVE TESTS
//
// Given a fake trace of a single operation, setup a chip and run the test. We replace
// the write part of the trace and check that the core chip throws the expected error.
// A dummy adapter is used so memory interactions don't indirectly cause false passes.
//////////////////////////////////////////////////////////////////////////////////////

type Rv32ShiftTestChip<F> =
    VmChipWrapper<F, TestAdapterChip<F>, ShiftCoreChip<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>>;

#[derive(Clone, Copy, Default, PartialEq)]
struct ShiftPrankValues<const NUM_LIMBS: usize, const LIMB_BITS: usize> {
    pub bit_shift: Option<u32>,
    pub bit_multiplier_left: Option<u32>,
    pub bit_multiplier_right: Option<u32>,
    pub b_sign: Option<u32>,
    pub bit_shift_marker: Option<[u32; LIMB_BITS]>,
    pub limb_shift_marker: Option<[u32; NUM_LIMBS]>,
    pub bit_shift_carry: Option<[u32; NUM_LIMBS]>,
}

#[allow(clippy::too_many_arguments)]
fn run_rv32_shift_negative_test(
    opcode: ShiftOpcode,
    a: [u32; RV32_REGISTER_NUM_LIMBS],
    b: [u32; RV32_REGISTER_NUM_LIMBS],
    c: [u32; RV32_REGISTER_NUM_LIMBS],
    prank_vals: ShiftPrankValues<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>,
    interaction_error: bool,
) {
    let bitwise_bus = BitwiseOperationLookupBus::new(BITWISE_OP_LOOKUP_BUS);
    let bitwise_chip = SharedBitwiseOperationLookupChip::<RV32_CELL_BITS>::new(bitwise_bus);
    let mut tester: VmChipTestBuilder<BabyBear> = VmChipTestBuilder::default();
    let range_checker_chip = tester.memory_controller().borrow().range_checker.clone();
    let mut chip = Rv32ShiftTestChip::<F>::new(
        TestAdapterChip::new(
            vec![[b.map(F::from_canonical_u32), c.map(F::from_canonical_u32)].concat()],
            vec![None],
            ExecutionBridge::new(tester.execution_bus(), tester.program_bus()),
        ),
        ShiftCoreChip::new(
            bitwise_chip.clone(),
            range_checker_chip.clone(),
            ShiftOpcode::CLASS_OFFSET,
        ),
        tester.offline_memory_mutex_arc(),
    );

    tester.execute(
        &mut chip,
        &Instruction::from_usize(opcode.global_opcode(), [0, 0, 0, 1, 1]),
    );

    let bit_shift = prank_vals
        .bit_shift
        .unwrap_or(c[0] % (RV32_CELL_BITS as u32));
    let bit_shift_carry = prank_vals
        .bit_shift_carry
        .unwrap_or(array::from_fn(|i| match opcode {
            ShiftOpcode::SLL => b[i] >> ((RV32_CELL_BITS as u32) - bit_shift),
            _ => b[i] % (1 << bit_shift),
        }));

    range_checker_chip.clear();
    range_checker_chip.add_count(bit_shift, RV32_CELL_BITS.ilog2() as usize);
    for (a_val, carry_val) in a.iter().zip(bit_shift_carry.iter()) {
        range_checker_chip.add_count(*a_val, RV32_CELL_BITS);
        range_checker_chip.add_count(*carry_val, bit_shift as usize);
    }

    let trace_width = chip.trace_width();
    let adapter_width = BaseAir::<F>::width(chip.adapter.air());

    let modify_trace = |trace: &mut DenseMatrix<BabyBear>| {
        let mut values = trace.row_slice(0).to_vec();
        let cols: &mut ShiftCoreCols<F, RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS> =
            values.split_at_mut(adapter_width).1.borrow_mut();

        cols.a = a.map(F::from_canonical_u32);
        if let Some(bit_multiplier_left) = prank_vals.bit_multiplier_left {
            cols.bit_multiplier_left = F::from_canonical_u32(bit_multiplier_left);
        }
        if let Some(bit_multiplier_right) = prank_vals.bit_multiplier_right {
            cols.bit_multiplier_right = F::from_canonical_u32(bit_multiplier_right);
        }
        if let Some(b_sign) = prank_vals.b_sign {
            cols.b_sign = F::from_canonical_u32(b_sign);
        }
        if let Some(bit_shift_marker) = prank_vals.bit_shift_marker {
            cols.bit_shift_marker = bit_shift_marker.map(F::from_canonical_u32);
        }
        if let Some(limb_shift_marker) = prank_vals.limb_shift_marker {
            cols.limb_shift_marker = limb_shift_marker.map(F::from_canonical_u32);
        }
        if let Some(bit_shift_carry) = prank_vals.bit_shift_carry {
            cols.bit_shift_carry = bit_shift_carry.map(F::from_canonical_u32);
        }

        *trace = RowMajorMatrix::new(values, trace_width);
    };

    drop(range_checker_chip);
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
fn rv32_shift_wrong_negative_test() {
    let a = [1, 0, 0, 0];
    let b = [1, 0, 0, 0];
    let c = [1, 0, 0, 0];
    let prank_vals = Default::default();
    run_rv32_shift_negative_test(ShiftOpcode::SLL, a, b, c, prank_vals, false);
    run_rv32_shift_negative_test(ShiftOpcode::SRL, a, b, c, prank_vals, false);
    run_rv32_shift_negative_test(ShiftOpcode::SRA, a, b, c, prank_vals, false);
}

#[test]
fn rv32_sll_wrong_bit_shift_negative_test() {
    let a = [0, 4, 4, 4];
    let b = [1, 1, 1, 1];
    let c = [9, 10, 100, 0];
    let prank_vals = ShiftPrankValues {
        bit_shift: Some(2),
        bit_multiplier_left: Some(4),
        bit_shift_marker: Some([0, 0, 1, 0, 0, 0, 0, 0]),
        ..Default::default()
    };
    run_rv32_shift_negative_test(ShiftOpcode::SLL, a, b, c, prank_vals, true);
}

#[test]
fn rv32_sll_wrong_limb_shift_negative_test() {
    let a = [0, 0, 2, 2];
    let b = [1, 1, 1, 1];
    let c = [9, 0, 0, 0];
    let prank_vals = ShiftPrankValues {
        limb_shift_marker: Some([0, 0, 1, 0]),
        ..Default::default()
    };
    run_rv32_shift_negative_test(ShiftOpcode::SLL, a, b, c, prank_vals, true);
}

#[test]
fn rv32_sll_wrong_bit_carry_negative_test() {
    let a = [0, 510, 510, 510];
    let b = [255, 255, 255, 255];
    let c = [9, 0, 0, 0];
    let prank_vals = ShiftPrankValues {
        bit_shift_carry: Some([0, 0, 0, 0]),
        ..Default::default()
    };
    run_rv32_shift_negative_test(ShiftOpcode::SLL, a, b, c, prank_vals, true);
}

#[test]
fn rv32_sll_wrong_bit_mult_side_negative_test() {
    let a = [128, 128, 128, 0];
    let b = [1, 1, 1, 1];
    let c = [9, 0, 0, 0];
    let prank_vals = ShiftPrankValues {
        bit_multiplier_left: Some(0),
        bit_multiplier_right: Some(1),
        ..Default::default()
    };
    run_rv32_shift_negative_test(ShiftOpcode::SLL, a, b, c, prank_vals, false);
}

#[test]
fn rv32_srl_wrong_bit_shift_negative_test() {
    let a = [0, 0, 32, 0];
    let b = [0, 0, 0, 128];
    let c = [9, 0, 0, 0];
    let prank_vals = ShiftPrankValues {
        bit_shift: Some(2),
        bit_multiplier_left: Some(4),
        bit_shift_marker: Some([0, 0, 1, 0, 0, 0, 0, 0]),
        ..Default::default()
    };
    run_rv32_shift_negative_test(ShiftOpcode::SRL, a, b, c, prank_vals, false);
}

#[test]
fn rv32_srl_wrong_limb_shift_negative_test() {
    let a = [0, 64, 0, 0];
    let b = [0, 0, 0, 128];
    let c = [9, 0, 0, 0];
    let prank_vals = ShiftPrankValues {
        limb_shift_marker: Some([0, 1, 0, 0]),
        ..Default::default()
    };
    run_rv32_shift_negative_test(ShiftOpcode::SRL, a, b, c, prank_vals, false);
}

#[test]
fn rv32_srx_wrong_bit_mult_side_negative_test() {
    let a = [0, 0, 0, 0];
    let b = [0, 0, 0, 128];
    let c = [9, 0, 0, 0];
    let prank_vals = ShiftPrankValues {
        bit_multiplier_left: Some(1),
        bit_multiplier_right: Some(0),
        ..Default::default()
    };
    run_rv32_shift_negative_test(ShiftOpcode::SRL, a, b, c, prank_vals, false);
    run_rv32_shift_negative_test(ShiftOpcode::SRA, a, b, c, prank_vals, false);
}

#[test]
fn rv32_sra_wrong_bit_shift_negative_test() {
    let a = [0, 0, 224, 255];
    let b = [0, 0, 0, 128];
    let c = [9, 0, 0, 0];
    let prank_vals = ShiftPrankValues {
        bit_shift: Some(2),
        bit_multiplier_left: Some(4),
        bit_shift_marker: Some([0, 0, 1, 0, 0, 0, 0, 0]),
        ..Default::default()
    };
    run_rv32_shift_negative_test(ShiftOpcode::SRA, a, b, c, prank_vals, false);
}

#[test]
fn rv32_sra_wrong_limb_shift_negative_test() {
    let a = [0, 192, 255, 255];
    let b = [0, 0, 0, 128];
    let c = [9, 0, 0, 0];
    let prank_vals = ShiftPrankValues {
        limb_shift_marker: Some([0, 1, 0, 0]),
        ..Default::default()
    };
    run_rv32_shift_negative_test(ShiftOpcode::SRA, a, b, c, prank_vals, false);
}

#[test]
fn rv32_sra_wrong_sign_negative_test() {
    let a = [0, 0, 64, 0];
    let b = [0, 0, 0, 128];
    let c = [9, 0, 0, 0];
    let prank_vals = ShiftPrankValues {
        b_sign: Some(0),
        ..Default::default()
    };
    run_rv32_shift_negative_test(ShiftOpcode::SRA, a, b, c, prank_vals, true);
}

///////////////////////////////////////////////////////////////////////////////////////
/// SANITY TESTS
///
/// Ensure that solve functions produce the correct results.
///////////////////////////////////////////////////////////////////////////////////////

#[test]
fn run_sll_sanity_test() {
    let x: [u32; RV32_REGISTER_NUM_LIMBS] = [45, 7, 61, 186];
    let y: [u32; RV32_REGISTER_NUM_LIMBS] = [91, 0, 100, 0];
    let z: [u32; RV32_REGISTER_NUM_LIMBS] = [0, 0, 0, 104];
    let (result, limb_shift, bit_shift) =
        run_shift::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(ShiftOpcode::SLL, &x, &y);
    for i in 0..RV32_REGISTER_NUM_LIMBS {
        assert_eq!(z[i], result[i])
    }
    let shift = (y[0] as usize) % (RV32_REGISTER_NUM_LIMBS * RV32_CELL_BITS);
    assert_eq!(shift / RV32_CELL_BITS, limb_shift);
    assert_eq!(shift % RV32_CELL_BITS, bit_shift);
}

#[test]
fn run_srl_sanity_test() {
    let x: [u32; RV32_REGISTER_NUM_LIMBS] = [31, 190, 221, 200];
    let y: [u32; RV32_REGISTER_NUM_LIMBS] = [49, 190, 190, 190];
    let z: [u32; RV32_REGISTER_NUM_LIMBS] = [110, 100, 0, 0];
    let (result, limb_shift, bit_shift) =
        run_shift::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(ShiftOpcode::SRL, &x, &y);
    for i in 0..RV32_REGISTER_NUM_LIMBS {
        assert_eq!(z[i], result[i])
    }
    let shift = (y[0] as usize) % (RV32_REGISTER_NUM_LIMBS * RV32_CELL_BITS);
    assert_eq!(shift / RV32_CELL_BITS, limb_shift);
    assert_eq!(shift % RV32_CELL_BITS, bit_shift);
}

#[test]
fn run_sra_sanity_test() {
    let x: [u32; RV32_REGISTER_NUM_LIMBS] = [31, 190, 221, 200];
    let y: [u32; RV32_REGISTER_NUM_LIMBS] = [113, 20, 50, 80];
    let z: [u32; RV32_REGISTER_NUM_LIMBS] = [110, 228, 255, 255];
    let (result, limb_shift, bit_shift) =
        run_shift::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(ShiftOpcode::SRA, &x, &y);
    for i in 0..RV32_REGISTER_NUM_LIMBS {
        assert_eq!(z[i], result[i])
    }
    let shift = (y[0] as usize) % (RV32_REGISTER_NUM_LIMBS * RV32_CELL_BITS);
    assert_eq!(shift / RV32_CELL_BITS, limb_shift);
    assert_eq!(shift % RV32_CELL_BITS, bit_shift);
}
