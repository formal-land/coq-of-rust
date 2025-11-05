use std::{array, borrow::BorrowMut};

use openvm_circuit::arch::{
    testing::{VmChipTestBuilder, BITWISE_OP_LOOKUP_BUS},
    VmAdapterChip,
};
use openvm_circuit_primitives::bitwise_op_lookup::{
    BitwiseOperationLookupBus, SharedBitwiseOperationLookupChip,
};
use openvm_instructions::{instruction::Instruction, program::PC_BITS, LocalOpcode};
use openvm_rv32im_transpiler::Rv32JalrOpcode::{self, *};
use openvm_stark_backend::{
    p3_air::BaseAir,
    p3_field::{FieldAlgebra, PrimeField32},
    p3_matrix::{dense::RowMajorMatrix, Matrix},
    utils::disable_debug_builder,
    verifier::VerificationError,
    Chip, ChipUsageGetter,
};
use openvm_stark_sdk::{p3_baby_bear::BabyBear, utils::create_seeded_rng};
use rand::{rngs::StdRng, Rng};

use crate::{
    adapters::{compose, Rv32JalrAdapterChip, RV32_CELL_BITS, RV32_REGISTER_NUM_LIMBS},
    jalr::{run_jalr, Rv32JalrChip, Rv32JalrCoreChip, Rv32JalrCoreCols},
};

const IMM_BITS: usize = 16;
type F = BabyBear;

fn into_limbs(num: u32) -> [u32; 4] {
    array::from_fn(|i| (num >> (8 * i)) & 255)
}

#[allow(clippy::too_many_arguments)]
fn set_and_execute(
    tester: &mut VmChipTestBuilder<F>,
    chip: &mut Rv32JalrChip<F>,
    rng: &mut StdRng,
    opcode: Rv32JalrOpcode,
    initial_imm: Option<u32>,
    initial_imm_sign: Option<u32>,
    initial_pc: Option<u32>,
    rs1: Option<[u32; RV32_REGISTER_NUM_LIMBS]>,
) {
    let imm = initial_imm.unwrap_or(rng.gen_range(0..(1 << IMM_BITS)));
    let imm_sign = initial_imm_sign.unwrap_or(rng.gen_range(0..2));
    let imm_ext = imm + imm_sign * (0xffffffff ^ ((1 << IMM_BITS) - 1));
    let a = rng.gen_range(0..32) << 2;
    let b = rng.gen_range(1..32) << 2;
    let to_pc = rng.gen_range(0..(1 << PC_BITS));

    let rs1 = rs1.unwrap_or(into_limbs((to_pc as u32).wrapping_sub(imm_ext)));
    let rs1 = rs1.map(F::from_canonical_u32);

    tester.write(1, b, rs1);

    tester.execute_with_pc(
        chip,
        &Instruction::from_usize(
            opcode.global_opcode(),
            [
                a,
                b,
                imm as usize,
                1,
                0,
                (a != 0) as usize,
                imm_sign as usize,
            ],
        ),
        initial_pc.unwrap_or(rng.gen_range(0..(1 << PC_BITS))),
    );
    let initial_pc = tester.execution.last_from_pc().as_canonical_u32();
    let final_pc = tester.execution.last_to_pc().as_canonical_u32();

    let rs1 = compose(rs1);

    let (next_pc, rd_data) = run_jalr(opcode, initial_pc, imm_ext, rs1);
    let rd_data = if a == 0 { [0; 4] } else { rd_data };

    assert_eq!(next_pc, final_pc);
    assert_eq!(rd_data.map(F::from_canonical_u32), tester.read::<4>(1, a));
}

///////////////////////////////////////////////////////////////////////////////////////
/// POSITIVE TESTS
///
/// Randomly generate computations and execute, ensuring that the generated trace
/// passes all constraints.
///////////////////////////////////////////////////////////////////////////////////////
#[test]
fn rand_jalr_test() {
    let mut rng = create_seeded_rng();
    let bitwise_bus = BitwiseOperationLookupBus::new(BITWISE_OP_LOOKUP_BUS);
    let bitwise_chip = SharedBitwiseOperationLookupChip::<RV32_CELL_BITS>::new(bitwise_bus);
    let mut tester = VmChipTestBuilder::default();
    let range_checker_chip = tester.memory_controller().borrow().range_checker.clone();

    let adapter = Rv32JalrAdapterChip::<F>::new(
        tester.execution_bus(),
        tester.program_bus(),
        tester.memory_bridge(),
    );
    let inner = Rv32JalrCoreChip::new(bitwise_chip.clone(), range_checker_chip.clone());
    let mut chip = Rv32JalrChip::<F>::new(adapter, inner, tester.offline_memory_mutex_arc());

    let num_tests: usize = 100;
    for _ in 0..num_tests {
        set_and_execute(
            &mut tester,
            &mut chip,
            &mut rng,
            JALR,
            None,
            None,
            None,
            None,
        );
    }

    drop(range_checker_chip);
    let tester = tester.build().load(chip).load(bitwise_chip).finalize();
    tester.simple_test().expect("Verification failed");
}

//////////////////////////////////////////////////////////////////////////////////////
// NEGATIVE TESTS
//
// Given a fake trace of a single operation, setup a chip and run the test. We replace
// the write part of the trace and check that the core chip throws the expected error.
// A dummy adaptor is used so memory interactions don't indirectly cause false passes.
//////////////////////////////////////////////////////////////////////////////////////

#[allow(clippy::too_many_arguments)]
fn run_negative_jalr_test(
    opcode: Rv32JalrOpcode,
    initial_pc: Option<u32>,
    initial_rs1: Option<[u32; RV32_REGISTER_NUM_LIMBS]>,
    initial_imm: Option<u32>,
    initial_imm_sign: Option<u32>,
    rd_data: Option<[u32; RV32_REGISTER_NUM_LIMBS - 1]>,
    rs1_data: Option<[u32; RV32_REGISTER_NUM_LIMBS]>,
    to_pc_least_sig_bit: Option<u32>,
    to_pc_limbs: Option<[u32; 2]>,
    imm_sign: Option<u32>,
    expected_error: VerificationError,
) {
    let mut rng = create_seeded_rng();
    let bitwise_bus = BitwiseOperationLookupBus::new(BITWISE_OP_LOOKUP_BUS);
    let bitwise_chip = SharedBitwiseOperationLookupChip::<RV32_CELL_BITS>::new(bitwise_bus);
    let mut tester = VmChipTestBuilder::default();
    let range_checker_chip = tester.memory_controller().borrow().range_checker.clone();

    let adapter = Rv32JalrAdapterChip::<F>::new(
        tester.execution_bus(),
        tester.program_bus(),
        tester.memory_bridge(),
    );
    let adapter_width = BaseAir::<F>::width(adapter.air());
    let inner = Rv32JalrCoreChip::new(bitwise_chip.clone(), range_checker_chip.clone());
    let mut chip = Rv32JalrChip::<F>::new(adapter, inner, tester.offline_memory_mutex_arc());

    set_and_execute(
        &mut tester,
        &mut chip,
        &mut rng,
        opcode,
        initial_imm,
        initial_imm_sign,
        initial_pc,
        initial_rs1,
    );

    let tester = tester.build();

    let jalr_trace_width = chip.trace_width();
    let air = chip.air();
    let mut chip_input = chip.generate_air_proof_input();
    let jalr_trace = chip_input.raw.common_main.as_mut().unwrap();
    {
        let mut trace_row = jalr_trace.row_slice(0).to_vec();

        let (_, core_row) = trace_row.split_at_mut(adapter_width);

        let core_cols: &mut Rv32JalrCoreCols<F> = core_row.borrow_mut();

        if let Some(data) = rd_data {
            core_cols.rd_data = data.map(F::from_canonical_u32);
        }

        if let Some(data) = rs1_data {
            core_cols.rs1_data = data.map(F::from_canonical_u32);
        }

        if let Some(data) = to_pc_least_sig_bit {
            core_cols.to_pc_least_sig_bit = F::from_canonical_u32(data);
        }

        if let Some(data) = to_pc_limbs {
            core_cols.to_pc_limbs = data.map(F::from_canonical_u32);
        }

        if let Some(data) = imm_sign {
            core_cols.imm_sign = F::from_canonical_u32(data);
        }

        *jalr_trace = RowMajorMatrix::new(trace_row, jalr_trace_width);
    }

    drop(range_checker_chip);
    disable_debug_builder();
    let tester = tester
        .load_air_proof_input((air, chip_input))
        .load(bitwise_chip)
        .finalize();
    tester.simple_test_with_expected_error(expected_error);
}

#[test]
fn invalid_cols_negative_tests() {
    run_negative_jalr_test(
        JALR,
        None,
        None,
        Some(15362),
        Some(0),
        None,
        None,
        None,
        None,
        Some(1),
        VerificationError::OodEvaluationMismatch,
    );

    run_negative_jalr_test(
        JALR,
        None,
        None,
        Some(15362),
        Some(1),
        None,
        None,
        None,
        None,
        Some(0),
        VerificationError::OodEvaluationMismatch,
    );

    run_negative_jalr_test(
        JALR,
        None,
        Some([23, 154, 67, 28]),
        Some(42512),
        Some(1),
        None,
        None,
        Some(0),
        None,
        None,
        VerificationError::OodEvaluationMismatch,
    );
}

#[test]
fn overflow_negative_tests() {
    run_negative_jalr_test(
        JALR,
        Some(251),
        None,
        None,
        None,
        Some([1, 0, 0]),
        None,
        None,
        None,
        None,
        VerificationError::ChallengePhaseError,
    );

    run_negative_jalr_test(
        JALR,
        None,
        Some([0, 0, 0, 0]),
        Some((1 << 15) - 2),
        Some(0),
        None,
        None,
        None,
        Some([
            (F::NEG_ONE * F::from_canonical_u32((1 << 14) + 1)).as_canonical_u32(),
            1,
        ]),
        None,
        VerificationError::ChallengePhaseError,
    );
}

///////////////////////////////////////////////////////////////////////////////////////
/// SANITY TESTS
///
/// Ensure that solve functions produce the correct results.
///////////////////////////////////////////////////////////////////////////////////////
#[test]
fn execute_roundtrip_sanity_test() {
    let mut rng = create_seeded_rng();
    let bitwise_bus = BitwiseOperationLookupBus::new(BITWISE_OP_LOOKUP_BUS);
    let bitwise_chip = SharedBitwiseOperationLookupChip::<RV32_CELL_BITS>::new(bitwise_bus);
    let mut tester = VmChipTestBuilder::default();
    let range_checker_chip = tester.memory_controller().borrow().range_checker.clone();

    let adapter = Rv32JalrAdapterChip::<F>::new(
        tester.execution_bus(),
        tester.program_bus(),
        tester.memory_bridge(),
    );
    let inner = Rv32JalrCoreChip::new(bitwise_chip, range_checker_chip);
    let mut chip = Rv32JalrChip::<F>::new(adapter, inner, tester.offline_memory_mutex_arc());

    let num_tests: usize = 10;
    for _ in 0..num_tests {
        set_and_execute(
            &mut tester,
            &mut chip,
            &mut rng,
            JALR,
            None,
            None,
            None,
            None,
        );
    }
}

#[test]
fn run_jalr_sanity_test() {
    let opcode = JALR;
    let initial_pc = 789456120;
    let imm = -1235_i32 as u32;
    let rs1 = 736482910;
    let (next_pc, rd_data) = run_jalr(opcode, initial_pc, imm, rs1);
    assert_eq!(next_pc, 736481674);
    assert_eq!(rd_data, [252, 36, 14, 47]);
}
