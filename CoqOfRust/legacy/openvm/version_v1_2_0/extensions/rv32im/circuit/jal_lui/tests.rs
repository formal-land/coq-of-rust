use std::borrow::BorrowMut;

use openvm_circuit::arch::{
    testing::{VmChipTestBuilder, BITWISE_OP_LOOKUP_BUS},
    VmAdapterChip,
};
use openvm_circuit_primitives::bitwise_op_lookup::{
    BitwiseOperationLookupBus, SharedBitwiseOperationLookupChip,
};
use openvm_instructions::{instruction::Instruction, program::PC_BITS, LocalOpcode};
use openvm_rv32im_transpiler::Rv32JalLuiOpcode::{self, *};
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

use super::{run_jal_lui, Rv32JalLuiChip, Rv32JalLuiCoreChip};
use crate::{
    adapters::{
        Rv32CondRdWriteAdapterChip, Rv32CondRdWriteAdapterCols, RV32_CELL_BITS,
        RV32_REGISTER_NUM_LIMBS, RV_IS_TYPE_IMM_BITS,
    },
    jal_lui::Rv32JalLuiCoreCols,
};

const IMM_BITS: usize = 20;
const LIMB_MAX: u32 = (1 << RV32_CELL_BITS) - 1;
type F = BabyBear;

fn set_and_execute(
    tester: &mut VmChipTestBuilder<F>,
    chip: &mut Rv32JalLuiChip<F>,
    rng: &mut StdRng,
    opcode: Rv32JalLuiOpcode,
    imm: Option<i32>,
    initial_pc: Option<u32>,
) {
    let imm: i32 = imm.unwrap_or(rng.gen_range(0..(1 << IMM_BITS)));
    let imm = match opcode {
        JAL => ((imm >> 1) << 2) - (1 << IMM_BITS),
        LUI => imm,
    };

    let a = rng.gen_range((opcode == LUI) as usize..32) << 2;
    let needs_write = a != 0 || opcode == LUI;

    tester.execute_with_pc(
        chip,
        &Instruction::large_from_isize(
            opcode.global_opcode(),
            a as isize,
            0,
            imm as isize,
            1,
            0,
            needs_write as isize,
            0,
        ),
        initial_pc.unwrap_or(rng.gen_range(imm.unsigned_abs()..(1 << PC_BITS))),
    );
    let initial_pc = tester.execution.last_from_pc().as_canonical_u32();
    let final_pc = tester.execution.last_to_pc().as_canonical_u32();

    let (next_pc, rd_data) = run_jal_lui(opcode, initial_pc, imm);
    let rd_data = if needs_write { rd_data } else { [0; 4] };

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
fn rand_jal_lui_test() {
    let mut rng = create_seeded_rng();
    let bitwise_bus = BitwiseOperationLookupBus::new(BITWISE_OP_LOOKUP_BUS);
    let bitwise_chip = SharedBitwiseOperationLookupChip::<RV32_CELL_BITS>::new(bitwise_bus);

    let mut tester = VmChipTestBuilder::default();
    let adapter = Rv32CondRdWriteAdapterChip::<F>::new(
        tester.execution_bus(),
        tester.program_bus(),
        tester.memory_bridge(),
    );
    let core = Rv32JalLuiCoreChip::new(bitwise_chip.clone());
    let mut chip = Rv32JalLuiChip::<F>::new(adapter, core, tester.offline_memory_mutex_arc());

    let num_tests: usize = 100;
    for _ in 0..num_tests {
        set_and_execute(&mut tester, &mut chip, &mut rng, JAL, None, None);
        set_and_execute(&mut tester, &mut chip, &mut rng, LUI, None, None);
    }

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
fn run_negative_jal_lui_test(
    opcode: Rv32JalLuiOpcode,
    initial_imm: Option<i32>,
    initial_pc: Option<u32>,
    rd_data: Option<[u32; RV32_REGISTER_NUM_LIMBS]>,
    imm: Option<i32>,
    is_jal: Option<bool>,
    is_lui: Option<bool>,
    needs_write: Option<bool>,
    expected_error: VerificationError,
) {
    let mut rng = create_seeded_rng();
    let bitwise_bus = BitwiseOperationLookupBus::new(BITWISE_OP_LOOKUP_BUS);
    let bitwise_chip = SharedBitwiseOperationLookupChip::<RV32_CELL_BITS>::new(bitwise_bus);

    let mut tester = VmChipTestBuilder::default();
    let adapter = Rv32CondRdWriteAdapterChip::<F>::new(
        tester.execution_bus(),
        tester.program_bus(),
        tester.memory_bridge(),
    );
    let adapter_width = BaseAir::<F>::width(adapter.air());
    let core = Rv32JalLuiCoreChip::new(bitwise_chip.clone());
    let mut chip = Rv32JalLuiChip::<F>::new(adapter, core, tester.offline_memory_mutex_arc());

    set_and_execute(
        &mut tester,
        &mut chip,
        &mut rng,
        opcode,
        initial_imm,
        initial_pc,
    );

    let tester = tester.build();

    let jal_lui_trace_width = chip.trace_width();
    let air = chip.air();
    let mut chip_input = chip.generate_air_proof_input();
    let jal_lui_trace = chip_input.raw.common_main.as_mut().unwrap();
    {
        let mut trace_row = jal_lui_trace.row_slice(0).to_vec();

        let (adapter_row, core_row) = trace_row.split_at_mut(adapter_width);

        let adapter_cols: &mut Rv32CondRdWriteAdapterCols<F> = adapter_row.borrow_mut();
        let core_cols: &mut Rv32JalLuiCoreCols<F> = core_row.borrow_mut();

        if let Some(data) = rd_data {
            core_cols.rd_data = data.map(F::from_canonical_u32);
        }

        if let Some(imm) = imm {
            core_cols.imm = if imm < 0 {
                F::NEG_ONE * F::from_canonical_u32((-imm) as u32)
            } else {
                F::from_canonical_u32(imm as u32)
            };
        }
        if let Some(is_jal) = is_jal {
            core_cols.is_jal = F::from_bool(is_jal);
        }
        if let Some(is_lui) = is_lui {
            core_cols.is_lui = F::from_bool(is_lui);
        }

        if let Some(needs_write) = needs_write {
            adapter_cols.needs_write = F::from_bool(needs_write);
        }

        *jal_lui_trace = RowMajorMatrix::new(trace_row, jal_lui_trace_width);
    }

    disable_debug_builder();
    let tester = tester
        .load_air_proof_input((air, chip_input))
        .load(bitwise_chip)
        .finalize();
    tester.simple_test_with_expected_error(expected_error);
}

#[test]
fn opcode_flag_negative_test() {
    run_negative_jal_lui_test(
        JAL,
        None,
        None,
        None,
        None,
        Some(false),
        Some(true),
        None,
        VerificationError::OodEvaluationMismatch,
    );
    run_negative_jal_lui_test(
        JAL,
        None,
        None,
        None,
        None,
        Some(false),
        Some(false),
        Some(false),
        VerificationError::ChallengePhaseError,
    );
    run_negative_jal_lui_test(
        LUI,
        None,
        None,
        None,
        None,
        Some(true),
        Some(false),
        None,
        VerificationError::OodEvaluationMismatch,
    );
}

#[test]
fn overflow_negative_tests() {
    run_negative_jal_lui_test(
        JAL,
        None,
        None,
        Some([LIMB_MAX, LIMB_MAX, LIMB_MAX, LIMB_MAX]),
        None,
        None,
        None,
        None,
        VerificationError::OodEvaluationMismatch,
    );
    run_negative_jal_lui_test(
        LUI,
        None,
        None,
        Some([LIMB_MAX, LIMB_MAX, LIMB_MAX, LIMB_MAX]),
        None,
        None,
        None,
        None,
        VerificationError::OodEvaluationMismatch,
    );
    run_negative_jal_lui_test(
        LUI,
        None,
        None,
        Some([0, LIMB_MAX, LIMB_MAX, LIMB_MAX + 1]),
        None,
        None,
        None,
        None,
        VerificationError::OodEvaluationMismatch,
    );
    run_negative_jal_lui_test(
        LUI,
        None,
        None,
        None,
        Some(-1),
        None,
        None,
        None,
        VerificationError::OodEvaluationMismatch,
    );
    run_negative_jal_lui_test(
        LUI,
        None,
        None,
        None,
        Some(-28),
        None,
        None,
        None,
        VerificationError::OodEvaluationMismatch,
    );
    run_negative_jal_lui_test(
        JAL,
        None,
        Some(251),
        Some([F::NEG_ONE.as_canonical_u32(), 1, 0, 0]),
        None,
        None,
        None,
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
    let adapter = Rv32CondRdWriteAdapterChip::<F>::new(
        tester.execution_bus(),
        tester.program_bus(),
        tester.memory_bridge(),
    );
    let core = Rv32JalLuiCoreChip::new(bitwise_chip);
    let mut chip = Rv32JalLuiChip::<F>::new(adapter, core, tester.offline_memory_mutex_arc());
    let num_tests: usize = 10;
    for _ in 0..num_tests {
        set_and_execute(&mut tester, &mut chip, &mut rng, JAL, None, None);
        set_and_execute(&mut tester, &mut chip, &mut rng, LUI, None, None);
    }

    set_and_execute(
        &mut tester,
        &mut chip,
        &mut rng,
        LUI,
        Some((1 << IMM_BITS) - 1),
        None,
    );
    set_and_execute(
        &mut tester,
        &mut chip,
        &mut rng,
        JAL,
        Some((1 << RV_IS_TYPE_IMM_BITS) - 1),
        None,
    );
}

#[test]
fn run_jal_sanity_test() {
    let opcode = JAL;
    let initial_pc = 28120;
    let imm = -2048;
    let (next_pc, rd_data) = run_jal_lui(opcode, initial_pc, imm);
    assert_eq!(next_pc, 26072);
    assert_eq!(rd_data, [220, 109, 0, 0]);
}

#[test]
fn run_lui_sanity_test() {
    let opcode = LUI;
    let initial_pc = 456789120;
    let imm = 853679;
    let (next_pc, rd_data) = run_jal_lui(opcode, initial_pc, imm);
    assert_eq!(next_pc, 456789124);
    assert_eq!(rd_data, [0, 240, 106, 208]);
}
