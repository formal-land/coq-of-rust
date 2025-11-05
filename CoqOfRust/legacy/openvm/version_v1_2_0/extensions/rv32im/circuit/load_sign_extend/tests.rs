use std::{array, borrow::BorrowMut};

use openvm_circuit::arch::{
    testing::{memory::gen_pointer, VmChipTestBuilder},
    VmAdapterChip,
};
use openvm_instructions::{instruction::Instruction, LocalOpcode};
use openvm_rv32im_transpiler::Rv32LoadStoreOpcode::{self, *};
use openvm_stark_backend::{
    p3_air::BaseAir,
    p3_field::FieldAlgebra,
    p3_matrix::{
        dense::{DenseMatrix, RowMajorMatrix},
        Matrix,
    },
    utils::disable_debug_builder,
    verifier::VerificationError,
};
use openvm_stark_sdk::{config::setup_tracing, p3_baby_bear::BabyBear, utils::create_seeded_rng};
use rand::{rngs::StdRng, Rng};

use super::run_write_data_sign_extend;
use crate::{
    adapters::{compose, Rv32LoadStoreAdapterChip, RV32_CELL_BITS, RV32_REGISTER_NUM_LIMBS},
    load_sign_extend::LoadSignExtendCoreCols,
    LoadSignExtendCoreChip, Rv32LoadSignExtendChip,
};

const IMM_BITS: usize = 16;

type F = BabyBear;

fn into_limbs<const NUM_LIMBS: usize, const LIMB_BITS: usize>(num: u32) -> [u32; NUM_LIMBS] {
    array::from_fn(|i| (num >> (LIMB_BITS * i)) & ((1 << LIMB_BITS) - 1))
}

#[allow(clippy::too_many_arguments)]
fn set_and_execute(
    tester: &mut VmChipTestBuilder<F>,
    chip: &mut Rv32LoadSignExtendChip<F>,
    rng: &mut StdRng,
    opcode: Rv32LoadStoreOpcode,
    read_data: Option<[u32; RV32_REGISTER_NUM_LIMBS]>,
    rs1: Option<[u32; RV32_REGISTER_NUM_LIMBS]>,
    imm: Option<u32>,
    imm_sign: Option<u32>,
) {
    let imm = imm.unwrap_or(rng.gen_range(0..(1 << IMM_BITS)));
    let imm_sign = imm_sign.unwrap_or(rng.gen_range(0..2));
    let imm_ext = imm + imm_sign * (0xffffffff ^ ((1 << IMM_BITS) - 1));

    let alignment = match opcode {
        LOADB => 0,
        LOADH => 1,
        _ => unreachable!(),
    };
    let ptr_val = rng.gen_range(
        0..(1
            << (tester
                .memory_controller()
                .borrow()
                .mem_config()
                .pointer_max_bits
                - alignment)),
    ) << alignment;

    let rs1 = rs1
        .unwrap_or(into_limbs::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(
            (ptr_val as u32).wrapping_sub(imm_ext),
        ))
        .map(F::from_canonical_u32);
    let a = gen_pointer(rng, 4);
    let b = gen_pointer(rng, 4);

    let ptr_val = imm_ext.wrapping_add(compose(rs1));
    let shift_amount = ptr_val % 4;
    tester.write(1, b, rs1);

    let some_prev_data: [F; RV32_REGISTER_NUM_LIMBS] = if a != 0 {
        array::from_fn(|_| F::from_canonical_u32(rng.gen_range(0..(1 << RV32_CELL_BITS))))
    } else {
        [F::ZERO; RV32_REGISTER_NUM_LIMBS]
    };
    let read_data: [F; RV32_REGISTER_NUM_LIMBS] = read_data
        .unwrap_or(array::from_fn(|_| rng.gen_range(0..(1 << RV32_CELL_BITS))))
        .map(F::from_canonical_u32);

    tester.write(1, a, some_prev_data);
    tester.write(2, (ptr_val - shift_amount) as usize, read_data);

    tester.execute(
        chip,
        &Instruction::from_usize(
            opcode.global_opcode(),
            [
                a,
                b,
                imm as usize,
                1,
                2,
                (a != 0) as usize,
                imm_sign as usize,
            ],
        ),
    );

    let write_data = run_write_data_sign_extend::<_, RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(
        opcode,
        read_data,
        some_prev_data,
        shift_amount,
    );
    if a != 0 {
        assert_eq!(write_data, tester.read::<4>(1, a));
    } else {
        assert_eq!([F::ZERO; RV32_REGISTER_NUM_LIMBS], tester.read::<4>(1, a));
    }
}

///////////////////////////////////////////////////////////////////////////////////////
/// POSITIVE TESTS
///
/// Randomly generate computations and execute, ensuring that the generated trace
/// passes all constraints.
///////////////////////////////////////////////////////////////////////////////////////
#[test]
fn rand_load_sign_extend_test() {
    setup_tracing();
    let mut rng = create_seeded_rng();
    let mut tester = VmChipTestBuilder::default();
    let range_checker_chip = tester.memory_controller().borrow().range_checker.clone();
    let adapter = Rv32LoadStoreAdapterChip::<F>::new(
        tester.execution_bus(),
        tester.program_bus(),
        tester.memory_bridge(),
        tester.address_bits(),
        range_checker_chip.clone(),
    );
    let core = LoadSignExtendCoreChip::new(range_checker_chip);
    let mut chip =
        Rv32LoadSignExtendChip::<F>::new(adapter, core, tester.offline_memory_mutex_arc());

    let num_tests: usize = 100;
    for _ in 0..num_tests {
        set_and_execute(
            &mut tester,
            &mut chip,
            &mut rng,
            LOADB,
            None,
            None,
            None,
            None,
        );
        set_and_execute(
            &mut tester,
            &mut chip,
            &mut rng,
            LOADH,
            None,
            None,
            None,
            None,
        );
    }

    let tester = tester.build().load(chip).finalize();
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
fn run_negative_loadstore_test(
    opcode: Rv32LoadStoreOpcode,
    read_data: Option<[u32; RV32_REGISTER_NUM_LIMBS]>,
    data_most_sig_bit: Option<u32>,
    shift_most_sig_bit: Option<u32>,
    opcode_flags: Option<[bool; 3]>,
    rs1: Option<[u32; RV32_REGISTER_NUM_LIMBS]>,
    imm: Option<u32>,
    imm_sign: Option<u32>,
    expected_error: VerificationError,
) {
    let mut rng = create_seeded_rng();
    let mut tester = VmChipTestBuilder::default();
    let range_checker_chip = tester.memory_controller().borrow().range_checker.clone();
    let adapter = Rv32LoadStoreAdapterChip::<F>::new(
        tester.execution_bus(),
        tester.program_bus(),
        tester.memory_bridge(),
        tester.address_bits(),
        range_checker_chip.clone(),
    );
    let core = LoadSignExtendCoreChip::new(range_checker_chip.clone());
    let adapter_width = BaseAir::<F>::width(adapter.air());
    let mut chip =
        Rv32LoadSignExtendChip::<F>::new(adapter, core, tester.offline_memory_mutex_arc());

    set_and_execute(
        &mut tester,
        &mut chip,
        &mut rng,
        opcode,
        read_data,
        rs1,
        imm,
        imm_sign,
    );

    let modify_trace = |trace: &mut DenseMatrix<BabyBear>| {
        let mut trace_row = trace.row_slice(0).to_vec();

        let (_, core_row) = trace_row.split_at_mut(adapter_width);

        let core_cols: &mut LoadSignExtendCoreCols<F, RV32_REGISTER_NUM_LIMBS> =
            core_row.borrow_mut();

        if let Some(shifted_read_data) = read_data {
            core_cols.shifted_read_data = shifted_read_data.map(F::from_canonical_u32);
        }

        if let Some(data_most_sig_bit) = data_most_sig_bit {
            core_cols.data_most_sig_bit = F::from_canonical_u32(data_most_sig_bit);
        }
        if let Some(shift_most_sig_bit) = shift_most_sig_bit {
            core_cols.shift_most_sig_bit = F::from_canonical_u32(shift_most_sig_bit);
        }

        if let Some(opcode_flags) = opcode_flags {
            core_cols.opcode_loadb_flag0 = F::from_bool(opcode_flags[0]);
            core_cols.opcode_loadb_flag1 = F::from_bool(opcode_flags[1]);
            core_cols.opcode_loadh_flag = F::from_bool(opcode_flags[2]);
        }
        *trace = RowMajorMatrix::new(trace_row, trace.width());
    };

    drop(range_checker_chip);
    disable_debug_builder();
    let tester = tester
        .build()
        .load_and_prank_trace(chip, modify_trace)
        .finalize();
    tester.simple_test_with_expected_error(expected_error);
}

#[test]
fn loadstore_negative_tests() {
    run_negative_loadstore_test(
        LOADB,
        Some([233, 187, 145, 238]),
        Some(0),
        None,
        None,
        None,
        None,
        None,
        VerificationError::ChallengePhaseError,
    );

    run_negative_loadstore_test(
        LOADH,
        None,
        None,
        Some(0),
        None,
        Some([202, 109, 183, 26]),
        Some(31212),
        None,
        VerificationError::ChallengePhaseError,
    );

    run_negative_loadstore_test(
        LOADB,
        None,
        None,
        None,
        Some([true, false, false]),
        Some([250, 132, 77, 5]),
        Some(47741),
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
    let mut tester = VmChipTestBuilder::default();
    let range_checker_chip = tester.memory_controller().borrow().range_checker.clone();
    let adapter = Rv32LoadStoreAdapterChip::<F>::new(
        tester.execution_bus(),
        tester.program_bus(),
        tester.memory_bridge(),
        tester.address_bits(),
        range_checker_chip.clone(),
    );
    let core = LoadSignExtendCoreChip::new(range_checker_chip);
    let mut chip =
        Rv32LoadSignExtendChip::<F>::new(adapter, core, tester.offline_memory_mutex_arc());

    let num_tests: usize = 10;
    for _ in 0..num_tests {
        set_and_execute(
            &mut tester,
            &mut chip,
            &mut rng,
            LOADB,
            None,
            None,
            None,
            None,
        );
        set_and_execute(
            &mut tester,
            &mut chip,
            &mut rng,
            LOADH,
            None,
            None,
            None,
            None,
        );
    }
}

#[test]
fn solve_loadh_extend_sign_sanity_test() {
    let read_data = [34, 159, 237, 151].map(F::from_canonical_u32);
    let prev_data = [94, 183, 56, 241].map(F::from_canonical_u32);
    let write_data0 = run_write_data_sign_extend::<_, RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(
        LOADH, read_data, prev_data, 0,
    );
    let write_data2 = run_write_data_sign_extend::<_, RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(
        LOADH, read_data, prev_data, 2,
    );

    assert_eq!(write_data0, [34, 159, 255, 255].map(F::from_canonical_u32));
    assert_eq!(write_data2, [237, 151, 255, 255].map(F::from_canonical_u32));
}

#[test]
fn solve_loadh_extend_zero_sanity_test() {
    let read_data = [34, 121, 237, 97].map(F::from_canonical_u32);
    let prev_data = [94, 183, 56, 241].map(F::from_canonical_u32);
    let write_data0 = run_write_data_sign_extend::<_, RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(
        LOADH, read_data, prev_data, 0,
    );
    let write_data2 = run_write_data_sign_extend::<_, RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(
        LOADH, read_data, prev_data, 2,
    );

    assert_eq!(write_data0, [34, 121, 0, 0].map(F::from_canonical_u32));
    assert_eq!(write_data2, [237, 97, 0, 0].map(F::from_canonical_u32));
}

#[test]
fn solve_loadb_extend_sign_sanity_test() {
    let read_data = [45, 82, 99, 127].map(F::from_canonical_u32);
    let prev_data = [53, 180, 29, 244].map(F::from_canonical_u32);
    let write_data0 = run_write_data_sign_extend::<_, RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(
        LOADB, read_data, prev_data, 0,
    );
    let write_data1 = run_write_data_sign_extend::<_, RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(
        LOADB, read_data, prev_data, 1,
    );
    let write_data2 = run_write_data_sign_extend::<_, RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(
        LOADB, read_data, prev_data, 2,
    );
    let write_data3 = run_write_data_sign_extend::<_, RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(
        LOADB, read_data, prev_data, 3,
    );

    assert_eq!(write_data0, [45, 0, 0, 0].map(F::from_canonical_u32));
    assert_eq!(write_data1, [82, 0, 0, 0].map(F::from_canonical_u32));
    assert_eq!(write_data2, [99, 0, 0, 0].map(F::from_canonical_u32));
    assert_eq!(write_data3, [127, 0, 0, 0].map(F::from_canonical_u32));
}

#[test]
fn solve_loadb_extend_zero_sanity_test() {
    let read_data = [173, 210, 227, 255].map(F::from_canonical_u32);
    let prev_data = [53, 180, 29, 244].map(F::from_canonical_u32);
    let write_data0 = run_write_data_sign_extend::<_, RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(
        LOADB, read_data, prev_data, 0,
    );
    let write_data1 = run_write_data_sign_extend::<_, RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(
        LOADB, read_data, prev_data, 1,
    );
    let write_data2 = run_write_data_sign_extend::<_, RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(
        LOADB, read_data, prev_data, 2,
    );
    let write_data3 = run_write_data_sign_extend::<_, RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(
        LOADB, read_data, prev_data, 3,
    );

    assert_eq!(write_data0, [173, 255, 255, 255].map(F::from_canonical_u32));
    assert_eq!(write_data1, [210, 255, 255, 255].map(F::from_canonical_u32));
    assert_eq!(write_data2, [227, 255, 255, 255].map(F::from_canonical_u32));
    assert_eq!(write_data3, [255, 255, 255, 255].map(F::from_canonical_u32));
}
