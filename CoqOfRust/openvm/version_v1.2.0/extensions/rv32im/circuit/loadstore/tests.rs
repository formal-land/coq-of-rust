use std::{array, borrow::BorrowMut};

use openvm_circuit::{
    arch::{
        testing::{memory::gen_pointer, VmChipTestBuilder},
        VmAdapterChip,
    },
    utils::u32_into_limbs,
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
use rand::{rngs::StdRng, seq::SliceRandom, Rng};

use super::{run_write_data, LoadStoreCoreChip, Rv32LoadStoreChip};
use crate::{
    adapters::{compose, Rv32LoadStoreAdapterChip, RV32_CELL_BITS, RV32_REGISTER_NUM_LIMBS},
    loadstore::LoadStoreCoreCols,
};

const IMM_BITS: usize = 16;

type F = BabyBear;

#[allow(clippy::too_many_arguments)]
fn set_and_execute(
    tester: &mut VmChipTestBuilder<F>,
    chip: &mut Rv32LoadStoreChip<F>,
    rng: &mut StdRng,
    opcode: Rv32LoadStoreOpcode,
    rs1: Option<[u32; RV32_REGISTER_NUM_LIMBS]>,
    imm: Option<u32>,
    imm_sign: Option<u32>,
    mem_as: Option<usize>,
) {
    let imm = imm.unwrap_or(rng.gen_range(0..(1 << IMM_BITS)));
    let imm_sign = imm_sign.unwrap_or(rng.gen_range(0..2));
    let imm_ext = imm + imm_sign * (0xffffffff ^ ((1 << IMM_BITS) - 1));

    let alignment = match opcode {
        LOADW | STOREW => 2,
        LOADHU | STOREH => 1,
        LOADBU | STOREB => 0,
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
        .unwrap_or(u32_into_limbs::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(
            (ptr_val as u32).wrapping_sub(imm_ext),
        ))
        .map(F::from_canonical_u32);
    let a = gen_pointer(rng, 4);
    let b = gen_pointer(rng, 4);
    let is_load = [LOADW, LOADHU, LOADBU].contains(&opcode);
    let mem_as = mem_as.unwrap_or(if is_load {
        *[1, 2].choose(rng).unwrap()
    } else {
        *[2, 3, 4].choose(rng).unwrap()
    });

    let ptr_val = imm_ext.wrapping_add(compose(rs1));
    let shift_amount = ptr_val % 4;
    tester.write(1, b, rs1);

    let mut some_prev_data: [F; RV32_REGISTER_NUM_LIMBS] =
        array::from_fn(|_| F::from_canonical_u32(rng.gen_range(0..(1 << RV32_CELL_BITS))));
    let mut read_data: [F; RV32_REGISTER_NUM_LIMBS] =
        array::from_fn(|_| F::from_canonical_u32(rng.gen_range(0..(1 << RV32_CELL_BITS))));

    if is_load {
        if a == 0 {
            some_prev_data = [F::ZERO; RV32_REGISTER_NUM_LIMBS];
        }
        tester.write(1, a, some_prev_data);
        if mem_as == 1 && ptr_val - shift_amount == 0 {
            read_data = [F::ZERO; RV32_REGISTER_NUM_LIMBS];
        }
        tester.write(mem_as, (ptr_val - shift_amount) as usize, read_data);
    } else {
        if a == 0 {
            read_data = [F::ZERO; RV32_REGISTER_NUM_LIMBS];
        }
        tester.write(mem_as, (ptr_val - shift_amount) as usize, some_prev_data);
        tester.write(1, a, read_data);
    }

    let enabled_write = !(is_load & (a == 0));

    tester.execute(
        chip,
        &Instruction::from_usize(
            opcode.global_opcode(),
            [
                a,
                b,
                imm as usize,
                1,
                mem_as,
                enabled_write as usize,
                imm_sign as usize,
            ],
        ),
    );

    let write_data = run_write_data(opcode, read_data, some_prev_data, shift_amount);
    if is_load {
        if enabled_write {
            assert_eq!(write_data, tester.read::<4>(1, a));
        } else {
            assert_eq!([F::ZERO; RV32_REGISTER_NUM_LIMBS], tester.read::<4>(1, a));
        }
    } else {
        assert_eq!(
            write_data,
            tester.read::<4>(mem_as, (ptr_val - shift_amount) as usize)
        );
    }
}

///////////////////////////////////////////////////////////////////////////////////////
/// POSITIVE TESTS
///
/// Randomly generate computations and execute, ensuring that the generated trace
/// passes all constraints.
///////////////////////////////////////////////////////////////////////////////////////
#[test]
fn rand_loadstore_test() {
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

    let core = LoadStoreCoreChip::new(Rv32LoadStoreOpcode::CLASS_OFFSET);
    let mut chip = Rv32LoadStoreChip::<F>::new(adapter, core, tester.offline_memory_mutex_arc());

    let num_tests: usize = 100;
    for _ in 0..num_tests {
        set_and_execute(
            &mut tester,
            &mut chip,
            &mut rng,
            LOADW,
            None,
            None,
            None,
            None,
        );
        set_and_execute(
            &mut tester,
            &mut chip,
            &mut rng,
            LOADBU,
            None,
            None,
            None,
            None,
        );
        set_and_execute(
            &mut tester,
            &mut chip,
            &mut rng,
            LOADHU,
            None,
            None,
            None,
            None,
        );
        set_and_execute(
            &mut tester,
            &mut chip,
            &mut rng,
            STOREW,
            None,
            None,
            None,
            None,
        );
        set_and_execute(
            &mut tester,
            &mut chip,
            &mut rng,
            STOREB,
            None,
            None,
            None,
            None,
        );
        set_and_execute(
            &mut tester,
            &mut chip,
            &mut rng,
            STOREH,
            None,
            None,
            None,
            None,
        );
    }

    drop(range_checker_chip);
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
    prev_data: Option<[u32; RV32_REGISTER_NUM_LIMBS]>,
    write_data: Option<[u32; RV32_REGISTER_NUM_LIMBS]>,
    flags: Option<[u32; 4]>,
    is_load: Option<bool>,
    rs1: Option<[u32; RV32_REGISTER_NUM_LIMBS]>,
    imm: Option<u32>,
    imm_sign: Option<u32>,
    mem_as: Option<usize>,
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

    let core = LoadStoreCoreChip::new(Rv32LoadStoreOpcode::CLASS_OFFSET);
    let adapter_width = BaseAir::<F>::width(adapter.air());
    let mut chip = Rv32LoadStoreChip::<F>::new(adapter, core, tester.offline_memory_mutex_arc());

    set_and_execute(
        &mut tester,
        &mut chip,
        &mut rng,
        opcode,
        rs1,
        imm,
        imm_sign,
        mem_as,
    );

    let modify_trace = |trace: &mut DenseMatrix<BabyBear>| {
        let mut trace_row = trace.row_slice(0).to_vec();
        let (_, core_row) = trace_row.split_at_mut(adapter_width);
        let core_cols: &mut LoadStoreCoreCols<F, RV32_REGISTER_NUM_LIMBS> = core_row.borrow_mut();
        if let Some(read_data) = read_data {
            core_cols.read_data = read_data.map(F::from_canonical_u32);
        }
        if let Some(prev_data) = prev_data {
            core_cols.prev_data = prev_data.map(F::from_canonical_u32);
        }
        if let Some(write_data) = write_data {
            core_cols.write_data = write_data.map(F::from_canonical_u32);
        }
        if let Some(flags) = flags {
            core_cols.flags = flags.map(F::from_canonical_u32);
        }
        if let Some(is_load) = is_load {
            core_cols.is_load = F::from_bool(is_load);
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
fn negative_wrong_opcode_tests() {
    run_negative_loadstore_test(
        LOADW,
        None,
        None,
        None,
        None,
        Some(false),
        None,
        None,
        None,
        None,
        VerificationError::OodEvaluationMismatch,
    );

    run_negative_loadstore_test(
        LOADBU,
        None,
        None,
        None,
        Some([0, 0, 0, 2]),
        None,
        Some([4, 0, 0, 0]),
        Some(1),
        None,
        None,
        VerificationError::OodEvaluationMismatch,
    );

    run_negative_loadstore_test(
        STOREH,
        None,
        None,
        None,
        Some([1, 0, 1, 0]),
        Some(true),
        Some([11, 169, 76, 28]),
        Some(37121),
        None,
        None,
        VerificationError::OodEvaluationMismatch,
    );
}

#[test]
fn negative_write_data_tests() {
    run_negative_loadstore_test(
        LOADHU,
        Some([175, 33, 198, 250]),
        Some([90, 121, 64, 205]),
        Some([175, 33, 0, 0]),
        Some([0, 2, 0, 0]),
        Some(true),
        Some([13, 11, 156, 23]),
        Some(43641),
        None,
        None,
        VerificationError::ChallengePhaseError,
    );

    run_negative_loadstore_test(
        STOREB,
        Some([175, 33, 198, 250]),
        Some([90, 121, 64, 205]),
        Some([175, 121, 64, 205]),
        Some([0, 0, 1, 1]),
        None,
        Some([45, 123, 87, 24]),
        Some(28122),
        Some(0),
        None,
        VerificationError::OodEvaluationMismatch,
    );
}

#[test]
fn negative_wrong_address_space_tests() {
    run_negative_loadstore_test(
        LOADW,
        None,
        None,
        None,
        None,
        None,
        None,
        None,
        None,
        Some(3),
        VerificationError::OodEvaluationMismatch,
    );
    run_negative_loadstore_test(
        LOADW,
        None,
        None,
        None,
        None,
        None,
        None,
        None,
        None,
        Some(4),
        VerificationError::OodEvaluationMismatch,
    );
    run_negative_loadstore_test(
        STOREW,
        None,
        None,
        None,
        None,
        None,
        None,
        None,
        None,
        Some(1),
        VerificationError::OodEvaluationMismatch,
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
    let core = LoadStoreCoreChip::new(Rv32LoadStoreOpcode::CLASS_OFFSET);
    let mut chip = Rv32LoadStoreChip::<F>::new(adapter, core, tester.offline_memory_mutex_arc());

    let num_tests: usize = 100;
    for _ in 0..num_tests {
        set_and_execute(
            &mut tester,
            &mut chip,
            &mut rng,
            LOADW,
            None,
            None,
            None,
            None,
        );
        set_and_execute(
            &mut tester,
            &mut chip,
            &mut rng,
            LOADBU,
            None,
            None,
            None,
            None,
        );
        set_and_execute(
            &mut tester,
            &mut chip,
            &mut rng,
            LOADHU,
            None,
            None,
            None,
            None,
        );
        set_and_execute(
            &mut tester,
            &mut chip,
            &mut rng,
            STOREW,
            None,
            None,
            None,
            None,
        );
        set_and_execute(
            &mut tester,
            &mut chip,
            &mut rng,
            STOREB,
            None,
            None,
            None,
            None,
        );
        set_and_execute(
            &mut tester,
            &mut chip,
            &mut rng,
            STOREH,
            None,
            None,
            None,
            None,
        );
    }
}

#[test]
fn run_loadw_storew_sanity_test() {
    let read_data = [138, 45, 202, 76].map(F::from_canonical_u32);
    let prev_data = [159, 213, 89, 34].map(F::from_canonical_u32);
    let store_write_data = run_write_data(STOREW, read_data, prev_data, 0);
    let load_write_data = run_write_data(LOADW, read_data, prev_data, 0);
    assert_eq!(store_write_data, read_data);
    assert_eq!(load_write_data, read_data);
}

#[test]
fn run_storeh_sanity_test() {
    let read_data = [250, 123, 67, 198].map(F::from_canonical_u32);
    let prev_data = [144, 56, 175, 92].map(F::from_canonical_u32);
    let write_data = run_write_data(STOREH, read_data, prev_data, 0);
    let write_data2 = run_write_data(STOREH, read_data, prev_data, 2);
    assert_eq!(write_data, [250, 123, 175, 92].map(F::from_canonical_u32));
    assert_eq!(write_data2, [144, 56, 250, 123].map(F::from_canonical_u32));
}

#[test]
fn run_storeb_sanity_test() {
    let read_data = [221, 104, 58, 147].map(F::from_canonical_u32);
    let prev_data = [199, 83, 243, 12].map(F::from_canonical_u32);
    let write_data = run_write_data(STOREB, read_data, prev_data, 0);
    let write_data1 = run_write_data(STOREB, read_data, prev_data, 1);
    let write_data2 = run_write_data(STOREB, read_data, prev_data, 2);
    let write_data3 = run_write_data(STOREB, read_data, prev_data, 3);
    assert_eq!(write_data, [221, 83, 243, 12].map(F::from_canonical_u32));
    assert_eq!(write_data1, [199, 221, 243, 12].map(F::from_canonical_u32));
    assert_eq!(write_data2, [199, 83, 221, 12].map(F::from_canonical_u32));
    assert_eq!(write_data3, [199, 83, 243, 221].map(F::from_canonical_u32));
}

#[test]
fn run_loadhu_sanity_test() {
    let read_data = [175, 33, 198, 250].map(F::from_canonical_u32);
    let prev_data = [90, 121, 64, 205].map(F::from_canonical_u32);
    let write_data = run_write_data(LOADHU, read_data, prev_data, 0);
    let write_data2 = run_write_data(LOADHU, read_data, prev_data, 2);
    assert_eq!(write_data, [175, 33, 0, 0].map(F::from_canonical_u32));
    assert_eq!(write_data2, [198, 250, 0, 0].map(F::from_canonical_u32));
}

#[test]
fn run_loadbu_sanity_test() {
    let read_data = [131, 74, 186, 29].map(F::from_canonical_u32);
    let prev_data = [142, 67, 210, 88].map(F::from_canonical_u32);
    let write_data = run_write_data(LOADBU, read_data, prev_data, 0);
    let write_data1 = run_write_data(LOADBU, read_data, prev_data, 1);
    let write_data2 = run_write_data(LOADBU, read_data, prev_data, 2);
    let write_data3 = run_write_data(LOADBU, read_data, prev_data, 3);
    assert_eq!(write_data, [131, 0, 0, 0].map(F::from_canonical_u32));
    assert_eq!(write_data1, [74, 0, 0, 0].map(F::from_canonical_u32));
    assert_eq!(write_data2, [186, 0, 0, 0].map(F::from_canonical_u32));
    assert_eq!(write_data3, [29, 0, 0, 0].map(F::from_canonical_u32));
}
