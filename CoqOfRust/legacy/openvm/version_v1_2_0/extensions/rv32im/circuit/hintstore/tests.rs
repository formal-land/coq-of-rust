use std::{
    array,
    borrow::BorrowMut,
    sync::{Arc, Mutex},
};

use openvm_circuit::arch::{
    testing::{memory::gen_pointer, VmChipTestBuilder, BITWISE_OP_LOOKUP_BUS},
    Streams,
};
use openvm_circuit_primitives::bitwise_op_lookup::{
    BitwiseOperationLookupBus, SharedBitwiseOperationLookupChip,
};
use openvm_instructions::{
    instruction::Instruction,
    riscv::{RV32_CELL_BITS, RV32_REGISTER_NUM_LIMBS},
    VmOpcode,
};
use openvm_rv32im_transpiler::Rv32HintStoreOpcode::{self, *};
use openvm_stark_backend::{
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

use super::{Rv32HintStoreChip, Rv32HintStoreCols};
use crate::adapters::decompose;

type F = BabyBear;

fn set_and_execute(
    tester: &mut VmChipTestBuilder<F>,
    chip: &mut Rv32HintStoreChip<F>,
    rng: &mut StdRng,
    opcode: Rv32HintStoreOpcode,
) {
    let mem_ptr = rng.gen_range(
        0..(1
            << (tester
                .memory_controller()
                .borrow()
                .mem_config()
                .pointer_max_bits
                - 2)),
    ) << 2;
    let b = gen_pointer(rng, 4);

    tester.write(1, b, decompose(mem_ptr));

    let read_data: [F; RV32_REGISTER_NUM_LIMBS] =
        array::from_fn(|_| F::from_canonical_u32(rng.gen_range(0..(1 << RV32_CELL_BITS))));
    for data in read_data {
        chip.streams
            .get()
            .unwrap()
            .lock()
            .unwrap()
            .hint_stream
            .push_back(data);
    }

    tester.execute(
        chip,
        &Instruction::from_usize(VmOpcode::from_usize(opcode as usize), [0, b, 0, 1, 2]),
    );

    let write_data = read_data;
    assert_eq!(write_data, tester.read::<4>(2, mem_ptr as usize));
}

fn set_and_execute_buffer(
    tester: &mut VmChipTestBuilder<F>,
    chip: &mut Rv32HintStoreChip<F>,
    rng: &mut StdRng,
    opcode: Rv32HintStoreOpcode,
) {
    let mem_ptr = rng.gen_range(
        0..(1
            << (tester
                .memory_controller()
                .borrow()
                .mem_config()
                .pointer_max_bits
                - 2)),
    ) << 2;
    let b = gen_pointer(rng, 4);

    tester.write(1, b, decompose(mem_ptr));

    let num_words = rng.gen_range(1..20);
    let a = gen_pointer(rng, 4);
    tester.write(1, a, decompose(num_words));

    let data: Vec<[F; RV32_REGISTER_NUM_LIMBS]> = (0..num_words)
        .map(|_| array::from_fn(|_| F::from_canonical_u32(rng.gen_range(0..(1 << RV32_CELL_BITS)))))
        .collect();
    for i in 0..num_words {
        for datum in data[i as usize] {
            chip.streams
                .get()
                .unwrap()
                .lock()
                .unwrap()
                .hint_stream
                .push_back(datum);
        }
    }

    tester.execute(
        chip,
        &Instruction::from_usize(VmOpcode::from_usize(opcode as usize), [a, b, 0, 1, 2]),
    );

    for i in 0..num_words {
        assert_eq!(
            data[i as usize],
            tester.read::<4>(2, mem_ptr as usize + (i as usize * RV32_REGISTER_NUM_LIMBS))
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
fn rand_hintstore_test() {
    setup_tracing();
    let mut rng = create_seeded_rng();
    let mut tester = VmChipTestBuilder::default();

    let bitwise_bus = BitwiseOperationLookupBus::new(BITWISE_OP_LOOKUP_BUS);
    let bitwise_chip = SharedBitwiseOperationLookupChip::<RV32_CELL_BITS>::new(bitwise_bus);

    let range_checker_chip = tester.memory_controller().borrow().range_checker.clone();

    let mut chip = Rv32HintStoreChip::<F>::new(
        tester.execution_bus(),
        tester.program_bus(),
        bitwise_chip.clone(),
        tester.memory_bridge(),
        tester.offline_memory_mutex_arc(),
        tester.address_bits(),
        0,
    );
    chip.set_streams(Arc::new(Mutex::new(Streams::default())));

    let num_tests: usize = 8;
    for _ in 0..num_tests {
        if rng.gen_bool(0.5) {
            set_and_execute(&mut tester, &mut chip, &mut rng, HINT_STOREW);
        } else {
            set_and_execute_buffer(&mut tester, &mut chip, &mut rng, HINT_BUFFER);
        }
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
fn run_negative_hintstore_test(
    opcode: Rv32HintStoreOpcode,
    data: Option<[u32; RV32_REGISTER_NUM_LIMBS]>,
    expected_error: VerificationError,
) {
    let mut rng = create_seeded_rng();
    let mut tester = VmChipTestBuilder::default();

    let bitwise_bus = BitwiseOperationLookupBus::new(BITWISE_OP_LOOKUP_BUS);
    let bitwise_chip = SharedBitwiseOperationLookupChip::<RV32_CELL_BITS>::new(bitwise_bus);

    let range_checker_chip = tester.memory_controller().borrow().range_checker.clone();

    let mut chip = Rv32HintStoreChip::<F>::new(
        tester.execution_bus(),
        tester.program_bus(),
        bitwise_chip.clone(),
        tester.memory_bridge(),
        tester.offline_memory_mutex_arc(),
        tester.address_bits(),
        0,
    );
    chip.set_streams(Arc::new(Mutex::new(Streams::default())));

    set_and_execute(&mut tester, &mut chip, &mut rng, opcode);

    let modify_trace = |trace: &mut DenseMatrix<BabyBear>| {
        let mut trace_row = trace.row_slice(0).to_vec();
        let cols: &mut Rv32HintStoreCols<F> = trace_row.as_mut_slice().borrow_mut();
        if let Some(data) = data {
            cols.data = data.map(F::from_canonical_u32);
        }
        *trace = RowMajorMatrix::new(trace_row, trace.width());
    };

    drop(range_checker_chip);
    disable_debug_builder();
    let tester = tester
        .build()
        .load_and_prank_trace(chip, modify_trace)
        .load(bitwise_chip)
        .finalize();
    tester.simple_test_with_expected_error(expected_error);
}

#[test]
fn negative_hintstore_tests() {
    run_negative_hintstore_test(
        HINT_STOREW,
        Some([92, 187, 45, 280]),
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

    let bitwise_bus = BitwiseOperationLookupBus::new(BITWISE_OP_LOOKUP_BUS);
    let bitwise_chip = SharedBitwiseOperationLookupChip::<RV32_CELL_BITS>::new(bitwise_bus);

    let mut chip = Rv32HintStoreChip::<F>::new(
        tester.execution_bus(),
        tester.program_bus(),
        bitwise_chip.clone(),
        tester.memory_bridge(),
        tester.offline_memory_mutex_arc(),
        tester.address_bits(),
        0,
    );
    chip.set_streams(Arc::new(Mutex::new(Streams::default())));

    let num_tests: usize = 100;
    for _ in 0..num_tests {
        set_and_execute(&mut tester, &mut chip, &mut rng, HINT_STOREW);
    }
}
