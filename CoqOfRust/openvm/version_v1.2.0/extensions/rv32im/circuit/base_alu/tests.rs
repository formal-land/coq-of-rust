use std::borrow::BorrowMut;

use openvm_circuit::{
    arch::{
        testing::{TestAdapterChip, VmChipTestBuilder, BITWISE_OP_LOOKUP_BUS},
        AdapterRuntimeContext, BasicAdapterInterface, ExecutionBridge, ExecutionState,
        MinimalInstruction, Result, VmAdapterChip, VmAdapterInterface, VmChipWrapper,
    },
    system::memory::{MemoryController, OfflineMemory},
    utils::generate_long_number,
};
use openvm_circuit_primitives::bitwise_op_lookup::{
    BitwiseOperationLookupBus, SharedBitwiseOperationLookupChip,
};
use openvm_instructions::{instruction::Instruction, LocalOpcode};
use openvm_rv32im_transpiler::BaseAluOpcode;
use openvm_stark_backend::{
    p3_air::BaseAir,
    p3_field::{Field, FieldAlgebra, PrimeField32},
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

use super::{core::run_alu, BaseAluCoreChip, Rv32BaseAluChip};
use crate::{
    adapters::{
        Rv32BaseAluAdapterAir, Rv32BaseAluAdapterChip, Rv32BaseAluReadRecord,
        Rv32BaseAluWriteRecord, RV32_CELL_BITS, RV32_REGISTER_NUM_LIMBS,
    },
    base_alu::BaseAluCoreCols,
    test_utils::{generate_rv32_is_type_immediate, rv32_rand_write_register_or_imm},
};

type F = BabyBear;

//////////////////////////////////////////////////////////////////////////////////////
// POSITIVE TESTS
//
// Randomly generate computations and execute, ensuring that the generated trace
// passes all constraints.
//////////////////////////////////////////////////////////////////////////////////////

fn run_rv32_alu_rand_test(opcode: BaseAluOpcode, num_ops: usize) {
    let mut rng = create_seeded_rng();
    let bitwise_bus = BitwiseOperationLookupBus::new(BITWISE_OP_LOOKUP_BUS);
    let bitwise_chip = SharedBitwiseOperationLookupChip::<RV32_CELL_BITS>::new(bitwise_bus);

    let mut tester = VmChipTestBuilder::default();
    let mut chip = Rv32BaseAluChip::<F>::new(
        Rv32BaseAluAdapterChip::new(
            tester.execution_bus(),
            tester.program_bus(),
            tester.memory_bridge(),
            bitwise_chip.clone(),
        ),
        BaseAluCoreChip::new(bitwise_chip.clone(), BaseAluOpcode::CLASS_OFFSET),
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

        let a = run_alu::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(opcode, &b, &c)
            .map(F::from_canonical_u32);
        assert_eq!(a, tester.read::<RV32_REGISTER_NUM_LIMBS>(1, rd))
    }

    let tester = tester.build().load(chip).load(bitwise_chip).finalize();
    tester.simple_test().expect("Verification failed");
}

#[test]
fn rv32_alu_add_rand_test() {
    run_rv32_alu_rand_test(BaseAluOpcode::ADD, 100);
}

#[test]
fn rv32_alu_sub_rand_test() {
    run_rv32_alu_rand_test(BaseAluOpcode::SUB, 100);
}

#[test]
fn rv32_alu_xor_rand_test() {
    run_rv32_alu_rand_test(BaseAluOpcode::XOR, 100);
}

#[test]
fn rv32_alu_or_rand_test() {
    run_rv32_alu_rand_test(BaseAluOpcode::OR, 100);
}

#[test]
fn rv32_alu_and_rand_test() {
    run_rv32_alu_rand_test(BaseAluOpcode::AND, 100);
}

//////////////////////////////////////////////////////////////////////////////////////
// NEGATIVE TESTS
//
// Given a fake trace of a single operation, setup a chip and run the test. We replace
// the write part of the trace and check that the core chip throws the expected error.
// A dummy adapter is used so memory interactions don't indirectly cause false passes.
//////////////////////////////////////////////////////////////////////////////////////

type Rv32BaseAluTestChip<F> =
    VmChipWrapper<F, TestAdapterChip<F>, BaseAluCoreChip<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>>;

#[allow(clippy::too_many_arguments)]
fn run_rv32_alu_negative_test(
    opcode: BaseAluOpcode,
    a: [u32; RV32_REGISTER_NUM_LIMBS],
    b: [u32; RV32_REGISTER_NUM_LIMBS],
    c: [u32; RV32_REGISTER_NUM_LIMBS],
    interaction_error: bool,
) {
    let bitwise_bus = BitwiseOperationLookupBus::new(BITWISE_OP_LOOKUP_BUS);
    let bitwise_chip = SharedBitwiseOperationLookupChip::<RV32_CELL_BITS>::new(bitwise_bus);

    let mut tester: VmChipTestBuilder<BabyBear> = VmChipTestBuilder::default();
    let mut chip = Rv32BaseAluTestChip::<F>::new(
        TestAdapterChip::new(
            vec![[b.map(F::from_canonical_u32), c.map(F::from_canonical_u32)].concat()],
            vec![None],
            ExecutionBridge::new(tester.execution_bus(), tester.program_bus()),
        ),
        BaseAluCoreChip::new(bitwise_chip.clone(), BaseAluOpcode::CLASS_OFFSET),
        tester.offline_memory_mutex_arc(),
    );

    tester.execute(
        &mut chip,
        &Instruction::from_usize(opcode.global_opcode(), [0, 0, 0, 1, 1]),
    );

    let trace_width = chip.trace_width();
    let adapter_width = BaseAir::<F>::width(chip.adapter.air());

    if (opcode == BaseAluOpcode::ADD || opcode == BaseAluOpcode::SUB)
        && a.iter().all(|&a_val| a_val < (1 << RV32_CELL_BITS))
    {
        bitwise_chip.clear();
        for a_val in a {
            bitwise_chip.request_xor(a_val, a_val);
        }
    }

    let modify_trace = |trace: &mut DenseMatrix<BabyBear>| {
        let mut values = trace.row_slice(0).to_vec();
        let cols: &mut BaseAluCoreCols<F, RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS> =
            values.split_at_mut(adapter_width).1.borrow_mut();
        cols.a = a.map(F::from_canonical_u32);
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
fn rv32_alu_add_wrong_negative_test() {
    run_rv32_alu_negative_test(
        BaseAluOpcode::ADD,
        [246, 0, 0, 0],
        [250, 0, 0, 0],
        [250, 0, 0, 0],
        false,
    );
}

#[test]
fn rv32_alu_add_out_of_range_negative_test() {
    run_rv32_alu_negative_test(
        BaseAluOpcode::ADD,
        [500, 0, 0, 0],
        [250, 0, 0, 0],
        [250, 0, 0, 0],
        true,
    );
}

#[test]
fn rv32_alu_sub_wrong_negative_test() {
    run_rv32_alu_negative_test(
        BaseAluOpcode::SUB,
        [255, 0, 0, 0],
        [1, 0, 0, 0],
        [2, 0, 0, 0],
        false,
    );
}

#[test]
fn rv32_alu_sub_out_of_range_negative_test() {
    run_rv32_alu_negative_test(
        BaseAluOpcode::SUB,
        [F::NEG_ONE.as_canonical_u32(), 0, 0, 0],
        [1, 0, 0, 0],
        [2, 0, 0, 0],
        true,
    );
}

#[test]
fn rv32_alu_xor_wrong_negative_test() {
    run_rv32_alu_negative_test(
        BaseAluOpcode::XOR,
        [255, 255, 255, 255],
        [0, 0, 1, 0],
        [255, 255, 255, 255],
        true,
    );
}

#[test]
fn rv32_alu_or_wrong_negative_test() {
    run_rv32_alu_negative_test(
        BaseAluOpcode::OR,
        [255, 255, 255, 255],
        [255, 255, 255, 254],
        [0, 0, 0, 0],
        true,
    );
}

#[test]
fn rv32_alu_and_wrong_negative_test() {
    run_rv32_alu_negative_test(
        BaseAluOpcode::AND,
        [255, 255, 255, 255],
        [0, 0, 1, 0],
        [0, 0, 0, 0],
        true,
    );
}

///////////////////////////////////////////////////////////////////////////////////////
/// SANITY TESTS
///
/// Ensure that solve functions produce the correct results.
///////////////////////////////////////////////////////////////////////////////////////

#[test]
fn run_add_sanity_test() {
    let x: [u32; RV32_REGISTER_NUM_LIMBS] = [229, 33, 29, 111];
    let y: [u32; RV32_REGISTER_NUM_LIMBS] = [50, 171, 44, 194];
    let z: [u32; RV32_REGISTER_NUM_LIMBS] = [23, 205, 73, 49];
    let result = run_alu::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(BaseAluOpcode::ADD, &x, &y);
    for i in 0..RV32_REGISTER_NUM_LIMBS {
        assert_eq!(z[i], result[i])
    }
}

#[test]
fn run_sub_sanity_test() {
    let x: [u32; RV32_REGISTER_NUM_LIMBS] = [229, 33, 29, 111];
    let y: [u32; RV32_REGISTER_NUM_LIMBS] = [50, 171, 44, 194];
    let z: [u32; RV32_REGISTER_NUM_LIMBS] = [179, 118, 240, 172];
    let result = run_alu::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(BaseAluOpcode::SUB, &x, &y);
    for i in 0..RV32_REGISTER_NUM_LIMBS {
        assert_eq!(z[i], result[i])
    }
}

#[test]
fn run_xor_sanity_test() {
    let x: [u32; RV32_REGISTER_NUM_LIMBS] = [229, 33, 29, 111];
    let y: [u32; RV32_REGISTER_NUM_LIMBS] = [50, 171, 44, 194];
    let z: [u32; RV32_REGISTER_NUM_LIMBS] = [215, 138, 49, 173];
    let result = run_alu::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(BaseAluOpcode::XOR, &x, &y);
    for i in 0..RV32_REGISTER_NUM_LIMBS {
        assert_eq!(z[i], result[i])
    }
}

#[test]
fn run_or_sanity_test() {
    let x: [u32; RV32_REGISTER_NUM_LIMBS] = [229, 33, 29, 111];
    let y: [u32; RV32_REGISTER_NUM_LIMBS] = [50, 171, 44, 194];
    let z: [u32; RV32_REGISTER_NUM_LIMBS] = [247, 171, 61, 239];
    let result = run_alu::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(BaseAluOpcode::OR, &x, &y);
    for i in 0..RV32_REGISTER_NUM_LIMBS {
        assert_eq!(z[i], result[i])
    }
}

#[test]
fn run_and_sanity_test() {
    let x: [u32; RV32_REGISTER_NUM_LIMBS] = [229, 33, 29, 111];
    let y: [u32; RV32_REGISTER_NUM_LIMBS] = [50, 171, 44, 194];
    let z: [u32; RV32_REGISTER_NUM_LIMBS] = [32, 33, 12, 66];
    let result = run_alu::<RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS>(BaseAluOpcode::AND, &x, &y);
    for i in 0..RV32_REGISTER_NUM_LIMBS {
        assert_eq!(z[i], result[i])
    }
}

//////////////////////////////////////////////////////////////////////////////////////
// ADAPTER TESTS
//
// Ensure that the adapter is correct.
//////////////////////////////////////////////////////////////////////////////////////

// A pranking chip where `preprocess` can have `rs2` limbs that overflow.
struct Rv32BaseAluAdapterTestChip<F: Field>(Rv32BaseAluAdapterChip<F>);

impl<F: PrimeField32> VmAdapterChip<F> for Rv32BaseAluAdapterTestChip<F> {
    type ReadRecord = Rv32BaseAluReadRecord<F>;
    type WriteRecord = Rv32BaseAluWriteRecord<F>;
    type Air = Rv32BaseAluAdapterAir;
    type Interface = BasicAdapterInterface<
        F,
        MinimalInstruction<F>,
        2,
        1,
        RV32_REGISTER_NUM_LIMBS,
        RV32_REGISTER_NUM_LIMBS,
    >;

    fn preprocess(
        &mut self,
        memory: &mut MemoryController<F>,
        instruction: &Instruction<F>,
    ) -> Result<(
        <Self::Interface as VmAdapterInterface<F>>::Reads,
        Self::ReadRecord,
    )> {
        let Instruction { b, c, d, e, .. } = *instruction;

        let rs1 = memory.read::<RV32_REGISTER_NUM_LIMBS>(d, b);
        let (rs2, rs2_data, rs2_imm) = if e.is_zero() {
            let c_u32 = c.as_canonical_u32();
            memory.increment_timestamp();
            let mask1 = (1 << 9) - 1;
            let mask2 = (1 << 3) - 2;
            (
                None,
                [
                    (c_u32 & mask1) as u16,
                    ((c_u32 >> 8) & mask2) as u16,
                    (c_u32 >> 16) as u16,
                    (c_u32 >> 16) as u16,
                ]
                .map(F::from_canonical_u16),
                c,
            )
        } else {
            let rs2_read = memory.read::<RV32_REGISTER_NUM_LIMBS>(e, c);
            (Some(rs2_read.0), rs2_read.1, F::ZERO)
        };

        Ok((
            [rs1.1, rs2_data],
            Self::ReadRecord {
                rs1: rs1.0,
                rs2,
                rs2_imm,
            },
        ))
    }

    fn postprocess(
        &mut self,
        memory: &mut MemoryController<F>,
        instruction: &Instruction<F>,
        from_state: ExecutionState<u32>,
        output: AdapterRuntimeContext<F, Self::Interface>,
        _read_record: &Self::ReadRecord,
    ) -> Result<(ExecutionState<u32>, Self::WriteRecord)> {
        self.0
            .postprocess(memory, instruction, from_state, output, _read_record)
    }

    fn generate_trace_row(
        &self,
        row_slice: &mut [F],
        read_record: Self::ReadRecord,
        write_record: Self::WriteRecord,
        memory: &OfflineMemory<F>,
    ) {
        self.0
            .generate_trace_row(row_slice, read_record, write_record, memory)
    }

    fn air(&self) -> &Self::Air {
        self.0.air()
    }
}

#[test]
fn rv32_alu_adapter_unconstrained_imm_limb_test() {
    let mut rng = create_seeded_rng();
    let bitwise_bus = BitwiseOperationLookupBus::new(BITWISE_OP_LOOKUP_BUS);
    let bitwise_chip = SharedBitwiseOperationLookupChip::<RV32_CELL_BITS>::new(bitwise_bus);

    let mut tester = VmChipTestBuilder::default();
    let mut chip = VmChipWrapper::new(
        Rv32BaseAluAdapterTestChip(Rv32BaseAluAdapterChip::new(
            tester.execution_bus(),
            tester.program_bus(),
            tester.memory_bridge(),
            bitwise_chip.clone(),
        )),
        BaseAluCoreChip::new(bitwise_chip.clone(), BaseAluOpcode::CLASS_OFFSET),
        tester.offline_memory_mutex_arc(),
    );

    let b = [0, 0, 0, 0];
    let (c_imm, c) = {
        let imm = (1 << 11) - 1;
        let fake_c = [(1 << 9) - 1, (1 << 3) - 2, 0, 0];
        (Some(imm), fake_c)
    };

    let (instruction, _rd) = rv32_rand_write_register_or_imm(
        &mut tester,
        b,
        c,
        c_imm,
        BaseAluOpcode::ADD.global_opcode().as_usize(),
        &mut rng,
    );
    tester.execute(&mut chip, &instruction);

    disable_debug_builder();
    let tester = tester.build().load(chip).load(bitwise_chip).finalize();
    tester.simple_test_with_expected_error(VerificationError::ChallengePhaseError);
}

#[test]
fn rv32_alu_adapter_unconstrained_rs2_read_test() {
    let mut rng = create_seeded_rng();
    let bitwise_bus = BitwiseOperationLookupBus::new(BITWISE_OP_LOOKUP_BUS);
    let bitwise_chip = SharedBitwiseOperationLookupChip::<RV32_CELL_BITS>::new(bitwise_bus);

    let mut tester = VmChipTestBuilder::default();
    let mut chip = Rv32BaseAluChip::<F>::new(
        Rv32BaseAluAdapterChip::new(
            tester.execution_bus(),
            tester.program_bus(),
            tester.memory_bridge(),
            bitwise_chip.clone(),
        ),
        BaseAluCoreChip::new(bitwise_chip.clone(), BaseAluOpcode::CLASS_OFFSET),
        tester.offline_memory_mutex_arc(),
    );

    let b = [1, 1, 1, 1];
    let c = [1, 1, 1, 1];
    let (instruction, _rd) = rv32_rand_write_register_or_imm(
        &mut tester,
        b,
        c,
        None,
        BaseAluOpcode::ADD.global_opcode().as_usize(),
        &mut rng,
    );
    tester.execute(&mut chip, &instruction);

    let trace_width = chip.trace_width();
    let adapter_width = BaseAir::<F>::width(chip.adapter.air());

    let modify_trace = |trace: &mut DenseMatrix<BabyBear>| {
        let mut values = trace.row_slice(0).to_vec();
        let mut dummy_values = values.clone();
        let cols: &mut BaseAluCoreCols<F, RV32_REGISTER_NUM_LIMBS, RV32_CELL_BITS> =
            dummy_values.split_at_mut(adapter_width).1.borrow_mut();
        cols.opcode_add_flag = F::ZERO;
        values.extend(dummy_values);
        *trace = RowMajorMatrix::new(values, trace_width);
    };

    disable_debug_builder();
    let tester = tester
        .build()
        .load_and_prank_trace(chip, modify_trace)
        .load(bitwise_chip)
        .finalize();
    tester.simple_test_with_expected_error(VerificationError::OodEvaluationMismatch);
}
