use std::{
    cell::RefCell,
    iter::zip,
    rc::Rc,
    sync::{Arc, Mutex},
};

use openvm_circuit_primitives::var_range::{
    SharedVariableRangeCheckerChip, VariableRangeCheckerBus,
};
use openvm_instructions::instruction::Instruction;
use openvm_stark_backend::{
    config::{StarkGenericConfig, Val},
    engine::VerificationData,
    interaction::BusIndex,
    p3_field::PrimeField32,
    p3_matrix::dense::{DenseMatrix, RowMajorMatrix},
    prover::types::AirProofInput,
    verifier::VerificationError,
    AirRef, Chip,
};
use openvm_stark_sdk::{
    config::{
        baby_bear_blake3::{BabyBearBlake3Config, BabyBearBlake3Engine},
        baby_bear_poseidon2::{BabyBearPoseidon2Config, BabyBearPoseidon2Engine},
        setup_tracing_with_log_level, FriParameters,
    },
    engine::{StarkEngine, StarkFriEngine},
    p3_baby_bear::BabyBear,
};
use program::ProgramTester;
use rand::{rngs::StdRng, RngCore, SeedableRng};
use tracing::Level;

use super::{ExecutionBus, InstructionExecutor, SystemPort};
use crate::{
    arch::{ExecutionState, MemoryConfig},
    system::{
        memory::{
            offline_checker::{MemoryBridge, MemoryBus},
            MemoryController, OfflineMemory,
        },
        poseidon2::Poseidon2PeripheryChip,
        program::ProgramBus,
    },
};

pub mod execution;
pub mod memory;
pub mod program;
pub mod test_adapter;

pub use execution::ExecutionTester;
pub use memory::MemoryTester;
pub use test_adapter::TestAdapterChip;

pub const EXECUTION_BUS: BusIndex = 0;
pub const MEMORY_BUS: BusIndex = 1;
pub const POSEIDON2_DIRECT_BUS: BusIndex = 6;
pub const READ_INSTRUCTION_BUS: BusIndex = 8;
pub const BITWISE_OP_LOOKUP_BUS: BusIndex = 9;
pub const BYTE_XOR_BUS: BusIndex = 10;
pub const RANGE_TUPLE_CHECKER_BUS: BusIndex = 11;
pub const MEMORY_MERKLE_BUS: BusIndex = 12;

const RANGE_CHECKER_BUS: BusIndex = 4;

pub struct VmChipTestBuilder<F: PrimeField32> {
    pub memory: MemoryTester<F>,
    pub execution: ExecutionTester<F>,
    pub program: ProgramTester<F>,
    rng: StdRng,
    default_register: usize,
    default_pointer: usize,
}

impl<F: PrimeField32> VmChipTestBuilder<F> {
    pub fn new(
        memory_controller: Rc<RefCell<MemoryController<F>>>,
        execution_bus: ExecutionBus,
        program_bus: ProgramBus,
        rng: StdRng,
    ) -> Self {
        setup_tracing_with_log_level(Level::WARN);
        Self {
            memory: MemoryTester::new(memory_controller),
            execution: ExecutionTester::new(execution_bus),
            program: ProgramTester::new(program_bus),
            rng,
            default_register: 0,
            default_pointer: 0,
        }
    }

    // Passthrough functions from ExecutionTester and MemoryTester for better dev-ex
    pub fn execute<E: InstructionExecutor<F>>(
        &mut self,
        executor: &mut E,
        instruction: &Instruction<F>,
    ) {
        let initial_pc = self.next_elem_size_u32();
        self.execute_with_pc(executor, instruction, initial_pc);
    }

    pub fn execute_with_pc<E: InstructionExecutor<F>>(
        &mut self,
        executor: &mut E,
        instruction: &Instruction<F>,
        initial_pc: u32,
    ) {
        let initial_state = ExecutionState {
            pc: initial_pc,
            timestamp: self.memory.controller.borrow().timestamp(),
        };
        tracing::debug!(?initial_state.timestamp);

        let final_state = executor
            .execute(
                &mut *self.memory.controller.borrow_mut(),
                instruction,
                initial_state,
            )
            .expect("Expected the execution not to fail");

        self.program.execute(instruction, &initial_state);
        self.execution.execute(initial_state, final_state);
    }

    fn next_elem_size_u32(&mut self) -> u32 {
        self.rng.next_u32() % (1 << (F::bits() - 2))
    }

    pub fn read_cell(&mut self, address_space: usize, pointer: usize) -> F {
        self.memory.read_cell(address_space, pointer)
    }

    pub fn write_cell(&mut self, address_space: usize, pointer: usize, value: F) {
        self.memory.write_cell(address_space, pointer, value);
    }

    pub fn read<const N: usize>(&mut self, address_space: usize, pointer: usize) -> [F; N] {
        self.memory.read(address_space, pointer)
    }

    pub fn write<const N: usize>(&mut self, address_space: usize, pointer: usize, value: [F; N]) {
        self.memory.write(address_space, pointer, value);
    }

    pub fn write_usize<const N: usize>(
        &mut self,
        address_space: usize,
        pointer: usize,
        value: [usize; N],
    ) {
        self.memory
            .write(address_space, pointer, value.map(F::from_canonical_usize));
    }

    pub fn write_heap<const NUM_LIMBS: usize>(
        &mut self,
        register: usize,
        pointer: usize,
        writes: Vec<[F; NUM_LIMBS]>,
    ) {
        self.write(1usize, register, [F::from_canonical_usize(pointer)]);
        for (i, &write) in writes.iter().enumerate() {
            self.write(2usize, pointer + i * NUM_LIMBS, write);
        }
    }

    pub fn system_port(&self) -> SystemPort {
        SystemPort {
            execution_bus: self.execution.bus,
            program_bus: self.program.bus,
            memory_bridge: self.memory_bridge(),
        }
    }

    pub fn execution_bus(&self) -> ExecutionBus {
        self.execution.bus
    }

    pub fn program_bus(&self) -> ProgramBus {
        self.program.bus
    }

    pub fn memory_bus(&self) -> MemoryBus {
        self.memory.bus
    }

    pub fn memory_controller(&self) -> Rc<RefCell<MemoryController<F>>> {
        self.memory.controller.clone()
    }

    pub fn range_checker(&self) -> SharedVariableRangeCheckerChip {
        self.memory.controller.borrow().range_checker.clone()
    }

    pub fn memory_bridge(&self) -> MemoryBridge {
        self.memory.controller.borrow().memory_bridge()
    }

    pub fn address_bits(&self) -> usize {
        self.memory.controller.borrow().mem_config.pointer_max_bits
    }

    pub fn offline_memory_mutex_arc(&self) -> Arc<Mutex<OfflineMemory<F>>> {
        self.memory_controller().borrow().offline_memory().clone()
    }

    pub fn get_default_register(&mut self, increment: usize) -> usize {
        self.default_register += increment;
        self.default_register - increment
    }

    pub fn get_default_pointer(&mut self, increment: usize) -> usize {
        self.default_pointer += increment;
        self.default_pointer - increment
    }

    pub fn write_heap_pointer_default(
        &mut self,
        reg_increment: usize,
        pointer_increment: usize,
    ) -> (usize, usize) {
        let register = self.get_default_register(reg_increment);
        let pointer = self.get_default_pointer(pointer_increment);
        self.write(1, register, pointer.to_le_bytes().map(F::from_canonical_u8));
        (register, pointer)
    }

    pub fn write_heap_default<const NUM_LIMBS: usize>(
        &mut self,
        reg_increment: usize,
        pointer_increment: usize,
        writes: Vec<[F; NUM_LIMBS]>,
    ) -> (usize, usize) {
        let register = self.get_default_register(reg_increment);
        let pointer = self.get_default_pointer(pointer_increment);
        self.write_heap(register, pointer, writes);
        (register, pointer)
    }
}

// Use Blake3 as hash for faster tests.
type TestSC = BabyBearBlake3Config;

impl VmChipTestBuilder<BabyBear> {
    pub fn build(self) -> VmChipTester<TestSC> {
        self.memory
            .controller
            .borrow_mut()
            .finalize(None::<&mut Poseidon2PeripheryChip<BabyBear>>);
        let tester = VmChipTester {
            memory: Some(self.memory),
            ..Default::default()
        };
        let tester = tester.load(self.execution);
        tester.load(self.program)
    }
    pub fn build_babybear_poseidon2(self) -> VmChipTester<BabyBearPoseidon2Config> {
        self.memory
            .controller
            .borrow_mut()
            .finalize(None::<&mut Poseidon2PeripheryChip<BabyBear>>);
        let tester = VmChipTester {
            memory: Some(self.memory),
            ..Default::default()
        };
        let tester = tester.load(self.execution);
        tester.load(self.program)
    }
}

impl<F: PrimeField32> Default for VmChipTestBuilder<F> {
    fn default() -> Self {
        let mem_config = MemoryConfig::default();
        let range_checker = SharedVariableRangeCheckerChip::new(VariableRangeCheckerBus::new(
            RANGE_CHECKER_BUS,
            mem_config.decomp,
        ));
        let memory_controller = MemoryController::with_volatile_memory(
            MemoryBus::new(MEMORY_BUS),
            mem_config,
            range_checker,
        );
        Self {
            memory: MemoryTester::new(Rc::new(RefCell::new(memory_controller))),
            execution: ExecutionTester::new(ExecutionBus::new(EXECUTION_BUS)),
            program: ProgramTester::new(ProgramBus::new(READ_INSTRUCTION_BUS)),
            rng: StdRng::seed_from_u64(0),
            default_register: 0,
            default_pointer: 0,
        }
    }
}

pub struct VmChipTester<SC: StarkGenericConfig> {
    pub memory: Option<MemoryTester<Val<SC>>>,
    pub air_proof_inputs: Vec<(AirRef<SC>, AirProofInput<SC>)>,
}

impl<SC: StarkGenericConfig> Default for VmChipTester<SC> {
    fn default() -> Self {
        Self {
            memory: None,
            air_proof_inputs: vec![],
        }
    }
}

impl<SC: StarkGenericConfig> VmChipTester<SC>
where
    Val<SC>: PrimeField32,
{
    pub fn load<C: Chip<SC>>(mut self, chip: C) -> Self {
        if chip.current_trace_height() > 0 {
            let air = chip.air();
            let air_proof_input = chip.generate_air_proof_input();
            tracing::debug!("Generated air proof input for {}", air.name());
            self.air_proof_inputs.push((air, air_proof_input));
        }

        self
    }

    pub fn finalize(mut self) -> Self {
        if let Some(memory_tester) = self.memory.take() {
            let memory_controller = memory_tester.controller.clone();
            let range_checker = memory_controller.borrow().range_checker.clone();
            self = self.load(memory_tester); // dummy memory interactions
            {
                let airs = memory_controller.borrow().airs();
                let air_proof_inputs = Rc::try_unwrap(memory_controller)
                    .unwrap_or_else(|_| panic!("Memory controller was not dropped"))
                    .into_inner()
                    .generate_air_proof_inputs();
                self.air_proof_inputs.extend(
                    zip(airs, air_proof_inputs).filter(|(_, input)| input.main_trace_height() > 0),
                );
            }
            self = self.load(range_checker); // this must be last because other trace generation
                                             // mutates its state
        }
        self
    }

    pub fn load_air_proof_input(
        mut self,
        air_proof_input: (AirRef<SC>, AirProofInput<SC>),
    ) -> Self {
        self.air_proof_inputs.push(air_proof_input);
        self
    }

    pub fn load_with_custom_trace<C: Chip<SC>>(
        mut self,
        chip: C,
        trace: RowMajorMatrix<Val<SC>>,
    ) -> Self {
        let air = chip.air();
        let mut air_proof_input = chip.generate_air_proof_input();
        air_proof_input.raw.common_main = Some(trace);
        self.air_proof_inputs.push((air, air_proof_input));
        self
    }

    pub fn load_and_prank_trace<C: Chip<SC>, P>(mut self, chip: C, modify_trace: P) -> Self
    where
        P: Fn(&mut DenseMatrix<Val<SC>>),
    {
        let air = chip.air();
        let mut air_proof_input = chip.generate_air_proof_input();
        let trace = air_proof_input.raw.common_main.as_mut().unwrap();
        modify_trace(trace);
        self.air_proof_inputs.push((air, air_proof_input));
        self
    }

    /// Given a function to produce an engine from the max trace height,
    /// runs a simple test on that engine
    pub fn test<E: StarkEngine<SC>, P: Fn() -> E>(
        &self, // do no take ownership so it's easier to prank
        engine_provider: P,
    ) -> Result<VerificationData<SC>, VerificationError> {
        assert!(self.memory.is_none(), "Memory must be finalized");
        let (airs, air_proof_inputs) = self.air_proof_inputs.iter().cloned().unzip();
        engine_provider().run_test_impl(airs, air_proof_inputs)
    }
}

impl VmChipTester<BabyBearPoseidon2Config> {
    pub fn simple_test(
        &self,
    ) -> Result<VerificationData<BabyBearPoseidon2Config>, VerificationError> {
        self.test(|| BabyBearPoseidon2Engine::new(FriParameters::new_for_testing(1)))
    }

    pub fn simple_test_with_expected_error(&self, expected_error: VerificationError) {
        let msg = format!(
            "Expected verification to fail with {:?}, but it didn't",
            &expected_error
        );
        let result = self.simple_test();
        assert_eq!(result.err(), Some(expected_error), "{}", msg);
    }
}

impl VmChipTester<BabyBearBlake3Config> {
    pub fn simple_test(&self) -> Result<VerificationData<BabyBearBlake3Config>, VerificationError> {
        self.test(|| BabyBearBlake3Engine::new(FriParameters::new_for_testing(1)))
    }

    pub fn simple_test_with_expected_error(&self, expected_error: VerificationError) {
        let msg = format!(
            "Expected verification to fail with {:?}, but it didn't",
            &expected_error
        );
        let result = self.simple_test();
        assert_eq!(result.err(), Some(expected_error), "{}", msg);
    }
}
