use std::{cell::RefCell, rc::Rc};

use openvm_circuit_primitives_derive::AlignedBorrow;
use openvm_instructions::{
    instruction::Instruction, program::DEFAULT_PC_STEP, PhantomDiscriminant, VmOpcode,
};
use openvm_stark_backend::{
    interaction::{BusIndex, InteractionBuilder, PermutationCheckBus},
    p3_field::FieldAlgebra,
};
use serde::{Deserialize, Serialize};
use thiserror::Error;

use super::Streams;
use crate::system::{memory::MemoryController, program::ProgramBus};

pub type Result<T> = std::result::Result<T, ExecutionError>;

#[derive(Error, Debug)]
pub enum ExecutionError {
    #[error("execution failed at pc {pc}")]
    Fail { pc: u32 },
    #[error("pc {pc} not found for program of length {program_len}, with pc_base {pc_base} and step = {step}")]
    PcNotFound {
        pc: u32,
        step: u32,
        pc_base: u32,
        program_len: usize,
    },
    #[error("pc {pc} out of bounds for program of length {program_len}, with pc_base {pc_base} and step = {step}")]
    PcOutOfBounds {
        pc: u32,
        step: u32,
        pc_base: u32,
        program_len: usize,
    },
    #[error("at pc {pc}, opcode {opcode} was not enabled")]
    DisabledOperation { pc: u32, opcode: VmOpcode },
    #[error("at pc = {pc}")]
    HintOutOfBounds { pc: u32 },
    #[error("at pc {pc}, tried to publish into index {public_value_index} when num_public_values = {num_public_values}")]
    PublicValueIndexOutOfBounds {
        pc: u32,
        num_public_values: usize,
        public_value_index: usize,
    },
    #[error("at pc {pc}, tried to publish {new_value} into index {public_value_index} but already had {existing_value}")]
    PublicValueNotEqual {
        pc: u32,
        public_value_index: usize,
        existing_value: usize,
        new_value: usize,
    },
    #[error("at pc {pc}, phantom sub-instruction not found for discriminant {}", .discriminant.0)]
    PhantomNotFound {
        pc: u32,
        discriminant: PhantomDiscriminant,
    },
    #[error("at pc {pc}, discriminant {}, phantom error: {inner}", .discriminant.0)]
    Phantom {
        pc: u32,
        discriminant: PhantomDiscriminant,
        inner: eyre::Error,
    },
    #[error("program must terminate")]
    DidNotTerminate,
    #[error("program exit code {0}")]
    FailedWithExitCode(u32),
}

pub trait InstructionExecutor<F> {
    /// Runtime execution of the instruction, if the instruction is owned by the
    /// current instance. May internally store records of this call for later trace generation.
    fn execute(
        &mut self,
        memory: &mut MemoryController<F>,
        instruction: &Instruction<F>,
        from_state: ExecutionState<u32>,
    ) -> Result<ExecutionState<u32>>;

    /// For display purposes. From absolute opcode as `usize`, return the string name of the opcode
    /// if it is a supported opcode by the present executor.
    fn get_opcode_name(&self, opcode: usize) -> String;
}

impl<F, C: InstructionExecutor<F>> InstructionExecutor<F> for RefCell<C> {
    fn execute(
        &mut self,
        memory: &mut MemoryController<F>,
        instruction: &Instruction<F>,
        prev_state: ExecutionState<u32>,
    ) -> Result<ExecutionState<u32>> {
        self.borrow_mut().execute(memory, instruction, prev_state)
    }

    fn get_opcode_name(&self, opcode: usize) -> String {
        self.borrow().get_opcode_name(opcode)
    }
}

impl<F, C: InstructionExecutor<F>> InstructionExecutor<F> for Rc<RefCell<C>> {
    fn execute(
        &mut self,
        memory: &mut MemoryController<F>,
        instruction: &Instruction<F>,
        prev_state: ExecutionState<u32>,
    ) -> Result<ExecutionState<u32>> {
        self.borrow_mut().execute(memory, instruction, prev_state)
    }

    fn get_opcode_name(&self, opcode: usize) -> String {
        self.borrow().get_opcode_name(opcode)
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Default, AlignedBorrow, Serialize, Deserialize)]
pub struct ExecutionState<T> {
    pub pc: T,
    pub timestamp: T,
}

#[derive(Clone, Copy, Debug)]
pub struct ExecutionBus {
    pub inner: PermutationCheckBus,
}

impl ExecutionBus {
    pub const fn new(index: BusIndex) -> Self {
        Self {
            inner: PermutationCheckBus::new(index),
        }
    }

    #[inline(always)]
    pub fn index(&self) -> BusIndex {
        self.inner.index
    }
}

#[derive(Copy, Clone, Debug)]
pub struct ExecutionBridge {
    execution_bus: ExecutionBus,
    program_bus: ProgramBus,
}

pub struct ExecutionBridgeInteractor<AB: InteractionBuilder> {
    execution_bus: ExecutionBus,
    program_bus: ProgramBus,
    opcode: AB::Expr,
    operands: Vec<AB::Expr>,
    from_state: ExecutionState<AB::Expr>,
    to_state: ExecutionState<AB::Expr>,
}

pub enum PcIncOrSet<T> {
    Inc(T),
    Set(T),
}

impl<T> ExecutionState<T> {
    pub fn new(pc: impl Into<T>, timestamp: impl Into<T>) -> Self {
        Self {
            pc: pc.into(),
            timestamp: timestamp.into(),
        }
    }

    #[allow(clippy::should_implement_trait)]
    pub fn from_iter<I: Iterator<Item = T>>(iter: &mut I) -> Self {
        let mut next = || iter.next().unwrap();
        Self {
            pc: next(),
            timestamp: next(),
        }
    }

    pub fn flatten(self) -> [T; 2] {
        [self.pc, self.timestamp]
    }

    pub fn get_width() -> usize {
        2
    }

    pub fn map<U: Clone, F: Fn(T) -> U>(self, function: F) -> ExecutionState<U> {
        ExecutionState::from_iter(&mut self.flatten().map(function).into_iter())
    }
}

impl ExecutionBus {
    /// Caller must constrain that `enabled` is boolean.
    pub fn execute_and_increment_pc<AB: InteractionBuilder>(
        &self,
        builder: &mut AB,
        enabled: impl Into<AB::Expr>,
        prev_state: ExecutionState<AB::Expr>,
        timestamp_change: impl Into<AB::Expr>,
    ) {
        let next_state = ExecutionState {
            pc: prev_state.pc.clone() + AB::F::ONE,
            timestamp: prev_state.timestamp.clone() + timestamp_change.into(),
        };
        self.execute(builder, enabled, prev_state, next_state);
    }

    /// Caller must constrain that `enabled` is boolean.
    pub fn execute<AB: InteractionBuilder>(
        &self,
        builder: &mut AB,
        enabled: impl Into<AB::Expr>,
        prev_state: ExecutionState<impl Into<AB::Expr>>,
        next_state: ExecutionState<impl Into<AB::Expr>>,
    ) {
        let enabled = enabled.into();
        self.inner.receive(
            builder,
            [prev_state.pc.into(), prev_state.timestamp.into()],
            enabled.clone(),
        );
        self.inner.send(
            builder,
            [next_state.pc.into(), next_state.timestamp.into()],
            enabled,
        );
    }
}

impl ExecutionBridge {
    pub fn new(execution_bus: ExecutionBus, program_bus: ProgramBus) -> Self {
        Self {
            execution_bus,
            program_bus,
        }
    }

    /// If `to_pc` is `Some`, then `pc_inc` is ignored and the `to_state` uses `to_pc`. Otherwise
    /// `to_pc = from_pc + pc_inc`.
    pub fn execute_and_increment_or_set_pc<AB: InteractionBuilder>(
        &self,
        opcode: impl Into<AB::Expr>,
        operands: impl IntoIterator<Item = impl Into<AB::Expr>>,
        from_state: ExecutionState<impl Into<AB::Expr> + Clone>,
        timestamp_change: impl Into<AB::Expr>,
        pc_kind: impl Into<PcIncOrSet<AB::Expr>>,
    ) -> ExecutionBridgeInteractor<AB> {
        let to_state = ExecutionState {
            pc: match pc_kind.into() {
                PcIncOrSet::Set(to_pc) => to_pc,
                PcIncOrSet::Inc(pc_inc) => from_state.pc.clone().into() + pc_inc,
            },
            timestamp: from_state.timestamp.clone().into() + timestamp_change.into(),
        };
        self.execute(opcode, operands, from_state, to_state)
    }

    pub fn execute_and_increment_pc<AB: InteractionBuilder>(
        &self,
        opcode: impl Into<AB::Expr>,
        operands: impl IntoIterator<Item = impl Into<AB::Expr>>,
        from_state: ExecutionState<impl Into<AB::Expr> + Clone>,
        timestamp_change: impl Into<AB::Expr>,
    ) -> ExecutionBridgeInteractor<AB> {
        let to_state = ExecutionState {
            pc: from_state.pc.clone().into() + AB::Expr::from_canonical_u32(DEFAULT_PC_STEP),
            timestamp: from_state.timestamp.clone().into() + timestamp_change.into(),
        };
        self.execute(opcode, operands, from_state, to_state)
    }

    pub fn execute<AB: InteractionBuilder>(
        &self,
        opcode: impl Into<AB::Expr>,
        operands: impl IntoIterator<Item = impl Into<AB::Expr>>,
        from_state: ExecutionState<impl Into<AB::Expr> + Clone>,
        to_state: ExecutionState<impl Into<AB::Expr>>,
    ) -> ExecutionBridgeInteractor<AB> {
        ExecutionBridgeInteractor {
            execution_bus: self.execution_bus,
            program_bus: self.program_bus,
            opcode: opcode.into(),
            operands: operands.into_iter().map(Into::into).collect(),
            from_state: from_state.map(Into::into),
            to_state: to_state.map(Into::into),
        }
    }
}

impl<AB: InteractionBuilder> ExecutionBridgeInteractor<AB> {
    /// Caller must constrain that `enabled` is boolean.
    pub fn eval(self, builder: &mut AB, enabled: impl Into<AB::Expr>) {
        let enabled = enabled.into();

        // Interaction with program
        self.program_bus.lookup_instruction(
            builder,
            self.from_state.pc.clone(),
            self.opcode,
            self.operands,
            enabled.clone(),
        );

        self.execution_bus
            .execute(builder, enabled, self.from_state, self.to_state);
    }
}

impl<T: FieldAlgebra> From<(u32, Option<T>)> for PcIncOrSet<T> {
    fn from((pc_inc, to_pc): (u32, Option<T>)) -> Self {
        match to_pc {
            None => PcIncOrSet::Inc(T::from_canonical_u32(pc_inc)),
            Some(to_pc) => PcIncOrSet::Set(to_pc),
        }
    }
}

/// Phantom sub-instructions affect the runtime of the VM and the trace matrix values.
/// However they all have no AIR constraints besides advancing the pc by
/// [DEFAULT_PC_STEP](openvm_instructions::program::DEFAULT_PC_STEP).
///
/// They should not mutate memory, but they can mutate the input & hint streams.
///
/// Phantom sub-instructions are only allowed to use operands
/// `a,b` and `c_upper = c.as_canonical_u32() >> 16`.
pub trait PhantomSubExecutor<F>: Send {
    fn phantom_execute(
        &mut self,
        memory: &MemoryController<F>,
        streams: &mut Streams<F>,
        discriminant: PhantomDiscriminant,
        a: F,
        b: F,
        c_upper: u16,
    ) -> eyre::Result<()>;
}
