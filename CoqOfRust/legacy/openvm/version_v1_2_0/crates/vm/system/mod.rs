pub mod connector;
pub mod memory;
pub mod native_adapter;
/// Chip to handle phantom instructions.
/// The Air will always constrain a NOP which advances pc by DEFAULT_PC_STEP.
/// The runtime executor will execute different phantom instructions that may
/// affect trace generation based on the operand.
pub mod phantom;
pub mod poseidon2;
pub mod program;
pub mod public_values;
