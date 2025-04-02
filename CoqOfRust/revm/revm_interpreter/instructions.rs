//! EVM opcode implementations.

#[macro_use]
pub mod macros;
pub mod arithmetic;
pub mod bitwise;
pub mod block_info;
pub mod contract;
pub mod control;
pub mod data;
pub mod host;
pub mod i256;
pub mod memory;
pub mod stack;
pub mod system;
pub mod tx_info;
pub mod utility;

use crate::{interpreter_types::InterpreterTypes, Host};

/// Returns the instruction function for the given opcode and spec.
pub const fn instruction<WIRE: InterpreterTypes, H: Host + ?Sized>(
    opcode: u8,
) -> crate::table::Instruction<WIRE, H> {
    let table = instruction_table::<WIRE, H>();
    table[opcode as usize]
}

pub const fn instruction_table<WIRE: InterpreterTypes, H: Host + ?Sized>(
) -> [crate::table::Instruction<WIRE, H>; 256] {
    use bytecode::opcode::*;
    let mut table = [control::unknown as crate::table::Instruction<WIRE, H>; 256];

    table[STOP as usize] = control::stop;
    table[ADD as usize] = arithmetic::add;
    table[BALANCE as usize] = host::balance;

    table
}

#[cfg(test)]
mod tests {
    // use super::*;
    // use crate::DummyHost;
    // use bytecode::opcode::*;

    // TODO : Define EthEthereumWire
    // #[test]
    // fn all_instructions_and_opcodes_used() {
    //     // known unknown instruction we compare it with other instructions from table.
    //     let unknown_instruction = 0x0C_usize;
    //     let instr_table = instruction_table::<InterpreterTypes, DummyHost<DefaultEthereumWiring>>();

    //     let unknown_istr = instr_table[unknown_instruction];
    //     for (i, instr) in instr_table.iter().enumerate() {
    //         let is_opcode_unknown = OpCode::new(i as u8).is_none();
    //         let is_instr_unknown = *instr == unknown_istr;
    //         assert_eq!(
    //             is_instr_unknown, is_opcode_unknown,
    //             "Opcode 0x{:X?} is not handled",
    //             i
    //         );
    //     }
    // }
}
