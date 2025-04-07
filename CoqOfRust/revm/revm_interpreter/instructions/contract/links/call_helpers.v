Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.links.aliases.
Require Import core.links.option.
Require Import core.ops.links.range.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_interpreter.instructions.contract.call_helpers.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.

(*
pub fn get_memory_input_and_out_ranges(
    interpreter: &mut Interpreter<impl InterpreterTypes>,
) -> Option<(Bytes, Range<usize>)>
*)
Instance run_get_memory_input_and_out_ranges
  {WIRE : Set} `{Link WIRE}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types)) :
  Run.Trait
    instructions.contract.call_helpers.get_memory_input_and_out_ranges
    [] [Φ WIRE] [φ interpreter]
    (option (Bytes.t * Range.t Usize.t)).
Proof.
  constructor.
Admitted.

(*
pub fn resize_memory(
    interpreter: &mut Interpreter<impl InterpreterTypes>,
    offset: U256,
    len: U256,
) -> Option<Range<usize>>
*)
Instance run_resize_memory
  {WIRE : Set} `{Link WIRE}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (offset len : aliases.U256.t) :
  Run.Trait
    instructions.contract.call_helpers.resize_memory
    [] [Φ WIRE] [φ interpreter; φ offset; φ len]
    (option (Range.t Usize.t)).
Proof.
  constructor.
Admitted.

(*
pub fn calc_call_gas(
    interpreter: &mut Interpreter<impl InterpreterTypes>,
    account_load: AccountLoad,
    has_transfer: bool,
    local_gas_limit: u64,
) -> Option<u64>
*)
Instance run_calc_call_gas
  {WIRE : Set} `{Link WIRE}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (account_load : AccountLoad.t)
  (has_transfer : bool)
  (local_gas_limit : U64.t) :
  Run.Trait
    instructions.contract.call_helpers.calc_call_gas
    [] [Φ WIRE] [φ interpreter; φ account_load; φ has_transfer; φ local_gas_limit]
    (option U64.t).
Proof.
  constructor.
Admitted.
