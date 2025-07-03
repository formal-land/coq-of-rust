Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import alloc.links.boxed.
Require Import alloc.links.slice.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bits.links.fixed.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.utils.links.mod.
Require Import bytes.links.bytes.
Require Import core.convert.links.mod.
Require Import core.fmt.links.mod.
Require Import core.links.borrow.
Require Import core.links.cmp.
Require Import core.links.option.
Require Import core.links.panicking.
Require Import core.links.result.
Require Import core.num.links.mod.
Require Import core.ops.links.control_flow.
Require Import core.ops.links.range.
Require Import core.slice.links.iter.
Require Import revm.revm_bytecode.links.eof.
Require Import revm.revm_context_interface.links.cfg.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.gas.links.calc.
Require Import revm.revm_interpreter.gas.links.constants.
Require Import revm.revm_interpreter.interpreter_action.links.call_inputs.
Require Import revm.revm_interpreter.interpreter_action.links.eof_create_inputs.
Require Import revm.revm_interpreter.interpreter.links.shared_memory.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.instructions.contract.links.call_helpers.
Require Import revm.revm_interpreter.instructions.contract.
Require Import revm.revm_interpreter.instructions.links.utility.
Require Import revm.revm_specification.links.hardfork.
Require Import ruint.links.bytes.
Require Import ruint.links.cmp.
Require Import ruint.links.from.
Require Import ruint.links.lib.

(*
pub fn extcall_input(interpreter: &mut Interpreter<impl InterpreterTypes>) -> Option<Bytes>
*)
Instance run_extcall_input
  {WIRE : Set} `{Link WIRE}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types)) :
  Run.Trait
    instructions.contract.extcall_input [] [ Φ WIRE ] [ φ interpreter ]
    (option alloy_primitives.bytes.links.mod.Bytes.t).
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE eqn:?.
  destruct run_StackTrait_for_Stack.
  destruct run_LoopControl_for_Control.
  destruct run_MemoryTrait_for_Memory.
  destruct (Impl_Try_for_Option.run alloy_primitives.bytes.links.mod.Bytes.t).
  destruct run_FromResidual_for_Self.
  destruct (Impl_Try_for_Option.run (Range.t Usize.t)).
  destruct (Impl_AsRef_for_Slice.run U8.t).
  destruct run_Deref_for_Synthetic.
  destruct (Impl_FromResidual_Infallible_for_Option.run alloy_primitives.bytes.links.mod.Bytes.t).
  destruct (Impl_Clone_for_Range.run Usize.t).
  run_symbolic.
Defined.
