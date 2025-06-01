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
pub fn call<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
)
*)
Instance run_call
  {WIRE H : Set} `{Link WIRE} `{Link H}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (run_Host_for_H : Host.Run H H_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
  (host : Ref.t Pointer.Kind.MutRef H) :
  Run.Trait
    instructions.contract.call [] [ Φ WIRE; Φ H ] [ φ interpreter; φ host ]
    unit.
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE eqn:?.
  destruct run_StackTrait_for_Stack.
  destruct run_LoopControl_for_Control.
  destruct run_InputsTrait_for_Input.
  destruct run_RuntimeFlag_for_RuntimeFlag.
  destruct run_Host_for_H.
  destruct (TryFrom_Uint_for_u64.run {| Integer.value := 256 |} {| Integer.value := 4 |}).
  destruct Impl_IntoAddress_for_U256.run.
  run_symbolic.
Admitted.
