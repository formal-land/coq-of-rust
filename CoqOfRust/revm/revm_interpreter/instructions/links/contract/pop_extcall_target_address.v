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
Require Import core.ops.links.function.
Require Import core.ops.links.range.
Require Import core.slice.links.iter.
Require Import core.slice.links.mod.
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
pub fn pop_extcall_target_address(
    interpreter: &mut Interpreter<impl InterpreterTypes>,
) -> Option<Address>
*)
Instance run_pop_extcall_target_address
  {WIRE : Set} `{Link WIRE}
  {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
  (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
  (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types)) :
  Run.Trait
    instructions.contract.pop_extcall_target_address [] [ Φ WIRE ] [ φ interpreter ]
    (option Address.t).
Proof.
  constructor.
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  destruct run_LoopControl_for_Control.
  destruct Impl_From_U256_for_FixedBytes_32.run.
  destruct (Impl_Iterator_for_Iter.run U8.t).
  destruct (Impl_Index_for_FixedBytes_N.run {| Integer.value := 32 |} (RangeTo.t Usize.t)).
  run_symbolic.
  match goal with
  | |- context[M.closure ?closure] =>
    set (any_callback := closure)
  end.
  assert (run_any_callback :
    forall (i : Ref.t Pointer.Kind.Ref U8.t),
    Run.Trait (fun _ _ => any_callback) [] [] [φ i] bool
  ). {
    intros.
    constructor.
    run_symbolic.
  }
  change (M.closure any_callback) with (φ (Function1.of_run run_any_callback)).
  generalize any; clear; intros [? ? run_any]; cbn in *.
  epose proof (run_any' := run_any _ _ _ (Function1.of_run run_any_callback) _ _ _).
  typeclasses eauto.
Defined.
