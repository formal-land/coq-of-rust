Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.lib.
Require Import CoqOfRust.links.M.
Require Import revm.revm_interpreter.instructions.host.
Require Import revm.revm_interpreter.instructions.links.utility.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.

Import Run.

(*
pub fn balance<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
)
*)
Definition run_balance
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE WIRE_types))
    (host : Ref.t Pointer.Kind.MutRef H) :
  {{
    instructions.host.balance [] [ Φ WIRE; Φ H ] [ φ interpreter; φ host ] 🔽
    unit
  }}.
Proof.
  run.
  eapply Run.Rewrite. {
    do 3 erewrite IsTraitAssociatedType_eq by apply run_InterpreterTypes_for_WIRE.
    reflexivity.
  }
  destruct run_InterpreterTypes_for_WIRE.
  destruct run_StackTrait_for_Stack.
  destruct popn_top as [popn_top [H_popn_top run_popn_top]].
  run_symbolic.
  run_symbolic_let. {
    destruct Impl_IntoAddress_for_U256.run.
    destruct into_address as [into_address [H_into_address run_into_address]].
    run_symbolic.
  }
  intros [|[]]; run_symbolic.
  admit.
Admitted.
