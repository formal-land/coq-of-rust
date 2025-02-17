Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.lib.
Require Import CoqOfRust.links.M.
Require Import revm_context_interface.links.host.
Require Import revm_interpreter.links.interpreter.
Require Import revm_interpreter.links.interpreter_types.
Require Import revm_interpreter.instructions.arithmetic.

Import Run.

Definition run_add
    {WIRE : Set} `{Link WIRE} `{InterpreterTypes.Trait WIRE} `{InterpreterTypes.HasLinks.t WIRE}
    {H_ : Set} `{Link H_} `{Host.Trait H_}
    (interpreter : Ref.t Pointer.Kind.MutRef (Interpreter.t WIRE))
    (_host : Ref.t Pointer.Kind.MutRef H_) :
  {{
    instructions.arithmetic.add [] [ Φ WIRE; Φ H_ ] [ φ interpreter; φ _host ] 🔽
    unit
  }}.
Proof.
  run_symbolic.
  run_symbolic_let. {
    run_symbolic.
    admit.
  }
  admit.
Admitted.
