Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import CoqOfRust.simulate.M.
Require Import revm.revm_interpreter.gas.links.constants.

Lemma VERYLOW_eq {Stack : Stack.t} (stack : Stack.to_Set Stack) :
  {{
    StackM.eval_f (Stack := Stack) run_VERYLOW stack 🌲
    (Output.Success (Ref.immediate _ {| Integer.value := 3 |}), stack)
  }}.
Proof.
  cbn.
  apply Run.Pure.
Qed.
Global Opaque run_VERYLOW.
