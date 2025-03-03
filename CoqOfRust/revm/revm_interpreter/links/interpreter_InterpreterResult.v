Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import revm.links.dependencies.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm_interpreter.links.gas.

Module InterpreterResult.
  Record t : Set := {
    result: InstructionResult.t;
    output: alloy_primitives.links.bytes_.Bytes.t;
    gas: Gas.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter::InterpreterResult";
    φ '(Build_t result output gas) :=
      Value.StructRecord "revm_interpreter::interpreter::InterpreterResult" [
        ("result", φ result);
        ("output", φ output);
        ("gas", φ gas)
      ]
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_interpreter::interpreter::InterpreterResult").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with
      result result'
      output output'
      gas gas' :
    result' = φ result ->
    output' = φ output ->
    gas' = φ gas ->
    Value.StructRecord "revm_interpreter::interpreter::InterpreterResult" [
      ("result", result');
      ("output", output');
      ("gas", gas')
    ] =
    φ (Build_t result output gas).
  Proof. now intros; subst. Qed.
  Smpl Add eapply of_value_with : of_value.

  Definition of_value
      (result : InstructionResult.t) result'
      (output : alloy_primitives.links.bytes_.Bytes.t) output'
      (gas : Gas.t) gas' :
    result' = φ result ->
    output' = φ output ->
    gas' = φ gas ->
    OfValue.t (
      Value.StructRecord "revm_interpreter::interpreter::InterpreterResult" [
        ("result", result');
        ("output", output');
        ("gas", gas')
      ]
    ).
  Proof.
    intros.
    eapply OfValue.Make with (A := t).
    apply of_value_with; eassumption.
  Defined.
  Smpl Add eapply of_value : of_value.
End InterpreterResult.
