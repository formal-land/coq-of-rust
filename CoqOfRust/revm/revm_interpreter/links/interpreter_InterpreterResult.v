Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import alloy_primitives.bytes.links.mod.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm_interpreter.links.gas.

Module InterpreterResult.
  Record t : Set := {
    gas: Gas.t;
    output: Bytes.t;
    result: InstructionResult.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter::InterpreterResult";
    φ x :=
      Value.StructRecord "revm_interpreter::interpreter::InterpreterResult" [] [] [
        ("gas", φ x.(gas));
        ("output", φ x.(output));
        ("result", φ x.(result))
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
    Value.StructRecord "revm_interpreter::interpreter::InterpreterResult" [] [] [
      ("gas", gas');
      ("output", output');
      ("result", result')
    ] =
    φ (Build_t gas output result).
  Proof. now intros; subst. Qed.
  Smpl Add eapply of_value_with : of_value.

  Definition of_value
      (result : InstructionResult.t) result'
      (output : Bytes.t) output'
      (gas : Gas.t) gas' :
    result' = φ result ->
    output' = φ output ->
    gas' = φ gas ->
    OfValue.t (
      Value.StructRecord "revm_interpreter::interpreter::InterpreterResult" [] [] [
        ("gas", gas');
        ("output", output');
        ("result", result')
      ]
    ).
  Proof.
    intros.
    eapply OfValue.Make with (A := t).
    apply of_value_with; eassumption.
  Defined.
  Smpl Add eapply of_value : of_value.
End InterpreterResult.
