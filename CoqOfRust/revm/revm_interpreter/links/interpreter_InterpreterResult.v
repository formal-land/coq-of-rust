Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import revm.links.dependencies.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm_interpreter.links.gas.

Module InterpreterResult.
  Record t : Set := {
    result: revm_interpreter.links.instruction_result.InstructionResult.t;
    output: alloy_primitives.links.bytes_.Bytes.t;
    gas: revm_interpreter.links.gas.Gas.t;
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
End InterpreterResult.
