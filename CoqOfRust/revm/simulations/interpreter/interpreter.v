Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import CoqOfRust.simulations.M.
Import simulations.M.Notations.
Require Import CoqOfRust.revm.links.dependencies.
Require Import CoqOfRust.revm.links.interpreter.interpreter.instruction_result.
Require Import CoqOfRust.revm.links.interpreter.interpreter.gas.
Require Import CoqOfRust.revm.links.interpreter.interpreter.contract.
Require Import CoqOfRust.revm.links.interpreter.interpreter.shared_memory.
Require Import CoqOfRust.revm.links.interpreter.interpreter.stack.
Require Import CoqOfRust.revm.links.interpreter.interpreter.function_stack.
Require Import CoqOfRust.revm.links.interpreter.interpreter_action.
Require Import CoqOfRust.revm.links.interpreter.interpreter.


Module Interpreter.
  Definition update_gas
    {A : Set}
    (m : MS? Gas.t string A) :
    MS? Interpreter.t string A :=
  letS? interp := readS? in
  let gas := Interpreter.gas interp in
  match m gas with
  | (result, state) =>
    match result with
    | inr e => panicS? e
    | inl result =>
      letS? _ := writeS? (interp <|
        Interpreter.gas := state
      |>) in
      returnS? result
    end
  end.
End Interpreter.
