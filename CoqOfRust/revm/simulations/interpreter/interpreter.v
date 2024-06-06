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
  Module Lens.
    Definition gas : Lens.t Interpreter.t Gas.t := {|
      Lens.read interp := Interpreter.gas interp;
      Lens.write interp gas := interp <| Interpreter.gas := gas |>
    |}.
  End Lens.
End Interpreter.
