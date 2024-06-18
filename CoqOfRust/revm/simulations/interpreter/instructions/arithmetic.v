Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import CoqOfRust.simulations.M.
Import simulations.M.Notations.
Require Import CoqOfRust.revm.links.dependencies.
Require Import CoqOfRust.revm.links.interpreter.interpreter.
Require Import CoqOfRust.revm.links.interpreter.interpreter.instruction_result.
Require Import CoqOfRust.revm.simulations.interpreter.interpreter.
Require Import CoqOfRust.revm.simulations.interpreter.interpreter.gas.
Require Import CoqOfRust.revm.simulations.interpreter.interpreter.stack.
Require Import CoqOfRust.revm.simulations.interpreter.instructions.macros.

(*
  pub fn add<H: Host + ?Sized>(interpreter: &mut Interpreter, _host: &mut H) {
      gas!(interpreter, gas::VERYLOW);
      pop_top!(interpreter, op1, op2);
      *op2 = op1.wrapping_add( *op2 );
  }
*)

Definition add :
  MS? Interpreter.t string unit :=
  letS? _ := gas_macro Gas.VERYLOW in
  letS? '(op1, op2) := pop_top_macro2 in
  liftS? Interpreter.Lens.stack (
    Stack.top_unsafe_write (wrapping_add op1 op2)
  ).

(*
  pub fn mul<H: Host + ?Sized>(interpreter: &mut Interpreter, _host: &mut H) {
      gas!(interpreter, gas::LOW);
      pop_top!(interpreter, op1, op2);
      *op2 = op1.wrapping_mul( *op2 );
  }
*)

Definition mul :
  MS? Interpreter.t string unit :=
  letS? _ := gas_macro Gas.LOW in
  letS? '(op1, op2) := pop_top_macro2 in
  liftS? Interpreter.Lens.stack (
    Stack.top_unsafe_write (wrapping_mul op1 op2)
  ).

(*
  pub fn sub<H: Host + ?Sized>(interpreter: &mut Interpreter, _host: &mut H) {
      gas!(interpreter, gas::VERYLOW);
      pop_top!(interpreter, op1, op2);
      *op2 = op1.wrapping_sub( *op2 );
  }
*)

Definition sub :
  MS? Interpreter.t string unit :=
  letS? _ := gas_macro Gas.VERYLOW in
  letS? '(op1, op2) := pop_top_macro2 in
  liftS? Interpreter.Lens.stack (
    Stack.top_unsafe_write (wrapping_sub op1 op2)
  ).
