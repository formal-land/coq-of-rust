Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import CoqOfRust.simulations.M.
Import simulations.M.Notations.
Require Import CoqOfRust.revm.links.dependencies.
Require Import CoqOfRust.revm.links.interpreter.interpreter.
Require Import CoqOfRust.revm.links.interpreter.interpreter.instruction_result.
Require Import CoqOfRust.revm.links.primitives.specification.
Require Import CoqOfRust.revm.simulations.interpreter.gas.calc.
Require Import CoqOfRust.revm.simulations.interpreter.interpreter.
Require Import CoqOfRust.revm.simulations.interpreter.interpreter.gas.
Require Import CoqOfRust.revm.simulations.interpreter.interpreter.stack.
Require Import CoqOfRust.revm.simulations.interpreter.instructions.macros.
Require Import CoqOfRust.revm.simulations.interpreter.instructions.i256.

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
    Stack.top_unsafe_write (U256.wrapping_add op1 op2)
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
    Stack.top_unsafe_write (U256.wrapping_mul op1 op2)
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
    Stack.top_unsafe_write (U256.wrapping_sub op1 op2)
  ).

(*
  pub fn div<H: Host + ?Sized>(interpreter: &mut Interpreter, _host: &mut H) {
    gas!(interpreter, gas::LOW);
    pop_top!(interpreter, op1, op2);
    if *op2 != U256::ZERO {
        *op2 = op1.wrapping_div( *op2 );
    }
  }
*)

Definition div :
    MS? Interpreter.t string unit :=
  letS? _ := gas_macro Gas.LOW in
  letS? '(op1, op2) := pop_top_macro2 in
  if U256.eq op2 U256.ZERO
  then returnS? tt
  else liftS? Interpreter.Lens.stack (
    Stack.top_unsafe_write (U256.wrapping_div op1 op2)
  ).

(*
  pub fn sdiv<H: Host + ?Sized>(interpreter: &mut Interpreter, _host: &mut H) {
      gas!(interpreter, gas::LOW);
      pop_top!(interpreter, op1, op2);
      *op2 = i256_div(op1, *op2);
  }
*)

Definition sdiv :
    MS? Interpreter.t string unit :=
  letS? _ := gas_macro Gas.LOW in
  letS? '(op1, op2) := pop_top_macro2 in
  liftS? Interpreter.Lens.stack (
    Stack.top_unsafe_write (i256_div op1 op2)
  ).

(*
  pub fn rem<H: Host + ?Sized>(interpreter: &mut Interpreter, _host: &mut H) {
      gas!(interpreter, gas::LOW);
      pop_top!(interpreter, op1, op2);
      if *op2 != U256::ZERO {
          *op2 = op1.wrapping_rem( *op2 );
      }
  }
*)

Definition rem :
    MS? Interpreter.t string unit :=
  letS? _ := gas_macro Gas.LOW in
  letS? '(op1, op2) := pop_top_macro2 in
  if U256.eq op2 U256.ZERO
  then returnS? tt
  else liftS? Interpreter.Lens.stack (
    Stack.top_unsafe_write (U256.wrapping_rem op1 op2)
  ).

(*
  pub fn smod<H: Host + ?Sized>(interpreter: &mut Interpreter, _host: &mut H) {
      gas!(interpreter, gas::LOW);
      pop_top!(interpreter, op1, op2);
      *op2 = i256_mod(op1, *op2)
  }
*)

Definition smod :
    MS? Interpreter.t string unit :=
  letS? _ := gas_macro Gas.LOW in
  letS? '(op1, op2) := pop_top_macro2 in
  liftS? Interpreter.Lens.stack (
    Stack.top_unsafe_write (i256_mod op1 op2)
  ).

(*
  pub fn addmod<H: Host + ?Sized>(interpreter: &mut Interpreter, _host: &mut H) {
      gas!(interpreter, gas::MID);
      pop_top!(interpreter, op1, op2, op3);
      *op3 = op1.add_mod(op2, *op3)
  }
*)

Definition addmod :
  MS? Interpreter.t string unit :=
  letS? _ := gas_macro Gas.MID in
  letS? '(op1, op2, op3) := pop_top_macro3 in
  liftS? Interpreter.Lens.stack (
    Stack.top_unsafe_write (U256.add_mod op1 op2 op3)
  ).

(*
  pub fn mulmod<H: Host + ?Sized>(interpreter: &mut Interpreter, _host: &mut H) {
      gas!(interpreter, gas::MID);
      pop_top!(interpreter, op1, op2, op3);
      *op3 = op1.mul_mod(op2, *op3)
  }
*)

Definition mulmod :
  MS? Interpreter.t string unit :=
  letS? _ := gas_macro Gas.MID in
  letS? '(op1, op2, op3) := pop_top_macro3 in
  liftS? Interpreter.Lens.stack (
    Stack.top_unsafe_write (U256.mul_mod op1 op2 op3)
  ).

(*
  pub fn exp<H: Host + ?Sized, SPEC: Spec>(interpreter: &mut Interpreter, _host: &mut H) {
      pop_top!(interpreter, op1, op2);
      gas_or_fail!(interpreter, gas::exp_cost(SPEC::SPEC_ID, *op2));
      *op2 = op1.pow( *op2 );
  }
*)

Definition exp (SPEC : Spec.t) :
    MS? Interpreter.t string unit :=
  letS? '(op1, op2) := pop_top_macro2 in
  letS? _ := gas_or_fail_macro (exp_cost (Spec.SPEC_ID SPEC) op2) in
  liftS? Interpreter.Lens.stack (
    Stack.top_unsafe_write (U256.wrapping_pow op1 op2)
  ).
