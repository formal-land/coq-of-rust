Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import CoqOfRust.simulations.M.
Import simulations.M.Notations.

(*
Require Import revm.interpreter.links.interpreter.
Require Import revm.interpreter.interpreter.links.instruction_result.
Require Import revm.primitives.links.specification.
Require Import revm.simulations.dependencies.
Require Import revm.interpreter.gas.simulations.calc.
Require Import revm.interpreter.simulations.interpreter.
Require Import revm.interpreter.interpreter.simulations.gas.
Require Import revm.interpreter.interpreter.simulations.stack.
Require Import revm.interpreter.instructions.simulations.macros.
Require Import revm.interpreter.instructions.simulations.i256.

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
  letS? '(op1, op2_ref) := pop_top_macro2 in
  liftS? Interpreter.Lens.stack (
    liftS?of!? op2_ref (
      letS? op2 := readS? in
      writeS? (U256.wrapping_add op1 op2)
    )
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
  letS? '(op1, op2_ref) := pop_top_macro2 in
  liftS? Interpreter.Lens.stack (
    liftS?of!? op2_ref (
      letS? op2 := readS? in
      writeS? (U256.wrapping_mul op1 op2)
    )
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
  letS? '(op1, op2_ref) := pop_top_macro2 in
  liftS? Interpreter.Lens.stack (
    liftS?of!? op2_ref (
      letS? op2 := readS? in
      writeS? (U256.wrapping_sub op1 op2)
    )
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
  letS? '(op1, op2_ref) := pop_top_macro2 in
  liftS? Interpreter.Lens.stack (
    liftS?of!? op2_ref (
      letS? op2 := readS? in
      if U256.eq op2 U256.ZERO
      then returnS? tt
      else writeS? (U256.wrapping_div op1 op2)
    )
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
  letS? '(op1, op2_ref) := pop_top_macro2 in
  liftS? Interpreter.Lens.stack (
    liftS?of!? op2_ref (
      letS? op2 := readS? in
      writeS? (i256_div op1 op2)
    )
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
  letS? '(op1, op2_ref) := pop_top_macro2 in
  liftS? Interpreter.Lens.stack (
    liftS?of!? op2_ref (
      letS? op2 := readS? in
      if U256.eq op2 U256.ZERO
      then returnS? tt
      else writeS? (U256.wrapping_rem op1 op2)
    )
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
  letS? '(op1, op2_ref) := pop_top_macro2 in
  liftS? Interpreter.Lens.stack (
    liftS?of!? op2_ref (
      letS? op2 := readS? in
      writeS? (i256_mod op1 op2)
    )
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
  letS? '(op1, op2, op3_ref) := pop_top_macro3 in
  liftS? Interpreter.Lens.stack (
    liftS?of!? op3_ref (
      letS? op3 := readS? in
      writeS? (U256.add_mod op1 op2 op3)
    )
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
  letS? '(op1, op2, op3_ref) := pop_top_macro3 in
  liftS? Interpreter.Lens.stack (
    liftS?of!? op3_ref (
      letS? op3 := readS? in
      writeS? (U256.mul_mod op1 op2 op3)
    )
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
  letS? '(op1, op2_ref) := pop_top_macro2 in
  letS? op2 := liftS? Interpreter.Lens.stack (
    liftS?of!? op2_ref readS?
  ) in
  letS? _ := gas_or_fail_macro (exp_cost (Spec.SPEC_ID SPEC) op2) in
  liftS? Interpreter.Lens.stack (
    liftS?of!? op2_ref (writeS? (U256.wrapping_pow op1 op2))
  ).

(*
  pub fn signextend<H: Host + ?Sized>(interpreter: &mut Interpreter, _host: &mut H) {
      gas!(interpreter, gas::LOW);
      pop_top!(interpreter, ext, x);
      // For 31 we also don't need to do anything.
      if ext < U256::from(31) {
          let ext = ext.as_limbs()[0];
          let bit_index = (8 * ext + 7) as usize;
          let bit = x.bit(bit_index);
          let mask = (U256::from(1) << bit_index) - U256::from(1);
          *x = if bit { *x | !mask } else { *x & mask };
      }
  }
*)

Definition signextend :
    MS? Interpreter.t string unit :=
  letS? _ := gas_macro Gas.LOW in
  letS? '(ext, x_ref) := pop_top_macro2 in
  liftS? Interpreter.Lens.stack (
    liftS?of!? x_ref (
      letS? x := readS? in
      if U256.lt ext (U256.from 31)
      then
        let ext := hd 0 (U256.as_limbs ext) in
        let bit_index := (8 * ext + 7)%Z in
        let bit := U256.bit x bit_index in
        let mask :=
          U256.wrapping_sub
            (U256.shl (U256.from 1) bit_index)
            (U256.from 1) in
        writeS? (
          if bit
          then U256.or x (U256.not mask)
          else U256.and x mask
        )
      else
        returnS? tt
    )
  ). 
*)
