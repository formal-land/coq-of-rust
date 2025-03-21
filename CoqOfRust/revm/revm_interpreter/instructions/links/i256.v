Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import revm.revm_interpreter.instructions.i256.

(* NOTE: This function isn't associated with a trait. I wonder if this is the correct way to translate it... *)
(* pub fn i256_div(mut first: U256, mut second: U256) -> U256  *)

Global Instance Instance_IsFunction_i256_div :
  M.IsFunction.Trait "revm::revm_interpreter::instructions::i256::i256_div" instructions.i256.i256_div.
Admitted.
Global Typeclasses Opaque instructions.i256.i256_div.