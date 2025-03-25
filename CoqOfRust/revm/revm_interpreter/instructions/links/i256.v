Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import revm.links.dependencies.
Require Import revm.revm_interpreter.instructions.i256.

(* pub fn i256_div(mut first: U256, mut second: U256) -> U256 *)
Instance run_i256_div (first second : U256.t) :
  Run.Trait instructions.i256.i256_div [] [] [ φ first; φ second ] U256.t.
Proof.
  constructor.
  run_symbolic.
Admitted.

(* pub fn i256_mod(mut first: U256, mut second: U256) -> U256 *)
Instance run_i256_mod (first second : U256.t) :
  Run.Trait instructions.i256.i256_mod [] [] [ φ first; φ second ] U256.t.
Proof.
  constructor.
  run_symbolic.
Admitted.