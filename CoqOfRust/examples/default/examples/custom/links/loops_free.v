Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import examples.default.examples.custom.loops_free.

(* pub fn max2(a: u32, b: u32) -> u32 *)
Instance run_max2 (a b : U32.t) : Run.Trait max2 [] [] [φ a; φ b] U32.t.
Proof.
  constructor.
  run_symbolic.
Defined.
