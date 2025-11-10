Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import examples.default.examples.custom.loops_free.

Instance run_max2 (a b : U32.t) : Run.Trait max2 [] [] [φ a; φ b] U32.t.
Proof.
  constructor.
  run_symbolic.
Defined.

Instance run_abs_i32 (x : I32.t) : Run.Trait abs_i32 [] [] [φ x] I32.t.
Proof.
  constructor.
  run_symbolic.
Defined.

Instance run_bool_and (a b : Bool.t) : Run.Trait bool_and [] [] [φ a; φ b] Bool.t.
Proof.
  constructor.
  run_symbolic.
Defined.

Instance run_get_or_zero (xs : Array.t U32.t 4) (i : Usize.t) :
  Run.Trait get_or_zero [] [] [φ xs; φ i] U32.t.
Proof.
  constructor.
  run_symbolic.
Defined.

Instance run_eq2 (a b : Array.t U32.t 2) : Run.Trait eq2 [] [] [φ a; φ b] Bool.t.
Proof.
  constructor.
  run_symbolic.
Defined.

Instance run_eq_pair (x y : Prod.t U32.t U32.t) : Run.Trait eq_pair [] [] [φ x; φ y] Bool.t.
Proof.
  constructor.
  run_symbolic.
Defined.

Instance run_min3 (a b c : U32.t) : Run.Trait min3 [] [] [φ a; φ b; φ c] U32.t.
Proof.
  constructor.
  run_symbolic.
Defined.
