Require Import CoqOfRust.CoqOfRust.
Require Import simulations.M.
Require Import CoqOfRust.core.simulations.eq.

Module ImplEq.
  Global Instance I (A B : Set) `{Eq.Trait A} `{Eq.Trait B} :
    Eq.Trait (A * B) := {
      eqb '(a, b) '(c, d) := ((a =? c) && (b =? d))%bool;
    }.
End ImplEq.
