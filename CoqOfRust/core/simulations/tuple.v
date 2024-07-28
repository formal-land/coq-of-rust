Require Import CoqOfRust.CoqOfRust.
Require Import simulations.M.
Import simulations.M.Notations.
Require Import CoqOfRust.core.simulations.eq.
Import simulations.eq.Notations.

Module ImplEq.
  Global Instance I (A B : Set) `{Eq.Trait A} `{Eq.Trait B} :
    Eq.Trait (A * B) := {
      eqb '(a, b) '(c, d) := ((a =? c) && (b =? d))%bool;
    }.
End ImplEq.
