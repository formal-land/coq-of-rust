Require Import Coq.Strings.String.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.core.simulations.eq.

Module ImplEq.
  Global Instance I :
    Eq.Trait unit := {
      eqb _ _ := true;
    }.
End ImplEq.
