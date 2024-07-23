Require Import CoqOfRust.CoqOfRust.
Require Import simulations.M.
Require Import CoqOfRust.core.simulations.eq.

Module U64.
  Definition checked_add (a b : Z) : option Z :=
    let r := (a + b)%Z in
    if r <? 2 ^ 64
    then Some r
    else None.
End U64.

Module ImplEq.
  Global Instance I :
    Eq.Trait Z := {
      eqb := Z.eqb;
    }.
End ImplEq.
