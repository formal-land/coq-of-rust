Require Import CoqOfRust.CoqOfRust.
Require Import simulations.M.

Module U64.
  Definition checked_add (a b : Z) : option Z :=
    let r := (a + b)%Z in
    if r <? 2 ^ 64
    then Some r
    else None.
End U64.
