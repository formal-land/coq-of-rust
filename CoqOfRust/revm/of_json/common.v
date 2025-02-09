Require Import CoqOfRust.CoqOfRust.
Require Import simulations.M.

Module ruint.
  Module Uint.
    Definition t (BITS LIMBS : Z) : Set :=
      Z.
  End Uint.
End ruint.
