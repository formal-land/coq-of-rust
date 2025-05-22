Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.links.array.
Require Import pinocchio.pubkey.

Module Pubkey.
  Definition t : Set :=
    array.t U8.t {| Integer.value := 32 |}.
End Pubkey.