Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.

Require Import move_sui.simulations.move_binary_format.file_format.

Module SignatureToken.
  Lemma t_beq_is_valid (x y : SignatureToken.t) :
    SignatureToken.t_beq x y = true <-> x = y.
  Proof.
  Admitted.
End SignatureToken.
