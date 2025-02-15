Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.lib.proofs.lib.
Require Import links.M.
Require Import simulations.integer.

Module U64.
  Lemma checked_add_is_valid (a b : Z)
      (H_a : Integer.Valid.t IntegerKind.U64 a)
      (H_b : Integer.Valid.t IntegerKind.U64 b) :
    match U64.checked_add a b with
    | Some c => Integer.Valid.t IntegerKind.U64 c
    | None => True
    end.
  Proof.
    unfold U64.checked_add.
    destruct (_ <? _) eqn:?; [|exact I].
    unfold Integer.Valid.t in *.
    cbn in *.
    lia.
  Qed.

  Lemma checked_add_eq (a b : Z) :
    match U64.checked_add a b with
    | Some c => c = (a + b)%Z
    | None => True
    end.
  Proof.
    unfold U64.checked_add.
    hauto l: on.
  Qed.
End U64.
