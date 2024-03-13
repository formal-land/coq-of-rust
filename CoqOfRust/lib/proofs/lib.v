Require Import CoqOfRust.lib.lib.
Require Import CoqOfRust.proofs.M.
Require CoqOfRust.simulations.M.

(* Proof libraries that we can use everywhere. *)
Require Export Lia.
From Hammer Require Export Tactics.

Import simulations.M.Notations.

(*** Destruct the matched value in an expression [e]. *)
Ltac destruct_match_in e :=
  lazymatch e with
  | context[match ?e with | _ => _ end] =>
    destruct_match_in e
  | context[let? _ := ?e in _] =>
    destruct_match_in e
  | context[letS? _ := ?e in _] =>
    destruct_match_in e
  | _ => destruct e eqn:?
  end.

(** Destruct one matched value in the goal. *)
Ltac step :=
  match goal with
  | |- context[match ?e with | _ => _ end] =>
    destruct_match_in e
  | |- context[let? _ := ?e in _] =>
    destruct_match_in e
  | |- context[letS? _ := ?e in _] =>
    destruct_match_in e
  end.

Module Integer.
  Module Valid.
    Definition t (kind : Integer.t) (z : Z) : Prop :=
      Integer.min kind <= z <= Integer.max kind.
  End Valid.
End Integer.

Module BinOp.
  Module Error.
    Lemma add_eq (kind : Integer.t) (z1 z2 z : Z) :
      BinOp.Error.add (Value.Integer kind z1) (Value.Integer kind z2) =
        inl (Value.Integer kind z) ->
      z = (z1 + z2)%Z.
    Proof.
      unfold
        BinOp.Error.add,
        BinOp.Error.make_arithmetic,
        Integer.normalize_with_error.
      sauto.
    Qed.

    Lemma add_is_valid (kind : Integer.t) (z1 z2 : Z) (v : Value.t)
      (H_z1 : Integer.Valid.t kind z1)
      (H_z2 : Integer.Valid.t kind z2)
      (H_v :
        BinOp.Error.add (Value.Integer kind z1) (Value.Integer kind z2) =
          inl v) :
      match v with
      | Value.Integer _ z => Integer.Valid.t kind z
      | _ => False
      end.
    Proof.
      unfold
        Integer.Valid.t,
        BinOp.Error.add,
        BinOp.Error.make_arithmetic,
        Integer.normalize_with_error
        in *.
      repeat destruct (_ <? _) eqn:? in H_v; try congruence.
      sauto lq: on solve: lia.
    Qed.
  End Error.
End BinOp.
