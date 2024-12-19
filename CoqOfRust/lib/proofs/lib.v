Require Import CoqOfRust.lib.lib.
Require Import CoqOfRust.proofs.M.
Require CoqOfRust.simulations.M.

Import simulations.M.Notations.

(*** Destruct the matched value in an expression [e]. *)
Ltac destruct_match_in e :=
  lazymatch e with
  | context[match ?e with | _ => _ end] =>
    destruct_match_in e
  | context[let? _ := ?e in _] =>
    destruct_match_in e
  | context[let! _ := ?e in _] =>
    destruct_match_in e
  | context[let!? _ := ?e in _] =>
    destruct_match_in e
  | context[letS _ := ?e in _] =>
    destruct_match_in e
  | context[letS! _ := ?e in _] =>
    destruct_match_in e
  | context[letS!? _ := ?e in _] =>
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
  | |- context[let! _ := ?e in _] =>
    destruct_match_in e
  | |- context[let!? _ := ?e in _] =>
    destruct_match_in e
  | |- context[letS _ := ?e in _] =>
    destruct_match_in e
  | |- context[letS! _ := ?e in _] =>
    destruct_match_in e
  | |- context[letS!? _ := ?e in _] =>
    destruct_match_in e
  end.

Ltac Zify.zify_pre_hook ::=
  autounfold with coq_of_rust_z in *;
  trivial.

Module Integer.
  Module Valid.
    Definition t (kind : IntegerKind.t) (z : Z) : Prop :=
      Integer.min kind <= z <= Integer.max kind.
    Global Hint Unfold t : coq_of_rust_z.
  End Valid.

  Lemma normalize_wrap_is_valid (kind : IntegerKind.t) (z : Z) :
    Integer.Valid.t kind (Integer.normalize_wrap kind z).
  Proof.
    unfold
      Integer.normalize_wrap,
      Integer.Valid.t,
      Integer.min,
      Integer.max.
    destruct kind; cbn; lia.
  Qed.

  Lemma normalize_with_error_eq (kind : IntegerKind.t) (z z' : Z) :
    Integer.normalize_option kind z = Some z' ->
    Valid.t kind z /\
    z' = z.
  Proof.
    unfold Integer.normalize_option, Valid.t.
    repeat destruct (_ <? _) eqn:? in |- *; try congruence.
    split; [lia | congruence].
  Qed.
End Integer.

Module BinOp.
  Module Error.
    Lemma add_is_valid (kind : IntegerKind.t) (z1 z2 z : Z)
      (H_z1 : Integer.Valid.t kind z1)
      (H_z2 : Integer.Valid.t kind z2)
      (H_v :
        BinOp.Wrap.add (Value.Integer kind z1) (Value.Integer kind z2) =
        M.pure (Value.Integer kind z)
      ) :
      Integer.Valid.t kind z.
    Proof.
      unfold
        Integer.Valid.t,
        BinOp.Wrap.add,
        BinOp.Wrap.make_arithmetic
        in *.
      rewrite IntegerKind.eqb_refl in H_v.
      simpl in H_v.
      injection H_v; clear H_v; intro H_v; rewrite <- H_v.
      apply Integer.normalize_wrap_is_valid.
    Qed.
  End Error.
End BinOp.

Module List.
  Lemma Forall_nth_error {A : Set} (P : A -> Prop) (l : list A) (n : nat)
      (H_l : List.Forall P l) :
    match List.nth_error l n with
    | Some x => P x
    | None => True
    end.
  Proof.
    generalize dependent n.
    induction H_l; intros; destruct n; cbn; sfirstorder.
  Qed.
End List.
