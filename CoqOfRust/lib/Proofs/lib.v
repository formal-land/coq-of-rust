Require Import CoqOfRust.lib.lib.
Require Import CoqOfRust.Proofs.M.
Require CoqOfRust.Simulations.M.

(* Proof libraries that we can use everywhere. *)
Require Export Lia.
From Hammer Require Export Tactics.

Import Simulations.M.Notations.

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
    Definition t {A : Set} `{Integer.C A} (v : A) : Prop :=
      Integer.min <= Integer.to_Z v <= Integer.max.
  End Valid.

  Module C.
    Module Valid.
      Record t (A : Set) `{Integer.C A} : Prop := {
        to_of_Z z : Integer.to_Z (Integer.of_Z z) = z;
        of_to_Z v : Integer.of_Z (Integer.to_Z v) = v;
      }.
    End Valid.

    Lemma u8_valid : Valid.t u8.t.
    Proof.
      sauto lq: on.
    Qed.

    Lemma u16_valid : Valid.t u16.t.
    Proof.
      sauto lq: on.
    Qed.

    Lemma u32_valid : Valid.t u32.t.
    Proof.
      sauto lq: on.
    Qed.

    Lemma u64_valid : Valid.t u64.t.
    Proof.
      sauto lq: on.
    Qed.

    Lemma u128_valid : Valid.t u128.t.
    Proof.
      sauto lq: on.
    Qed.

    Lemma usize_valid : Valid.t usize.t.
    Proof.
      sauto lq: on.
    Qed.

    Lemma i8_valid : Valid.t i8.t.
    Proof.
      sauto lq: on.
    Qed.

    Lemma i16_valid : Valid.t i16.t.
    Proof.
      sauto lq: on.
    Qed.

    Lemma i32_valid : Valid.t i32.t.
    Proof.
      sauto lq: on.
    Qed.

    Lemma i64_valid : Valid.t i64.t.
    Proof.
      sauto lq: on.
    Qed.

    Lemma i128_valid : Valid.t i128.t.
    Proof.
      sauto lq: on.
    Qed.

    Lemma isize_valid : Valid.t isize.t.
    Proof.
      sauto lq: on.
    Qed.
  End C.
End Integer.

Module BinOp.
  Module Error.
    Lemma add_eq {A : Set} `{Integer.C A} (z1 z2 z : Z) :
      Integer.C.Valid.t A ->
      BinOp.Error.add (Integer.of_Z z1) (Integer.of_Z z2) =
        inl (Integer.of_Z z) ->
      z = (z1 + z2)%Z.
    Proof.
      unfold
        BinOp.Error.add,
        BinOp.Error.make_arithmetic,
        Integer.normalize_error.
      sauto.
    Qed.

    Lemma add_is_valid {A : Set} `{Integer.C A} (v1 v2 v : A)
      (H_C : Integer.C.Valid.t A)
      (H_v1 : Integer.Valid.t v1)
      (H_v2 : Integer.Valid.t v2)
      (H_v : BinOp.Error.add v1 v2 = inl v) :
      Integer.Valid.t v.
    Proof.
      unfold
        Integer.Valid.t,
        BinOp.Error.add,
        BinOp.Error.make_arithmetic,
        Integer.normalize_error
        in *.
      repeat destruct (_ <? _) eqn:? in H_v; try congruence.
      sauto lq: on solve: lia.
    Qed.
  End Error.
End BinOp.
