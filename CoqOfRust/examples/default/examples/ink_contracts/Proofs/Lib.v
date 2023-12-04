Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.lib.Proofs.lib.
Require Import CoqOfRust.examples.default.examples.ink_contracts.Lib.

Module  Mapping.
Section Mapping.
  Context {K V : Set}.
  Context (K_eq_neq : forall (k1 k2 : K), k1 = k2 \/ k1 <> k2).

  Axiom get_empty : forall k,
    Mapping.get (K := K) (V := V) k Mapping.empty =
    option.Option.None.

  (** ** [get]/[insert] rules *)

  Axiom get_insert_eq : forall (k : K) (v : V) m,
    Mapping.get k (Mapping.insert k v m) = option.Option.Some v.

  Axiom get_insert_neq : forall (k1 k2 : K) (v : V) m,
    k1 <> k2 ->
    Mapping.get k1 (Mapping.insert k2 v m) = Mapping.get k1 m.

  (** ** [get/equality] rule *)

  Axiom get_all_equal : forall (m1 m2 : Lib.Mapping.t K V),
    (forall k, Mapping.get k m1 = Mapping.get k m2) ->
    m1 = m2.

  Lemma insert_insert (k : K) (v1 v2 : V) m :
    Mapping.insert k v2 (Mapping.insert k v1 m) = Mapping.insert k v2 m.
  Proof.
    apply get_all_equal; intros k'.
    destruct (K_eq_neq k k') as [H_eq | H_neq].
    { rewrite H_eq.
      now repeat rewrite get_insert_eq.
    }
    { repeat rewrite get_insert_neq; congruence. }
  Qed.

  Lemma insert_id (k : K) (v : V) m :
    Mapping.get k m = option.Option.Some v ->
    Mapping.insert k v m = m.
  Proof.
    intros H_get.
    apply get_all_equal; intros k'.
    destruct (K_eq_neq k k') as [H_eq | H_neq].
    { rewrite H_eq.
      rewrite get_insert_eq.
      congruence.
    }
    { rewrite get_insert_neq; congruence. }
  Qed.

  Lemma insert_switch (k1 k2 : K) (v1 v2 : V) m :
    k1 <> k2 ->
    Mapping.insert k1 v1 (Mapping.insert k2 v2 m) =
    Mapping.insert k2 v2 (Mapping.insert k1 v1 m).
  Proof.
    intros H_neq.
    apply get_all_equal; intros k'.
    destruct (K_eq_neq k1 k') as [H_eq1 | H_neq1];
      destruct (K_eq_neq k2 k') as [H_eq2 | H_neq2].
    { congruence. }
    { subst.
      rewrite get_insert_eq.
      rewrite get_insert_neq by congruence.
      now rewrite get_insert_eq.
    }
    { subst.
      rewrite get_insert_eq.
      rewrite get_insert_neq by congruence.
      now rewrite get_insert_eq.
    }
    { repeat rewrite get_insert_neq; congruence. }
  Qed.

  (** ** [sum] rules *)

  Axiom sum_empty : forall f,
    Mapping.sum (K := K) (V := V) f Mapping.empty = 0.

  Axiom sum_insert : forall f k v m,
    Mapping.sum (K := K) (V := V) f (Mapping.insert k v m) =
      (f v -
      match Mapping.get k m with
      | option.Option.None => 0
      | option.Option.Some v' => f v'
      end +
      Mapping.sum f m)%Z.

  (** Forall predicate. *)
  Definition Forall (P : K -> V -> Prop) m : Prop :=
    forall k v, Mapping.get k m = option.Option.Some v -> P k v.

  Lemma Forall_insert : forall P k v m,
    Forall P m ->
    P k v ->
    Forall P (Mapping.insert k v m).
  Proof.
    unfold Forall.
    intros.
    destruct (K_eq_neq k0 k);
      hauto q: on use: get_insert_eq, get_insert_neq.
  Qed.
End Mapping.
End Mapping.
