Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.lib.proofs.lib.
Require Import CoqOfRust.simulations.M.
Require CoqOfRust.core.simulations.option.
Require CoqOfRust.examples.default.examples.ink_contracts.simulations.lib.
Require CoqOfRust.examples.default.examples.ink_contracts.lib.

Module  Mapping.
Section Mapping.
  Context {K V : Set}.
  Context (K_eq_neq : forall (k1 k2 : K), k1 = k2 \/ k1 <> k2).
  Context `(ToValue K) `(ToValue V).

  (** ** Simulations with the implementation on [Value.t]. *)
  Axiom run_empty :
    lib.Mapping.empty =
    φ (simulations.lib.Mapping.empty (K := K) (V := V)).

  Axiom run_get : forall (key : K) (m : simulations.lib.Mapping.t K V),
    lib.Mapping.get (φ key) (φ m) =
    φ (simulations.lib.Mapping.get key m).

  Axiom run_insert :
    forall (key : K) (value : V) (m : simulations.lib.Mapping.t K V),
    lib.Mapping.insert (φ key) (φ value) (φ m) =
    φ (simulations.lib.Mapping.insert key value m).

  Axiom run_sum :
    forall (f : Value.t -> Z) (m : simulations.lib.Mapping.t K V),
    lib.Mapping.sum f (φ m) =
    simulations.lib.Mapping.sum (fun v => f (φ v)) m.

  (** ** [empty] rule *)

  Axiom get_empty : forall (key : K),
    simulations.lib.Mapping.get (K := K) (V := V)
      key
      simulations.lib.Mapping.empty =
    None.

  (** ** [get]/[insert] rules *)

  Axiom get_insert_eq : forall (key : K) (v : V) m,
    simulations.lib.Mapping.get key (simulations.lib.Mapping.insert key v m) =
    Some v.

  Axiom get_insert_neq : forall (k1 k2 : K) (v : V) m,
    k1 <> k2 ->
    simulations.lib.Mapping.get
      k1
      (simulations.lib.Mapping.insert k2 v m) =
    simulations.lib.Mapping.get k1 m.

  (** ** [get/equality] rule *)

  Axiom get_all_equal : forall (m1 m2 : simulations.lib.Mapping.t K V),
    (forall k, simulations.lib.Mapping.get k m1 = simulations.lib.Mapping.get k m2) ->
    m1 = m2.

  Lemma insert_insert (k : K) (v1 v2 : V) m :
    simulations.lib.Mapping.insert
      k
      v2
      (simulations.lib.Mapping.insert k v1 m) =
    simulations.lib.Mapping.insert k v2 m.
  Proof.
    apply get_all_equal; intros k'.
    destruct (K_eq_neq k k') as [H_eq | H_neq].
    { rewrite H_eq.
      now repeat rewrite get_insert_eq.
    }
    { repeat rewrite get_insert_neq; congruence. }
  Qed.

  Lemma insert_id (k : K) (v : V) m :
    simulations.lib.Mapping.get k m = Some v ->
    simulations.lib.Mapping.insert k v m = m.
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
    simulations.lib.Mapping.insert k1 v1
      (simulations.lib.Mapping.insert k2 v2 m) =
    simulations.lib.Mapping.insert k2 v2
      (simulations.lib.Mapping.insert k1 v1 m).
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
    simulations.lib.Mapping.sum (K := K) (V := V)
      f
      simulations.lib.Mapping.empty =
    0.

  Axiom sum_insert : forall f k v m,
    simulations.lib.Mapping.sum (K := K) (V := V)
      f
      (simulations.lib.Mapping.insert k v m) =
    (f v -
      match simulations.lib.Mapping.get k m with
      | None => 0
      | Some v' => f v'
      end +
      simulations.lib.Mapping.sum f m)%Z.

  (** Forall predicate. *)
  Definition Forall (P : K -> V -> Prop) m : Prop :=
    forall k v,
    simulations.lib.Mapping.get k m = Some v ->
    P k v.

  Lemma Forall_insert : forall P k v m,
    Forall P m ->
    P k v ->
    Forall P (simulations.lib.Mapping.insert k v m).
  Proof.
    intros * H_m H_k_v.
    unfold Forall in *.
    intros.
    destruct (K_eq_neq k0 k).
    { subst.
      rewrite get_insert_eq in *.
      congruence.
    }
    { rewrite get_insert_neq in * by congruence.
      now apply H_m.
    }
  Qed.
End Mapping.
End Mapping.
