Require Import CoqOfRust.CoqOfRust.
Require CoqOfRust.examples.erc20.lib.

Module EmptyState.
  Module State.
    Definition t : Set := Datatypes.unit.
  End State.

  Module Address.
    Definition t : Set := Empty_set.
  End Address.

  Local Instance I : State.Trait State.t Address.t := {
    State.get_Set address := match address with end;
    State.read address := match address with end;
    State.alloc_write address := match address with end;
  }.

  Lemma is_valid : State.Valid.t I.
  Proof.
    sauto lq: on.
  Qed.
End EmptyState.

Module State.
  Definition t : Set := Datatypes.option (erc20.lib.Erc20 (ℋ := EmptyState.I)).
End State.

Module Address.
  Definition t : Set := Datatypes.unit.
End Address.

Local Instance I : State.Trait State.t Address.t := {
  State.get_Set address :=
    match address with
    | tt => erc20.lib.Erc20 (ℋ := EmptyState.I)
    end;
  State.read address state :=
    match address with
    | tt => state
    end;
  State.alloc_write address state value :=
    match address, value with
    | tt, _ => Datatypes.Some (Datatypes.Some value)
    end;
}.

Lemma is_valid : State.Valid.t I.
Proof.
  sauto l: on.
Qed.
