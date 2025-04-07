Require Import CoqOfRust.CoqOfRust.

Module Eq.
  Class Trait (Self : Set) : Set := {
    eqb: Self -> Self -> bool
  }.

  Module Valid.
  (** An equality [equal] is valid when it decides the standard equality [=]. *)
  Definition t {Self : Set} `{Trait Self} (domain : Self -> Prop) : Prop :=
    forall x y,
    domain x -> domain y ->
    (x = y) <-> (eqb x y = true).
  End Valid.
End Eq.

Module Notations.
  Notation "x =? y" := (Eq.eqb x y) (at level 70).
End Notations.
Export Notations.

Global Instance ZIsEq : Eq.Trait Z := {
  Eq.eqb := Z.eqb
}.
