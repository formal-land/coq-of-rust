Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.

(* pub struct Map<I, F> { /* private fields */ } *)
Module Map.
  Parameter t : forall (I F : Set), Set.

  Parameter to_value : forall (I F : Set), t I F -> Value.t.

  Global Instance IsLink (I F : Set) `{Link I} `{Link F}: Link (t I F) := {
    Φ := Ty.apply (Ty.path "core::iter::adapters::map::Map") [] [Φ I; Φ F];
    φ := to_value I F;
  }.

  Definition of_ty (I' F' : Ty.t) :
    OfTy.t I' ->
    OfTy.t F' ->
    OfTy.t (Ty.apply (Ty.path "core::iter::adapters::map::Map") [] [I'; F']).
  Proof.
    intros [I] [F].
    eapply OfTy.Make with (A := t I F).
    now subst.
  Defined.
  Smpl Add unshelve eapply of_ty : of_ty.
End Map.
