Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.slice.iter.

(* pub struct IterMut<'a, T: 'a> { /* private fields */ } *)
Module IterMut.
  Parameter t : forall (T : Set), Set.

  Parameter to_value : forall {T : Set}, t T -> Value.t.

  Global Instance IsLink (T : Set) `{Link T} : Link (t T) := {
    Φ := Ty.apply (Ty.path "core::slice::iter::IterMut") [] [Φ T];
    φ := to_value;
  }.

  Definition of_ty T_ty :
    OfTy.t T_ty ->
    OfTy.t (Ty.apply (Ty.path "core::slice::iter::IterMut") [] [T_ty]).
  Proof.
    intros [T].
    eapply OfTy.Make with (A := t T).
    subst.
    reflexivity.
  Defined.
  Smpl Add apply of_ty : of_ty.
End IterMut.
