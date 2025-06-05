Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.iter.traits.links.iterator.

(*
pub struct IntoIter<T, A = Global>
where
    A: Allocator,
{ /* private fields */ }
*)
Module IntoIter.
  Parameter t : forall (T A : Set), Set.

  Parameter to_value : forall (T A : Set), t T A -> Value.t.

  Global Instance IsLink (T A : Set) `{Link T} `{Link A}: Link (t T A) := {
    Φ := Ty.apply (Ty.path "alloc::vec::into_iter::IntoIter") [] [Φ T; Φ A];
    φ := to_value T A;
  }.

  Definition of_ty (T' A' : Ty.t) :
    OfTy.t T' ->
    OfTy.t A' ->
    OfTy.t (Ty.apply (Ty.path "alloc::vec::into_iter::IntoIter") [] [T'; A']).
  Proof.
    intros [T] [A].
    eapply OfTy.Make with (A := t T A).
    now subst.
  Defined.
  Smpl Add unshelve eapply of_ty : of_ty.
End IntoIter.

(*
impl<T, A: Allocator> Iterator for IntoIter<T, A> {
    type Item = T;
*)
Module Impl_Iterator_for_IntoIter.
  Definition Self (T A : Set) : Set :=
    IntoIter.t T A.

  Instance run (T A : Set) `{Link T} `{Link A} :
    Iterator.Run (Self T A) T.
  Admitted.
End Impl_Iterator_for_IntoIter.
Export Impl_Iterator_for_IntoIter.
