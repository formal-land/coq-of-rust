Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.iter.traits.links.iterator.
Require Import core.slice.iter.

(*
pub struct Iter<'a, T>
where
    T: 'a,
*)
Module Iter.
  Parameter t : forall (T : Set), Set.

  Parameter to_value : forall {T : Set}, t T -> Value.t.

  Global Instance IsLink (T : Set) `{Link T} : Link (t T) := {
    Φ := Ty.apply (Ty.path "core::slice::iter::Iter") [] [Φ T];
    φ := to_value;
  }.

  Definition of_ty T_ty :
    OfTy.t T_ty ->
    OfTy.t (Ty.apply (Ty.path "core::slice::iter::Iter") [] [T_ty]).
  Proof.
    intros [T].
    eapply OfTy.Make with (A := t T).
    subst.
    reflexivity.
  Defined.
  Smpl Add apply of_ty : of_ty.
End Iter.

(* impl<'a, T> Iterator for Iter<'a, T> *)
Module Impl_Iterator_for_Iter.
  Definition Self (T : Set) `{Link T} : Set :=
    Iter.t T.

  (* type Item = &'a T; *)
  Definition Item (T : Set) `{Link T} : Set :=
    Ref.t Pointer.Kind.Ref T.

  Instance run (T : Set) `{Link T} : Iterator.Run (Self T) (Item T).
  Admitted.
End Impl_Iterator_for_Iter.

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

(*
pub struct ChunksExact<'a, T: 'a> {
    v: &'a [T],
    rem: &'a [T],
    chunk_size: usize,
}
*)
Module ChunksExact.
  Parameter t : forall (T : Set), Set.

  Parameter to_value : forall {T : Set}, t T -> Value.t.

  Global Instance IsLink (T : Set) `{Link T} : Link (t T) := {
    Φ := Ty.apply (Ty.path "core::slice::iter::ChunksExact") [] [Φ T];
    φ := to_value;
  }.

  Definition of_ty T_ty :
    OfTy.t T_ty ->
    OfTy.t (Ty.apply (Ty.path "core::slice::iter::ChunksExact") [] [T_ty]).
  Proof.
    intros [T].
    eapply OfTy.Make with (A := t T).
    subst.
    reflexivity.
  Defined.
  Smpl Add apply of_ty : of_ty.
End ChunksExact.

Module Impl_ChunksExact.
  Definition Self (T : Set) `{Link T} : Set :=
    ChunksExact.t T.
    
  (* pub fn remainder(&self) -> &'a [T] *)
  Instance run_remainder
    (T : Set) `{Link T}
    (self : Ref.t Pointer.Kind.Ref (Self T)) :
    Run.Trait (slice.iter.Impl_core_slice_iter_ChunksExact_T.remainder (Φ T)) [] [] [φ self]
      (Ref.t Pointer.Kind.Ref (list T)).
  Admitted.
End Impl_ChunksExact.
Export Impl_ChunksExact.

(* impl<'a, T> Iterator for ChunksExact<'a, T> *)
Module Impl_Iterator_for_ChunksExact.
  Definition Self (T : Set) `{Link T} : Set :=
    ChunksExact.t T.

    (* type Item = &'a [T]; *)
    Definition Item (T : Set) `{Link T} : Set :=
      Ref.t Pointer.Kind.Ref (list T).

    Instance run (T : Set) `{Link T} : Iterator.Run (Self T) (Item T).
    Admitted.
End Impl_Iterator_for_ChunksExact.

(*
pub struct RChunksExact<'a, T: 'a> {
    v: &'a [T],
    rem: &'a [T],
    chunk_size: usize,
}
*)
Module RChunksExact.
  Parameter t : forall (T : Set), Set.

  Parameter to_value : forall {T : Set}, t T -> Value.t.

  Global Instance IsLink (T : Set) `{Link T} : Link (t T) := {
    Φ := Ty.apply (Ty.path "core::slice::iter::RChunksExact") [] [Φ T];
    φ := to_value;
  }.

  Definition of_ty T_ty :
    OfTy.t T_ty ->
    OfTy.t (Ty.apply (Ty.path "core::slice::iter::RChunksExact") [] [T_ty]).
  Proof.
    intros [T].
    eapply OfTy.Make with (A := t T).
    subst.
    reflexivity.
  Defined.
  Smpl Add apply of_ty : of_ty.
End RChunksExact.

(* impl<'a, T> RChunksExact<'a, T> *)
Module Impl_RChunksExact.
  Definition Self (T : Set) : Set :=
    RChunksExact.t T.

  (* pub fn remainder(&self) -> &'a [T] *)
  Instance run_remainder
    (T : Set) `{Link T}
    (self : Ref.t Pointer.Kind.Ref (Self T)) :
    Run.Trait
      (slice.iter.Impl_core_slice_iter_RChunksExact_T.remainder (Φ T)) [] [] [φ self]
      (Ref.t Pointer.Kind.Ref (list T)).
  Admitted.
End Impl_RChunksExact.
Export Impl_RChunksExact.

(* impl<'a, T> Iterator for RChunksExact<'a, T> *)
Module Impl_Iterator_for_RChunksExact.
  Definition Self (T : Set) `{Link T} : Set :=
    RChunksExact.t T.

    (* type Item = &'a [T]; *)
    Definition Item (T : Set) `{Link T} : Set :=
      Ref.t Pointer.Kind.Ref (list T).

    Instance run (T : Set) `{Link T} : Iterator.Run (Self T) (Item T).
    Admitted.
End Impl_Iterator_for_RChunksExact.
