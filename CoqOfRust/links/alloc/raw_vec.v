(* Generated file for the links. Do not edit. *)
Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require links.core.ptr.unique.

Import Run.

Module Cap.
  Inductive t : Set :=
  | Make : usize.t -> t.
End Cap.

Module RawVecInner.
  Record t (A: Set) `{Link A} : Set := {
    ptr: core.ptr.unique.Unique.t u8.t;
    cap: alloc.raw_vec.Cap.t;
    alloc: A;
  }.
End RawVecInner.

Module RawVec.
  Record t (T A: Set) `{Link T} `{Link A} : Set := {
    inner: alloc.raw_vec.RawVecInner.t A;
    _marker: core.marker.PhantomData.t T;
  }.
End RawVec.
