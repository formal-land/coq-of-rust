(* Generated file for the links. Do not edit. *)
Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require links.core.marker.
Require links.core.ptr.non_null.

Import Run.

Module Unique.
  Record t (T: Set) `{Link T} : Set := {
    pointer: core.ptr.non_null.NonNull.t T;
    _marker: core.marker.PhantomData.t T;
  }.
End Unique.
