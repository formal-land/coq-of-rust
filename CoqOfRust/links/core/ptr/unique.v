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
  Arguments Build_t {_ _}.

  Global Instance IsLink (T: Set) `{Link T} : Link (t T) := {
    to_ty := Ty.path "core::ptr::unique::Unique";
    to_value '(Build_t pointer _marker) :=
      Value.StructRecord "core::ptr::unique::Unique" [
        ("pointer", to_value pointer);
        ("_marker", to_value _marker)
      ];
  }.
End Unique.
