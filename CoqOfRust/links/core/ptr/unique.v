(* Generated file for the links. Do not edit. *)
Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require links.core.marker.
Require links.core.ptr.non_null.

Import Run.

Module Unique.
  Record t {T: Set} : Set := {
    pointer: core.ptr.non_null.NonNull.t T;
    _marker: core.marker.PhantomData.t T;
  }.
  Arguments Build_t {_}.
  Arguments t : clear implicits.

  Definition current_to_value {T: Set} (x: t T) : Value.t :=
    match x with
    | Build_t pointer _marker =>
      Value.StructRecord "core::ptr::unique::Unique" [
        ("pointer", to_value pointer);
        ("_marker", to_value _marker)
      ]
    end.

  Global Instance IsLink {T: Set} `{Link T} : Link (t T) := {
    to_ty := Ty.path "core::ptr::unique::Unique";
    to_value := to_value
  }.
End Unique.
