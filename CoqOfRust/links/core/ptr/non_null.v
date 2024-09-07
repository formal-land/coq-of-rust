(* Generated file for the links. Do not edit. *)
Require Import CoqOfRust.CoqOfRust.
Require Import links.M.

Import Run.

Module NonNull.
  Record t (T: Set) `{Link T} : Set := {
    pointer: Ref.t Pointer.Kind.ConstPointer T;
  }.
  Arguments Build_t {_ _}.

  Global Instance IsLink (T: Set) `{Link T} : Link (t T) := {
    to_ty := Ty.path "core::ptr::non_null::NonNull";
    to_value '(Build_t pointer) :=
      Value.StructRecord "core::ptr::non_null::NonNull" [
        ("pointer", to_value pointer)
      ];
  }.
End NonNull.
