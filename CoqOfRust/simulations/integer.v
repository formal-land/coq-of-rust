(** Here this file we define integer types which are useful for simulations, to make explicit the
    various integer kinds of Rust, in a more precise way than using the [Z] type. *)
Require Import CoqOfRust.CoqOfRust.

Module U8.
  Record t : Set := {
    value : Z;
  }.
End U8.

Module U16.
  Record t : Set := {
    value : Z;
  }.
End U16.

Module U32.
  Record t : Set := {
    value : Z;
  }.
End U32.

Module U64.
  Record t : Set := {
    value : Z;
  }.
End U64.

Module U128.
  Record t : Set := {
    value : Z;
  }.
End U128.

Module I8.
  Record t : Set := {
    value : Z;
  }.
End I8.

Module I16.
  Record t : Set := {
    value : Z;
  }.
End I16.

Module I32.
  Record t : Set := {
    value : Z;
  }.
End I32.

Module I64.
  Record t : Set := {
    value : Z;
  }.
End I64.

Module I128.
  Record t : Set := {
    value : Z;
  }.
End I128.
