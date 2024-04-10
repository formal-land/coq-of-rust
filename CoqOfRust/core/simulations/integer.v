Require Import CoqOfRust.CoqOfRust.
Require Import simulations.M.

Module I8.
  Inductive t : Set :=
  | Make (value : Z).

  Global Instance IsToValue : ToValue t := {
    Φ := Ty.path "i8";
    φ '(Make x) := Value.Integer Integer.I8 x;
  }.
End I8.

Module I16.
  Inductive t : Set :=
  | Make (value : Z).

  Global Instance IsToValue : ToValue t := {
    Φ := Ty.path "i16";
    φ '(Make x) := Value.Integer Integer.I16 x;
  }.
End I16.

Module I32.
  Inductive t : Set :=
  | Make (value : Z).

  Global Instance IsToValue : ToValue t := {
    Φ := Ty.path "i32";
    φ '(Make x) := Value.Integer Integer.I32 x;
  }.
End I32.

Module I64.
  Inductive t : Set :=
  | Make (value : Z).

  Global Instance IsToValue : ToValue t := {
    Φ := Ty.path "i64";
    φ '(Make x) := Value.Integer Integer.I64 x;
  }.
End I64.

Module I128.
  Inductive t : Set :=
  | Make (value : Z).

  Global Instance IsToValue : ToValue t := {
    Φ := Ty.path "i128";
    φ '(Make x) := Value.Integer Integer.I128 x;
  }.
End I128.

Module Isize.
  Inductive t : Set :=
  | Make (value : Z).

  Global Instance IsToValue : ToValue t := {
    Φ := Ty.path "isize";
    φ '(Make x) := Value.Integer Integer.Isize x;
  }.
End Isize.

Module U8.
  Inductive t : Set :=
  | Make (value : Z).

  Global Instance IsToValue : ToValue t := {
    Φ := Ty.path "u8";
    φ '(Make x) := Value.Integer Integer.U8 x;
  }.
End U8.

Module U16.
  Inductive t : Set :=
  | Make (value : Z).

  Global Instance IsToValue : ToValue t := {
    Φ := Ty.path "u16";
    φ '(Make x) := Value.Integer Integer.U16 x;
  }.
End U16.

Module U32.
  Inductive t : Set :=
  | Make (value : Z).

  Global Instance IsToValue : ToValue t := {
    Φ := Ty.path "u32";
    φ '(Make x) := Value.Integer Integer.U32 x;
  }.
End U32.

Module U64.
  Inductive t : Set :=
  | Make (value : Z).

  Global Instance IsToValue : ToValue t := {
    Φ := Ty.path "u64";
    φ '(Make x) := Value.Integer Integer.U64 x;
  }.
End U64.

Module U128.
  Inductive t : Set :=
  | Make (value : Z).

  Global Instance IsToValue : ToValue t := {
    Φ := Ty.path "u128";
    φ '(Make x) := Value.Integer Integer.U128 x;
  }.
End U128.

Module Usize.
  Inductive t : Set :=
  | Make (value : Z).

  Global Instance IsToValue : ToValue t := {
    Φ := Ty.path "usize";
    φ '(Make x) := Value.Integer Integer.Usize x;
  }.
End Usize.
