Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.

Import simulations.M.Notations.

Module u8.
  Inductive t : Set :=
  | Make (_ : Z).

  Global Instance IsToValue : ToValue t := {
    Φ := Ty.path "u8";
    φ '(Make x) := Value.Integer Integer.U8 x;
  }.

  Definition get : t -> Z := fun '(Make x) => x.
End u8.

Module u16.
  Inductive t : Set :=
  | Make (_ : Z).

  Global Instance IsToValue : ToValue t := {
    Φ := Ty.path "u16";
    φ '(Make x) := Value.Integer Integer.U16 x;
  }.

  Definition get : t -> Z := fun '(Make x) => x.
End u16.

Module u32.
  Inductive t : Set :=
  | Make (_ : Z).

  Global Instance IsToValue : ToValue t := {
    Φ := Ty.path "u32";
    φ '(Make x) := Value.Integer Integer.U32 x;
  }.

  Definition get : t -> Z := fun '(Make x) => x.
End u32.

Module u64.
  Inductive t : Set :=
  | Make (_ : Z).

  Global Instance IsToValue : ToValue t := {
    Φ := Ty.path "u64";
    φ '(Make x) := Value.Integer Integer.U64 x;
  }.

  Definition get : t -> Z := fun '(Make x) => x.
End u64.

Module u128.
  Inductive t : Set :=
  | Make (_ : Z).

  Global Instance IsToValue : ToValue t := {
    Φ := Ty.path "u128";
    φ '(Make x) := Value.Integer Integer.U128 x;
  }.

  Definition get : t -> Z := fun '(Make x) => x.
End u128.

Module usize.
  Inductive t : Set :=
  | Make (_ : Z).

  Global Instance IsToValue : ToValue t := {
    Φ := Ty.path "usize";
    φ '(Make x) := Value.Integer Integer.Usize x;
  }.

  Definition get : t -> Z := fun '(Make x) => x.
End usize.

Module i8.
  Inductive t : Set :=
  | Make (_ : Z).

  Global Instance IsToValue : ToValue t := {
    Φ := Ty.path "i8";
    φ '(Make x) := Value.Integer Integer.I8 x;
  }.

  Definition get : t -> Z := fun '(Make x) => x.
End i8.

Module i16.
  Inductive t : Set :=
  | Make (_ : Z).

  Global Instance IsToValue : ToValue t := {
    Φ := Ty.path "i16";
    φ '(Make x) := Value.Integer Integer.I16 x;
  }.

  Definition get : t -> Z := fun '(Make x) => x.
End i16.

Module i32.
  Inductive t : Set :=
  | Make (_ : Z).

  Global Instance IsToValue : ToValue t := {
    Φ := Ty.path "i32";
    φ '(Make x) := Value.Integer Integer.I32 x;
  }.

  Definition get : t -> Z := fun '(Make x) => x.
End i32.

Module i64.
  Inductive t : Set :=
  | Make (_ : Z).

  Global Instance IsToValue : ToValue t := {
    Φ := Ty.path "i64";
    φ '(Make x) := Value.Integer Integer.I64 x;
  }.

  Definition get : t -> Z := fun '(Make x) => x.
End i64.

Module i128.
  Inductive t : Set :=
  | Make (_ : Z).

  Global Instance IsToValue : ToValue t := {
    Φ := Ty.path "i128";
    φ '(Make x) := Value.Integer Integer.I128 x;
  }.

  Definition get : t -> Z := fun '(Make x) => x.
End i128.

Module isize.
  Inductive t : Set :=
  | Make (_ : Z).

  Global Instance IsToValue : ToValue t := {
    Φ := Ty.path "isize";
    φ '(Make x) := Value.Integer Integer.Isize x;
  }.

  Definition get : t -> Z := fun '(Make x) => x.
End isize.
