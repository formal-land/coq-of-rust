Require Import CoqOfRust.lib.lib.

(* ********STRUCTS******** *)
(*
[x] Saturating
[x] NonZeroI8
[x] NonZeroI16
[x] NonZeroI32
[x] NonZeroI64
[x] NonZeroI128
[x] NonZeroIsize
[x] NonZeroU8
[x] NonZeroU16
[x] NonZeroU32
[x] NonZeroU64
[x] NonZeroU128
[x] NonZeroUsize
[x] ParseFloatError
[x] ParseIntError
[x] TryFromIntError
[x] Wrapping
*)

(* pub struct Saturating<T>(pub T); *)
Module Saturating.
  Parameter t : Set -> Set.
End Saturating.
Definition Saturating := Saturating.t.

(* pub struct NonZeroI8(_); *)
Module NonZeroI8.
  Parameter t : Set.
End NonZeroI8.
Definition NonZeroI8 := NonZeroI8.t.

(* pub struct NonZeroI16(_); *)
Module NonZeroI16.
  Parameter t : Set.
End NonZeroI16.
Definition NonZeroI16 := NonZeroI16.t.

(* pub struct NonZeroI32(_); *)
Module NonZeroI32.
  Parameter t : Set.
End NonZeroI32.
Definition NonZeroI32 := NonZeroI32.t.

(* pub struct NonZeroI64(_); *)
Module NonZeroI64.
  Parameter t : Set.
End NonZeroI64.
Definition NonZeroI64 := NonZeroI64.t.

(* pub struct NonZeroI128(_); *)
Module NonZeroI128.
  Parameter t : Set.
End NonZeroI128.
Definition NonZeroI128 := NonZeroI128.t.

(* pub struct NonZeroIsize(_); *)
Module NonZeroIsize.
  Parameter t : Set.
End NonZeroIsize.
Definition NonZeroIsize := NonZeroIsize.t.

(* pub struct NonZeroU8(_); *)
Module NonZeroU8.
  Parameter t : Set.
End NonZeroU8.
Definition NonZeroU8 := NonZeroU8.t.

(* pub struct NonZeroU16(_); *)
Module NonZeroU16.
  Parameter t : Set.
End NonZeroU16.
Definition NonZeroU16 := NonZeroU16.t.

(* pub struct NonZeroU32(_); *)
Module NonZeroU32.
  Parameter t : Set.
End NonZeroU32.
Definition NonZeroU32 := NonZeroU32.t.

(* pub struct NonZeroU64(_); *)
Module NonZeroU64.
  Parameter t : Set.
End NonZeroU64.
Definition NonZeroU64 := NonZeroU64.t.

(* pub struct NonZeroU128(_); *)
Module NonZeroU128.
  Parameter t : Set.
End NonZeroU128.
Definition NonZeroU128 := NonZeroU128.t.

(* pub struct NonZeroUsize(_); *)
Module NonZeroUsize.
  Parameter t : Set.
End NonZeroUsize.

Module error.
  (* pub struct ParseFloatError { /* private fields */ } *)
  Module ParseFloatError.
    Parameter t : Set.
  End ParseFloatError.
  Definition ParseFloatError := ParseFloatError.t.

  (* pub struct ParseIntError { /* private fields */ } *)
  Module ParseIntError.
    Parameter t : Set.
  End ParseIntError.
  Definition ParseIntError := ParseIntError.t.

  (* pub struct TryFromIntError(_); *)
  Module TryFromIntError.
    Parameter t : Set.
  End TryFromIntError.
  Definition TryFromIntError := TryFromIntError.t.
End error.

(* pub struct Wrapping<T>(pub T); *)
Module Wrapping.
  Parameter t : Set -> Set.
End Wrapping.
Definition Wrapping := Wrapping.t.

(* ********ENUMS******** *)
(*
[x] FpCategory
[x] IntErrorKind
*)
(* 
pub enum FpCategory {
    Nan,
    Infinite,
    Zero,
    Subnormal,
    Normal,
}
*)
Module FpCategory.
  Inductive t : Set := 
  | Nan
  | Infinite
  | Zero
  | Subnormal
  | Normal
  .
End FpCategory.
Definition FpCategory := FpCategory.t.

(* 
#[non_exhaustive]
pub enum IntErrorKind {
    Empty,
    InvalidDigit,
    PosOverflow,
    NegOverflow,
    Zero,
}
*)
Module IntErrorKind.
  Inductive t : Set := 
  | Empty
  | InvalidDigit
  | PosOverflow
  | NegOverflow
  | Zero
  .
End IntErrorKind.
Definition IntErrorKind := IntErrorKind.t.

Module Impl_u32.
  Definition Self : Set := u32.t.

  (* pub const fn to_le_bytes(self) -> [u8; 4] *)
  Parameter to_le_bytes : Self -> M (array u8.t).

  Global Instance AF_to_le_bytes : Notations.DoubleColon Self "to_le_bytes" := {
    Notations.double_colon := to_le_bytes;
  }.
End Impl_u32.
