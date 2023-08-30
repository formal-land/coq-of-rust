Require Import CoqOfRust.lib.lib.

(* ********RE-EXPORTS******** *)
(*
[ ] bool
[ ] char
[ ] f32
[ ] f64
[ ] i128
[ ] i16
[ ] i32
[ ] i64
[ ] i8
[ ] isize
[ ] str
[ ] u128
[ ] u16
[ ] u32
[ ] u64
[ ] u8
[ ] usize
*)

Module Impl_f32.
  Parameter NAN : f32.

  Global Instance AssociatedFunction_NAN :
    Notation.DoubleColon f32 "NAN" := {
    Notation.double_colon := NAN;
  }.

  Definition Self : Set := f32.

  Parameter to_int_unchecked :
    forall `{H : State.Trait} {Int : Set} (*`{FloatToInt.Trait Int}*),
    Self -> M (H := H) Int.

  Global Instance Method_to_int_unchecked `{State.Trait} {Int : Set} :
    Notation.Dot "to_int_unchecked" := {
    Notation.dot := to_int_unchecked (Int := Int);
  }.
End Impl_f32.
