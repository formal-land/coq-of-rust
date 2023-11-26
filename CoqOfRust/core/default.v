Require Import CoqOfRust.lib.lib.
Require CoqOfRust.core.marker.

(* ********TRAITS******** *)
(* 
[x] Default
*)

(* 
pub trait Default: Sized {
    // Required method
    fn default() -> Self;
}
*)
Module Default.
  Class Trait (Self : Set) : Set := {
    default : M Self;
  }.
End Default.

Module Default_instances.
  Global Instance I_ref_str : Default.Trait (ref str.t).
  Admitted.

  Global Instance I_mut_ref_str : Default.Trait (mut_ref str.t).
  Admitted.

  Global Instance I_bool : Default.Trait bool.
  Admitted.

  Global Instance I_char : Default.Trait char.t.
  Admitted.

  Global Instance I_f32 : Default.Trait f32.t.
  Admitted.

  Global Instance I_f64 : Default.Trait f64.t.
  Admitted.

  Global Instance I_i8 : Default.Trait i8.t.
  Admitted.

  Global Instance I_i16 : Default.Trait i16.t.
  Admitted.

  Global Instance I_i32 : Default.Trait i32.t.
  Admitted.

  Global Instance I_i64 : Default.Trait i64.t.
  Admitted.

  Global Instance I_i128 : Default.Trait i128.t.
  Admitted.

  Global Instance I_isize : Default.Trait isize.t.
  Admitted.

  Global Instance I_u8 : Default.Trait u8.t.
  Admitted.

  Global Instance I_u16 : Default.Trait u16.t.
  Admitted.

  Global Instance I_u32 : Default.Trait u32.t.
  Admitted.

  Global Instance I_u64 : Default.Trait u64.t.
  Admitted.

  Global Instance I_u128 : Default.Trait u128.t.
  Admitted.

  Global Instance I_unit : Default.Trait unit.
  Admitted.

  Global Instance I_usize : Default.Trait usize.t := {
    default := M.pure 0;
  }.

  Global Instance I_ref_slice {T : Set} : Default.Trait (ref (slice T)).
  Admitted.

  Global Instance I_mut_ref_slice {T : Set} : Default.Trait (mut_ref (slice T)).
  Admitted.

  Global Instance I_array {T : Set} : Default.Trait (array T).
  Admitted.

  Global Instance I_PhantomData {T : Set} :
    Default.Trait (core.marker.PhantomData.t T).
  Admitted.
End Default_instances.
