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

  Global Instance I_f32 : Default.Trait f32.t:= {
    default := M.pure (f32.Make 0);
  }.

  Global Instance I_f64 : Default.Trait f64.t:= {
    default := M.pure (f64.Make 0);
  }.

  Global Instance I_i8 : Default.Trait i8.t:= {
    default := M.pure (i8.Make 0);
  }.

  Global Instance I_i16 : Default.Trait i16.t:= {
    default := M.pure (i16.Make 0);
  }.

  Global Instance I_i32 : Default.Trait i32.t:= {
    default := M.pure (i32.Make 0);
  }.

  Global Instance I_i64 : Default.Trait i64.t:= {
    default := M.pure (i64.Make 0);
  }.

  Global Instance I_i128 : Default.Trait i128.t:= {
    default := M.pure (i128.Make 0);
  }.

  Global Instance I_isize : Default.Trait isize.t:= {
    default := M.pure (isize.Make 0);
  }.

  Global Instance I_u8 : Default.Trait u8.t:= {
    default := M.pure (u8.Make 0);
  }.

  Global Instance I_u16 : Default.Trait u16.t:= {
    default := M.pure (u16.Make 0);
  }.

  Global Instance I_u32 : Default.Trait u32.t:= {
    default := M.pure (u32.Make 0);
  }.

  Global Instance I_u64 : Default.Trait u64.t:= {
    default := M.pure (u64.Make 0);
  }.

  Global Instance I_u128 : Default.Trait u128.t:= {
    default := M.pure (u128.Make 0);
  }.

  Global Instance I_unit : Default.Trait unit.
  Admitted.

  Global Instance I_usize : Default.Trait usize.t := {
    default := M.pure (usize.Make 0);
  }.

  Global Instance I_ref_slice {T : Set} {ℋ : Default.Trait T} :
    Default.Trait (ref (slice T)).
  Admitted.

  Global Instance I_mut_ref_slice {T : Set} {ℋ : Default.Trait T} :
    Default.Trait (mut_ref (slice T)).
  Admitted.

  Global Instance I_array {T : Set} {ℋ : Default.Trait T} :
    Default.Trait (array T).
  Admitted.

  Global Instance I_PhantomData {T : Set} {ℋ : Default.Trait T} :
    Default.Trait (core.marker.PhantomData.t T).
  Admitted.

  Global Instance I_tuple_2 {T1 T2 : Set}
    {ℋ_1 : Default.Trait T1}
    {ℋ_2 : Default.Trait T2} :
    Default.Trait (T1 * T2).
  Admitted.

  Global Instance I_tuple_3 {T1 T2 T3 : Set}
    {ℋ_1 : Default.Trait T1}
    {ℋ_2 : Default.Trait T2}
    {ℋ_3 : Default.Trait T3} :
    Default.Trait (T1 * T2 * T3).
  Admitted.

  Global Instance I_tuple_4 {T1 T2 T3 T4 : Set}
    {ℋ_1 : Default.Trait T1}
    {ℋ_2 : Default.Trait T2}
    {ℋ_3 : Default.Trait T3}
    {ℋ_4 : Default.Trait T4} :
    Default.Trait (T1 * T2 * T3 * T4).
  Admitted.

  Global Instance I_tuple_5 {T1 T2 T3 T4 T5 : Set}
    {ℋ_1 : Default.Trait T1}
    {ℋ_2 : Default.Trait T2}
    {ℋ_3 : Default.Trait T3}
    {ℋ_4 : Default.Trait T4}
    {ℋ_5 : Default.Trait T5} :
    Default.Trait (T1 * T2 * T3 * T4 * T5).
  Admitted.

  Global Instance I_tuple_6 {T1 T2 T3 T4 T5 T6 : Set}
    {ℋ_1 : Default.Trait T1}
    {ℋ_2 : Default.Trait T2}
    {ℋ_3 : Default.Trait T3}
    {ℋ_4 : Default.Trait T4}
    {ℋ_5 : Default.Trait T5}
    {ℋ_6 : Default.Trait T6} :
    Default.Trait (T1 * T2 * T3 * T4 * T5 * T6).
  Admitted.

  Global Instance I_tuple_7 {T1 T2 T3 T4 T5 T6 T7 : Set}
    {ℋ_1 : Default.Trait T1}
    {ℋ_2 : Default.Trait T2}
    {ℋ_3 : Default.Trait T3}
    {ℋ_4 : Default.Trait T4}
    {ℋ_5 : Default.Trait T5}
    {ℋ_6 : Default.Trait T6}
    {ℋ_7 : Default.Trait T7} :
    Default.Trait (T1 * T2 * T3 * T4 * T5 * T6 * T7).
  Admitted.

  Global Instance I_tuple_8 {T1 T2 T3 T4 T5 T6 T7 T8 : Set}
    {ℋ_1 : Default.Trait T1}
    {ℋ_2 : Default.Trait T2}
    {ℋ_3 : Default.Trait T3}
    {ℋ_4 : Default.Trait T4}
    {ℋ_5 : Default.Trait T5}
    {ℋ_6 : Default.Trait T6}
    {ℋ_7 : Default.Trait T7}
    {ℋ_8 : Default.Trait T8} :
    Default.Trait (T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8).
  Admitted.

  Global Instance I_tuple_9 {T1 T2 T3 T4 T5 T6 T7 T8 T9 : Set}
    {ℋ_1 : Default.Trait T1}
    {ℋ_2 : Default.Trait T2}
    {ℋ_3 : Default.Trait T3}
    {ℋ_4 : Default.Trait T4}
    {ℋ_5 : Default.Trait T5}
    {ℋ_6 : Default.Trait T6}
    {ℋ_7 : Default.Trait T7}
    {ℋ_8 : Default.Trait T8}
    {ℋ_9 : Default.Trait T9} :
    Default.Trait (T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9).
  Admitted.

  Global Instance I_tuple_10 {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 : Set}
    {ℋ_1 : Default.Trait T1}
    {ℋ_2 : Default.Trait T2}
    {ℋ_3 : Default.Trait T3}
    {ℋ_4 : Default.Trait T4}
    {ℋ_5 : Default.Trait T5}
    {ℋ_6 : Default.Trait T6}
    {ℋ_7 : Default.Trait T7}
    {ℋ_8 : Default.Trait T8}
    {ℋ_9 : Default.Trait T9}
    {ℋ_10 : Default.Trait T10} :
    Default.Trait (T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10).
  Admitted.

  Global Instance I_tuple_11 {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 : Set}
    {ℋ_1 : Default.Trait T1}
    {ℋ_2 : Default.Trait T2}
    {ℋ_3 : Default.Trait T3}
    {ℋ_4 : Default.Trait T4}
    {ℋ_5 : Default.Trait T5}
    {ℋ_6 : Default.Trait T6}
    {ℋ_7 : Default.Trait T7}
    {ℋ_8 : Default.Trait T8}
    {ℋ_9 : Default.Trait T9}
    {ℋ_10 : Default.Trait T10}
    {ℋ_11 : Default.Trait T11} :
    Default.Trait (T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10 * T11).
  Admitted.

  Global Instance I_tuple_12 {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 : Set}
    {ℋ_1 : Default.Trait T1}
    {ℋ_2 : Default.Trait T2}
    {ℋ_3 : Default.Trait T3}
    {ℋ_4 : Default.Trait T4}
    {ℋ_5 : Default.Trait T5}
    {ℋ_6 : Default.Trait T6}
    {ℋ_7 : Default.Trait T7}
    {ℋ_8 : Default.Trait T8}
    {ℋ_9 : Default.Trait T9}
    {ℋ_10 : Default.Trait T10}
    {ℋ_11 : Default.Trait T11}
    {ℋ_12 : Default.Trait T12} :
    Default.Trait (T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10 * T11 * T12).
  Admitted.
End Default_instances.
