Require Import CoqOfRust.lib.lib.

Require CoqOfRust.core.option.
Require Import CoqOfRust.core.marker.

(* ********STRUCTS******** *)
(* [x] Reverse *)
(* pub struct Reverse<T>(pub T); *)
Module Reverse.
  Record t (T : Set) : Set := { _1 : T }.
End Reverse.
Definition Reverse := Reverse.t.

(* ********ENUMS******** *)
(* 
[x] Ordering
*)
Module Ordering.
  Inductive t : Set :=
  | Less : t
  | Greater : t
  | Equal : t.
End Ordering.
Definition Ordering := Ordering.t.

(* ********TRAITS******** *)
(* 
Traits
[x] Eq
[x] Ord
[x] PartialEq
[x] PartialOrd
*)
Module PartialEq.
  Class Trait (Self : Set) {Rhs : Set} `{State.Trait} : Set := {
    Rhs := Rhs;

    eq : ref Self -> ref Rhs -> M bool;
  }.

  Module Default.
    Definition Rhs (Self : Set) : Set := Self.
  End Default.

  Global Instance Method_eq `(Trait) : Notation.Dot "eq" := {
    Notation.dot := eq;
  }.
  Global Instance Method_ne `(Trait) : Notation.Dot "ne" := {
    Notation.dot x y :=
      let* is_eq := eq x y in
      let* is_eq := M.read is_eq in
      Pure (negb is_eq);
  }.

  Module Instances. Section Instances.
    Context `{State.Trait}.

    Global Instance I_bool : Trait bool (Rhs := bool).
    Admitted.

    Global Instance I_char : Trait char (Rhs := char).
    Admitted.

    Global Instance I_f32 : Trait f32 (Rhs := f32).
    Admitted.

    Global Instance I_f64 : Trait f64 (Rhs := f64).
    Admitted.

    Global Instance I_i8 : Trait i8 (Rhs := i8).
    Admitted.

    Global Instance I_i16 : Trait i16 (Rhs := i16).
    Admitted.

    Global Instance I_i32 : Trait i32 (Rhs := i32).
    Admitted.

    Global Instance I_i64 : Trait i64 (Rhs := i64).
    Admitted.

    Global Instance I_i128 : Trait i128 (Rhs := i128).
    Admitted.

    Global Instance I_isize : Trait isize (Rhs := isize).
    Admitted.

    Global Instance I_never : Trait never (Rhs := never).
    Admitted.

    Global Instance I_str : Trait str (Rhs := str).
    Admitted.

    Global Instance I_u8 : Trait u8 (Rhs := u8).
    Admitted.

    Global Instance I_u16 : Trait u16 (Rhs := u16).
    Admitted.

    Global Instance I_u32 : Trait u32 (Rhs := u32).
    Admitted.

    Global Instance I_u64 : Trait u64 (Rhs := u64).
    Admitted.

    Global Instance I_u128 : Trait u128 (Rhs := u128).
    Admitted.

    Global Instance I_unit : Trait unit (Rhs := unit).
    Admitted.

    Global Instance I_usize : Trait usize (Rhs := usize).
    Admitted.

    Global Instance I_ref_ref {A B : Set} :
      Trait A (Rhs := B) -> Trait (ref A) (Rhs := ref B).
    Admitted.
  End Instances. End Instances.
End PartialEq.

Module PartialOrd.
  Class Trait `{State.Trait} (Self : Set) {Rhs : Set} : Set := {
    Rhs := Rhs;
    partial_cmp :
      ref Self -> ref Self -> M (core.option.Option (Ordering.t));

    (* lt `{State.Trait} : ref Self -> ref Rhs -> M bool;
    le `{State.Trait} : ref Self -> ref Rhs -> M bool;
    gt `{State.Trait} : ref Self -> ref Rhs -> M bool;
    ge `{State.Trait} : ref Self -> ref Rhs -> M bool; *)
  }.

  Module Default.
    Definition Rhs (Self : Set) : Set := Self.
  End Default.

  Global Instance Method_partial_cmp `{State.Trait} `(Trait) :
    Notation.Dot "partial_cmp" := {
    Notation.dot := partial_cmp;
  }.
  (* Global Instance Method_lt `{State.Trait} `(Trait) : Notation.Dot "lt" := {
    Notation.dot := lt;
  }.
  Global Instance Method_le `{State.Trait} `(Trait) : Notation.Dot "le" := {
    Notation.dot := le;
  }.
  Global Instance Method_gt `{State.Trait} `(Trait) : Notation.Dot "gt" := {
    Notation.dot := gt;
  }.
  Global Instance Method_ge `{State.Trait} `(Trait) : Notation.Dot "ge" := {
    Notation.dot := ge;
  }. *)
  Module Impl_PartialOrd_for_str.
    Global Instance I `{State.Trait} : Trait str (Rhs := str). Admitted.
  End Impl_PartialOrd_for_str.
End PartialOrd.

(* 
pub trait Eq: PartialEq<Self> { }
 *)
Module Eq.
  Unset Primitive Projections.
  Class Trait `{State.Trait} (Self : Set) : Set := {
    _ :: PartialEq.Trait Self (Rhs := PartialEq.Default.Rhs Self);
  }.
  Set Primitive Projections.

  Module Impl_Eq_for_str.
    Global Instance I `{State.Trait} : Trait str := {}.
  End Impl_Eq_for_str.
End Eq.

(* 
pub trait Ord: Eq + PartialOrd<Self> {
    // Required method
    fn cmp(&self, other: &Self) -> Ordering;

    // Provided methods
    fn max(self, other: Self) -> Self
       where Self: Sized { ... }
    fn min(self, other: Self) -> Self
       where Self: Sized { ... }
    fn clamp(self, min: Self, max: Self) -> Self
       where Self: Sized + PartialOrd<Self> { ... }
}
*)
Module Ord.
  Class Trait `{State.Trait} (Self : Set) := {
    _ :: Eq.Trait Self;
    _ :: PartialOrd.Trait Self (Rhs := Self);
    cmp : ref Self -> ref Self -> M (H := H) Ordering;
  }.

  Module Impl_Ord_for_str.
    Global Instance I `{State.Trait} : Trait str. Admitted.
  End Impl_Ord_for_str.
End Ord.

(* ********FUNCTIONS******** *)
(* 
[ ] max
[ ] max_by
[ ] max_by_key
[ ] min
[ ] min_by
[ ] min_by_key
*)

(* **********IMPLS********** *)
(*
// Implementation of PartialEq, Eq, PartialOrd and Ord for primitive types
*)
Module Impls.
  (*
  impl PartialEq for () {
      #[inline]
      fn eq(&self, _other: &()) -> bool {
          true
      }
      #[inline]
      fn ne(&self, _other: &()) -> bool {
          false
      }
  }
  *)
  Module Impl_PartialEq_for_unit.
    Definition eq `{State.Trait} (x y : ref unit) : M bool :=
      let* result := M.alloc true in
      Pure result.

    Global Instance I `{State.Trait} :
      PartialEq.Trait unit (Rhs := PartialEq.Default.Rhs unit) := {
      eq := eq;
    }.
  End Impl_PartialEq_for_unit.
End Impls.
