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
Definition Ordering : Set :=
  M.Val Ordering.t.

(* ********TRAITS******** *)
(* 
Traits
[x] Eq
[x] Ord
[x] PartialEq
[x] PartialOrd
*)
Module PartialEq.
  Module Required.
    Class Trait (Self : Set) {Rhs : Set} : Set := {
      Rhs := Rhs;
      eq : ref Self -> ref Rhs -> M bool;
      ne : option (ref Self -> ref Rhs -> M bool);
    }.
  End Required.

  Module Provided.
    Definition ne {Self Rhs : Set}
        {H0 : Required.Trait Self (Rhs := Rhs)} :
        ref Self -> ref Rhs -> M bool :=
      match Required.ne with
      | Datatypes.Some ne => ne
      | Datatypes.None => fun self other =>
        let* is_eq := Required.eq self other in
        M.pure (negb is_eq)
      end.
  End Provided.

  Class Trait (Self : Set) {Rhs : Set} : Set := {
    Rhs := Rhs;
    eq : ref Self -> ref Rhs -> M bool;
    ne : ref Self -> ref Rhs -> M bool;
  }.

  Global Instance From_Required (Self Rhs : Set)
      {H0 : Required.Trait Self (Rhs := Rhs)} :
      Trait Self (Rhs := Rhs) := {
    eq := Required.eq;
    ne := Provided.ne;
  }.

  Module Default.
    Definition Rhs (Self : Set) : Set := Self.
  End Default.

  Global Instance Method_eq `(Trait) : Notations.Dot "eq" := {
    Notations.dot := eq;
  }.
  Global Instance Method_ne `(Trait) : Notations.Dot "ne" := {
    Notations.dot x y :=
      let* is_eq := eq x y in
      M.pure (negb is_eq);
  }.

  Module Instances.
    Global Instance I_bool : Trait bool (Rhs := bool).
    Admitted.

    Global Instance I_char : Trait char.t (Rhs := char.t).
    Admitted.

    Global Instance I_f32 : Trait f32.t (Rhs := f32.t).
    Admitted.

    Global Instance I_f64 : Trait f64.t (Rhs := f64.t).
    Admitted.

    Global Instance I_i8 : Trait i8.t (Rhs := i8.t).
    Admitted.

    Global Instance I_i16 : Trait i16.t (Rhs := i16.t).
    Admitted.

    Global Instance I_i32 : Trait i32.t (Rhs := i32.t).
    Admitted.

    Global Instance I_i64 : Trait i64.t (Rhs := i64.t).
    Admitted.

    Global Instance I_i128 : Trait i128.t (Rhs := i128.t).
    Admitted.

    Global Instance I_isize : Trait isize.t (Rhs := isize.t).
    Admitted.

    Global Instance I_never : Trait never.t (Rhs := never.t).
    Admitted.

    Global Instance I_str : Trait str.t (Rhs := str.t).
    Admitted.

    Global Instance I_u8 : Trait u8.t (Rhs := u8.t).
    Admitted.

    Global Instance I_u16 : Trait u16.t (Rhs := u16.t).
    Admitted.

    Global Instance I_u32 : Trait u32.t (Rhs := u32.t).
    Admitted.

    Global Instance I_u64 : Trait u64.t (Rhs := u64.t).
    Admitted.

    Global Instance I_u128 : Trait u128.t (Rhs := u128.t).
    Admitted.

    Global Instance I_unit : Trait unit (Rhs := unit).
    Admitted.

    Global Instance I_usize : Trait usize.t (Rhs := usize.t).
    Admitted.

    Global Instance I_ref_ref {A B : Set} :
      Trait A (Rhs := B) -> Trait (ref A) (Rhs := ref B).
    Admitted.

    Global Instance I_Option {T U : Set}
        {ℋ : core.cmp.PartialEq.Trait T (Rhs := U)} :
      core.cmp.PartialEq.Trait
        (core.option.Option.t T)
        (Rhs := core.option.Option.t U).
    Admitted.

    Global Instance I_tuple_2
      {T1 T2 : Set}
      {ℋ1 : Trait T1 (Rhs := T1)}
      {ℋ2 : Trait T2 (Rhs := T2)} :
      Trait (T1 * T2) (Rhs := T1 * T2).
    Admitted.

    Global Instance I_tuple_3
      {T1 T2 T3 : Set}
      {ℋ1 : Trait T1 (Rhs := T1)}
      {ℋ2 : Trait T2 (Rhs := T2)}
      {ℋ3 : Trait T3 (Rhs := T3)} :
      Trait (T1 * T2 * T3) (Rhs := T1 * T2 * T3).
    Admitted.

    Global Instance I_tuple_4
      {T1 T2 T3 T4 : Set}
      {ℋ1 : Trait T1 (Rhs := T1)}
      {ℋ2 : Trait T2 (Rhs := T2)}
      {ℋ3 : Trait T3 (Rhs := T3)}
      {ℋ4 : Trait T4 (Rhs := T4)} :
      Trait (T1 * T2 * T3 * T4) (Rhs := T1 * T2 * T3 * T4).
    Admitted.

    Global Instance I_tuple_5
      {T1 T2 T3 T4 T5 : Set}
      {ℋ1 : Trait T1 (Rhs := T1)}
      {ℋ2 : Trait T2 (Rhs := T2)}
      {ℋ3 : Trait T3 (Rhs := T3)}
      {ℋ4 : Trait T4 (Rhs := T4)}
      {ℋ5 : Trait T5 (Rhs := T5)} :
      Trait (T1 * T2 * T3 * T4 * T5) (Rhs := T1 * T2 * T3 * T4 * T5).
    Admitted.

    Global Instance I_tuple_6
      {T1 T2 T3 T4 T5 T6 : Set}
      {ℋ1 : Trait T1 (Rhs := T1)}
      {ℋ2 : Trait T2 (Rhs := T2)}
      {ℋ3 : Trait T3 (Rhs := T3)}
      {ℋ4 : Trait T4 (Rhs := T4)}
      {ℋ5 : Trait T5 (Rhs := T5)}
      {ℋ6 : Trait T6 (Rhs := T6)} :
      Trait (T1 * T2 * T3 * T4 * T5 * T6) (Rhs := T1 * T2 * T3 * T4 * T5 * T6).
    Admitted.

    Global Instance I_tuple_7
      {T1 T2 T3 T4 T5 T6 T7 : Set}
      {ℋ1 : Trait T1 (Rhs := T1)}
      {ℋ2 : Trait T2 (Rhs := T2)}
      {ℋ3 : Trait T3 (Rhs := T3)}
      {ℋ4 : Trait T4 (Rhs := T4)}
      {ℋ5 : Trait T5 (Rhs := T5)}
      {ℋ6 : Trait T6 (Rhs := T6)}
      {ℋ7 : Trait T7 (Rhs := T7)} :
      Trait
        (T1 * T2 * T3 * T4 * T5 * T6 * T7)
        (Rhs := T1 * T2 * T3 * T4 * T5 * T6 * T7).
    Admitted.

    Global Instance I_tuple_8
      {T1 T2 T3 T4 T5 T6 T7 T8 : Set}
      {ℋ1 : Trait T1 (Rhs := T1)}
      {ℋ2 : Trait T2 (Rhs := T2)}
      {ℋ3 : Trait T3 (Rhs := T3)}
      {ℋ4 : Trait T4 (Rhs := T4)}
      {ℋ5 : Trait T5 (Rhs := T5)}
      {ℋ6 : Trait T6 (Rhs := T6)}
      {ℋ7 : Trait T7 (Rhs := T7)}
      {ℋ8 : Trait T8 (Rhs := T8)} :
      Trait
        (T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8)
        (Rhs := T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8).
    Admitted.

    Global Instance I_tuple_9
      {T1 T2 T3 T4 T5 T6 T7 T8 T9 : Set}
      {ℋ1 : Trait T1 (Rhs := T1)}
      {ℋ2 : Trait T2 (Rhs := T2)}
      {ℋ3 : Trait T3 (Rhs := T3)}
      {ℋ4 : Trait T4 (Rhs := T4)}
      {ℋ5 : Trait T5 (Rhs := T5)}
      {ℋ6 : Trait T6 (Rhs := T6)}
      {ℋ7 : Trait T7 (Rhs := T7)}
      {ℋ8 : Trait T8 (Rhs := T8)}
      {ℋ9 : Trait T9 (Rhs := T9)} :
      Trait
        (T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9)
        (Rhs := T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9).
    Admitted.

    Global Instance I_tuple_10
      {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 : Set}
      {ℋ1 : Trait T1 (Rhs := T1)}
      {ℋ2 : Trait T2 (Rhs := T2)}
      {ℋ3 : Trait T3 (Rhs := T3)}
      {ℋ4 : Trait T4 (Rhs := T4)}
      {ℋ5 : Trait T5 (Rhs := T5)}
      {ℋ6 : Trait T6 (Rhs := T6)}
      {ℋ7 : Trait T7 (Rhs := T7)}
      {ℋ8 : Trait T8 (Rhs := T8)}
      {ℋ9 : Trait T9 (Rhs := T9)}
      {ℋ10 : Trait T10 (Rhs := T10)} :
      Trait
        (T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10)
        (Rhs := T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10).
    Admitted.

    Global Instance I_tuple_11
      {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 : Set}
      {ℋ1 : Trait T1 (Rhs := T1)}
      {ℋ2 : Trait T2 (Rhs := T2)}
      {ℋ3 : Trait T3 (Rhs := T3)}
      {ℋ4 : Trait T4 (Rhs := T4)}
      {ℋ5 : Trait T5 (Rhs := T5)}
      {ℋ6 : Trait T6 (Rhs := T6)}
      {ℋ7 : Trait T7 (Rhs := T7)}
      {ℋ8 : Trait T8 (Rhs := T8)}
      {ℋ9 : Trait T9 (Rhs := T9)}
      {ℋ10 : Trait T10 (Rhs := T10)}
      {ℋ11 : Trait T11 (Rhs := T11)} :
      Trait
        (T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10 * T11)
        (Rhs := T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10 * T11).
    Admitted.

    Global Instance I_tuple_12
      {T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 : Set}
      {ℋ1 : Trait T1 (Rhs := T1)}
      {ℋ2 : Trait T2 (Rhs := T2)}
      {ℋ3 : Trait T3 (Rhs := T3)}
      {ℋ4 : Trait T4 (Rhs := T4)}
      {ℋ5 : Trait T5 (Rhs := T5)}
      {ℋ6 : Trait T6 (Rhs := T6)}
      {ℋ7 : Trait T7 (Rhs := T7)}
      {ℋ8 : Trait T8 (Rhs := T8)}
      {ℋ9 : Trait T9 (Rhs := T9)}
      {ℋ10 : Trait T10 (Rhs := T10)}
      {ℋ11 : Trait T11 (Rhs := T11)}
      {ℋ12 : Trait T12 (Rhs := T12)} :
      Trait
        (T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10 * T11 * T12)
        (Rhs := T1 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10 * T11 * T12).
    Admitted.
  End Instances.
End PartialEq.

Module PartialOrd.
  Module Required.
    Class Trait (Self : Set) {Rhs : Set} : Set := {
      Rhs := Rhs;
      partial_cmp :
        ref Self ->
        ref Rhs ->
        M (core.option.Option.t Ordering.t);
      lt : Datatypes.option (ref Self -> ref Rhs -> M bool);
      le : Datatypes.option (ref Self -> ref Rhs -> M bool);
      gt : Datatypes.option (ref Self -> ref Rhs -> M bool);
      ge : Datatypes.option (ref Self -> ref Rhs -> M bool);
    }.
  End Required.

  Class Trait (Self : Set) {Rhs : Set} : Set := {
    Rhs := Rhs;
    partial_cmp :
      ref Self ->
      ref Rhs ->
      M (core.option.Option.t Ordering.t);
    lt : ref Self -> ref Rhs -> M bool;
    le : ref Self -> ref Rhs -> M bool;
    gt : ref Self -> ref Rhs -> M bool;
    ge : ref Self -> ref Rhs -> M bool;
  }.

  Global Instance From_Required (Self Rhs : Set)
      {H0 : Required.Trait Self (Rhs := Rhs)} :
      Trait Self (Rhs := Rhs) := {
    partial_cmp := Required.partial_cmp;
    lt :=
      match Required.lt with
      | Datatypes.Some lt => lt
      | Datatypes.None => fun self other =>
        let* cmp := Required.partial_cmp self other in
        match cmp with
        | core.option.Option.Some ordering =>
          match ordering with
          | Ordering.Less => M.pure true
          | _ => M.pure false
          end
        | _ => M.pure false
        end
      end;
    le :=
      match Required.lt with
      | Datatypes.Some lt => lt
      | Datatypes.None => fun self other =>
        let* cmp := Required.partial_cmp self other in
        match cmp with
        | core.option.Option.Some ordering =>
          match ordering with
          | Ordering.Less | Ordering.Equal => M.pure true
          | _ => M.pure false
          end
        | _ => M.pure false
        end
      end;
    gt :=
      match Required.lt with
      | Datatypes.Some lt => lt
      | Datatypes.None => fun self other =>
        let* cmp := Required.partial_cmp self other in
        match cmp with
        | core.option.Option.Some ordering =>
          match ordering with
          | Ordering.Greater => M.pure true
          | _ => M.pure false
          end
        | _ => M.pure false
        end
      end;
    ge :=
      match Required.lt with
      | Datatypes.Some lt => lt
      | Datatypes.None => fun self other =>
        let* cmp := Required.partial_cmp self other in
        match cmp with
        | core.option.Option.Some ordering =>
          match ordering with
          | Ordering.Greater | Ordering.Equal => M.pure true
          | _ => M.pure false
          end
        | _ => M.pure false
        end
      end;
  }.

  Module Default.
    Definition Rhs (Self : Set) : Set := Self.
  End Default.

  Module Instances.
    Global Instance I_bool : Trait bool (Rhs := bool).
    Admitted.

    Global Instance I_char : Trait char.t (Rhs := char.t).
    Admitted.

    Global Instance I_f32 : Trait f32.t (Rhs := f32.t).
    Admitted.

    Global Instance I_f64 : Trait f64.t (Rhs := f64.t).
    Admitted.

    Global Instance I_i8 : Trait i8.t (Rhs := i8.t).
    Admitted.

    Global Instance I_i16 : Trait i16.t (Rhs := i16.t).
    Admitted.

    Global Instance I_i32 : Trait i32.t (Rhs := i32.t).
    Admitted.

    Global Instance I_i64 : Trait i64.t (Rhs := i64.t).
    Admitted.

    Global Instance I_i128 : Trait i128.t (Rhs := i128.t).
    Admitted.

    Global Instance I_isize : Trait isize.t (Rhs := isize.t).
    Admitted.

    Global Instance I_never : Trait never.t (Rhs := never.t).
    Admitted.

    Global Instance I_str : Trait str.t (Rhs := str.t).
    Admitted.

    Global Instance I_u8 : Trait u8.t (Rhs := u8.t).
    Admitted.

    Global Instance I_u16 : Trait u16.t (Rhs := u16.t).
    Admitted.

    Global Instance I_u32 : Trait u32.t (Rhs := u32.t).
    Admitted.

    Global Instance I_u64 : Trait u64.t (Rhs := u64.t).
    Admitted.

    Global Instance I_u128 : Trait u128.t (Rhs := u128.t).
    Admitted.

    Global Instance I_unit : Trait unit (Rhs := unit).
    Admitted.

    Global Instance I_usize : Trait usize.t (Rhs := usize.t).
    Admitted.

    Global Instance I_ref_ref {A B : Set} :
      Trait A (Rhs := B) -> Trait (ref A) (Rhs := ref B).
    Admitted.
  End Instances.
End PartialOrd.

(* 
pub trait Eq: PartialEq<Self> { }
 *)
Module Eq.
  Module Required.
    Unset Primitive Projections.
    Class Trait (Self : Set) : Set := {
      L0 :: PartialEq.Trait Self (Rhs := PartialEq.Default.Rhs Self);
      assert_receiver_is_total_eq :
        Datatypes.option (ref Self -> M unit);
    }.
    Global Set Primitive Projections.
  End Required.

  Module Provided.
    Definition assert_receiver_is_total_eq {Self : Set}
        {H0 : Required.Trait Self} :
        ref Self -> M unit :=
      match Required.assert_receiver_is_total_eq with
      | Datatypes.Some assert_receiver_is_total_eq =>
        assert_receiver_is_total_eq
      | Datatypes.None => fun _ => M.pure tt
      end.
  End Provided.

  Unset Primitive Projections.
  Class Trait (Self : Set) : Set := {
    L0 :: PartialEq.Trait Self (Rhs := PartialEq.Default.Rhs Self);
    assert_receiver_is_total_eq : ref Self -> M unit;
  }.
  Global Set Primitive Projections.

  #[refine]
  Global Instance From_Required (Self : Set)
      {H0 : Required.Trait Self} :
      Trait Self := {
    assert_receiver_is_total_eq := Provided.assert_receiver_is_total_eq;
  }.
    match goal with H : _ |- _ => apply H end.
  Defined.

  Module Impl_Eq_for_str.
    Global Instance I : Required.Trait str.t := {
      assert_receiver_is_total_eq := Datatypes.None;
    }.
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
  Class Trait (Self : Set) := {
    _ :: Eq.Trait Self;
    _ :: PartialOrd.Trait Self (Rhs := Self);
    cmp : ref Self -> ref Self -> M Ordering;
  }.

  Module Impl_Ord_for_str.
    Global Instance I : Trait str.t. Admitted.
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
