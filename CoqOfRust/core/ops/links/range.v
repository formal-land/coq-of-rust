Require Import CoqOfRust.CoqOfRust.
Require Import core.links.cmp.
Require Import links.M.

(*
  pub struct Range<Idx> {
      pub start: Idx,
      pub end: Idx,
  }
*)
Module Range.
  Record t {Idx : Set} : Set := {
    start : Idx;
    end_ : Idx;
  }.
  Arguments t : clear implicits.

  Global Instance IsLink (Idx : Set) `{Link Idx} : Link (t Idx) := {
    Φ :=
      Ty.apply (Ty.path "core::ops::range::Range") [] [ Φ Idx ];
    φ x :=
      Value.StructRecord "core::ops::range::Range" [
        ("start", φ x.(start));
        ("end", φ x.(end_))
      ];
  }.
End Range.

(*
  pub enum Bound<T> {
    Included(T),
    Excluded(T),
    Unbounded,
  }
*)
Module Bound.
  Inductive t {T : Set} : Set :=
  | Included : T -> t
  | Excluded : T -> t
  | Unbounded : t.
  Arguments t : clear implicits.

  Global Instance IsLink {T : Set} `{Link T} : Link (t T) := {
    Φ := Ty.apply (Ty.path "core::ops::Range::Bound") [] [Φ T];
    φ x :=
      match x with
      | Included x => Value.StructTuple "core::ops::Range::Bound::Included" [φ x]
      | Excluded x => Value.StructTuple "core::ops::Range::Bound::Excluded" [φ x]
      | Unbounded => Value.StructTuple "core::ops::Range::Bound::Unbounded" []
      end;
  }.
End Bound.

(*
  pub trait RangeBounds<T: ?Sized> {
    fn start_bound(&self) -> Bound<&T>;
    fn end_bound(&self) -> Bound<&T>;
    fn contains<U>(&self, item: &U) -> bool
    where
        T: PartialOrd<U>,
        U: ?Sized + PartialOrd<T>
    fn is_empty(&self) -> bool
    where
        T: PartialOrd;
  }
*)
Module RangeBounds.
  Definition Run_start_bound (Self : Set) `{Link Self} 
      (T : Set) `{Link T} : Set :=
    {start_bound @
      IsTraitMethod.t "core::ops::RangeBounds" [] [] (Φ Self) "start_bound" start_bound *
      forall (self : Ref.t Pointer.Kind.Ref Self),
        {{ start_bound [] [] [φ self] 🔽 Bound.t (Ref.t Pointer.Kind.Ref T) }}
    }.

  Definition Run_end_bound (Self : Set) `{Link Self} 
      (T : Set) `{Link T} : Set :=
    {end_bound @
      IsTraitMethod.t "core::ops::RangeBounds" [] [] (Φ Self) "end_bound" end_bound *
      forall (self : Ref.t Pointer.Kind.Ref Self),
        {{ end_bound [] [] [φ self] 🔽 Bound.t (Ref.t Pointer.Kind.Ref T) }}
    }.

  Definition Run_contains (Self : Set) `{Link Self} 
      (T : Set) `{Link T}  : Set :=
    {contains @
      IsTraitMethod.t "core::ops::RangeBounds" [] [] (Φ Self) "contains" contains *
      forall 
          (self : Ref.t Pointer.Kind.Ref Self)
          (U : Set) `{Link U}
          (item : Ref.t Pointer.Kind.Ref U)
          (run_Ord_for_T : PartialOrd.Run T T)
          (run_Ord_for_U : PartialOrd.Run U U),
        {{ contains [] [] [φ self; φ item] 🔽 bool }}
    }.

  Definition Run_is_empty (Self : Set) `{Link Self} 
      (T : Set) `{Link T} : Set :=
    {is_empty @ 
      IsTraitMethod.t "core::ops::RangeBounds" [] [] (Φ Self) "is_empty" is_empty *
      forall (self : Ref.t Pointer.Kind.Ref Self)
          (run_Ord_for_T : PartialOrd.Run T T),
        {{ is_empty [] [] [φ self] 🔽 bool }}
    }.

  Record Run (Self : Set) `{Link Self} 
      {T : Set} `{Link T} : Set := {
    start_bound : Run_start_bound Self T;
    end_bound : Run_end_bound Self T;
    contains : Run_contains Self T;
    is_empty : Run_is_empty Self T;
  }.
End RangeBounds.