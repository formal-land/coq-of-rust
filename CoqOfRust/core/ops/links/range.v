Require Import CoqOfRust.CoqOfRust.
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
