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
