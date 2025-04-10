Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.links.cmpOrdering.
Require Import core.intrinsics.mod.

Instance run_three_way_compare (integer_kind : IntegerKind.t) (x y : Integer.t integer_kind) :
  Run.Trait
    intrinsics.three_way_compare [] [ Φ (Integer.t integer_kind) ] [ φ x; φ y ]
    Ordering.t.
Proof.
Admitted.

Instance run_saturating_add (integer_kind : IntegerKind.t) (x y : Integer.t integer_kind) :
  Run.Trait
    intrinsics.saturating_add [] [ Φ (Integer.t integer_kind) ] [ φ x; φ y ]
    (Integer.t integer_kind).
Proof.
Admitted.

Instance run_saturating_sub (integer_kind : IntegerKind.t) (x y : Integer.t integer_kind) :
  Run.Trait
    intrinsics.saturating_sub [] [ Φ (Integer.t integer_kind) ] [ φ x; φ y ]
    (Integer.t integer_kind).
Proof.
Admitted.

(* pub const unsafe fn transmute<Src, Dst>(_src: Src) -> Dst *)
Instance run_transmute (Src Dst : Set) `{Link Src} `{Link Dst} (src : Src) :
  Run.Trait
    intrinsics.transmute [] [ Φ Src; Φ Dst ] [ φ src ] Dst.
Proof.
Admitted.
