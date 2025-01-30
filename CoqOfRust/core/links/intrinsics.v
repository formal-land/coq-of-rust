Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.links.cmpOrdering.
Require Import core.intrinsics.

Import Run.

Lemma run_three_way_compare (integer_kind : IntegerKind.t) (x y : Integer.t integer_kind) :
  {{ intrinsics.three_way_compare [] [ Φ (Integer.t integer_kind) ] [ φ x; φ y ] 🔽 Ordering.t }}.
Proof.
Admitted.
