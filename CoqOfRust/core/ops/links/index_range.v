Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.ops.index_range.

(*
pub struct IndexRange {
    start: usize,
    end: usize,
}
*)
Module IndexRange.
  Record t : Set := {
    start : Usize.t;
    end_ : Usize.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "core::ops::index_range::IndexRange";
    φ x := Value.StructRecord "core::ops::index_range::IndexRange" [] [] [
      ("start", φ x.(start));
      ("end_", φ x.(end_))
    ];
  }.

  Definition of_ty : OfTy.t (Ty.path "core::ops::index_range::IndexRange").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.

  Lemma of_value_with start start' end_ end_' :
    start' = φ start ->
    end_' = φ end_ ->
    Value.StructRecord "core::ops::index_range::IndexRange" [] [] [
      ("start", start');
      ("end_", end_')
    ] = φ (Build_t start end_).
  Proof. now intros; subst. Qed.
  Smpl Add apply of_value_with : of_value.

  Definition of_value (start : Usize.t) start' (end_ : Usize.t) end_' :
    start' = φ start ->
    end_' = φ end_ ->
    OfValue.t (Value.StructRecord "core::ops::index_range::IndexRange" [] [] [
      ("start", start');
      ("end_", end_')
    ]).
  Proof. econstructor; apply of_value_with; eassumption. Defined.
  Smpl Add eapply of_value : of_value.

  Module SubPointer.
    Definition get_start : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "core::ops::index_range::IndexRange" "start") :=
    {|
      SubPointer.Runner.projection x := Some x.(start);
      SubPointer.Runner.injection x y := Some (x <| start := y |>);
    |}.

    Lemma get_start_is_valid :
      SubPointer.Runner.Valid.t get_start.
    Proof.
      now constructor.
    Qed.
  End SubPointer.
End IndexRange.
