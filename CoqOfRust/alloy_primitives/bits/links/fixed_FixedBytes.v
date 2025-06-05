Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.links.array.

(* pub struct FixedBytes<const N: usize>(pub [u8; N]); *)
Module FixedBytes.
  Record t {N : Usize.t} : Set := {
    value : array.t U8.t N;
  }.
  Arguments t : clear implicits.

  Global Instance IsLink (N : Usize.t) : Link (t N) := {
    Φ := Ty.apply (Ty.path "alloy_primitives::bits::fixed::FixedBytes") [ φ N ] [];
    φ x := Value.StructTuple "alloy_primitives::bits::fixed::FixedBytes" [φ N] [] [φ x.(value)];
  }.

  Definition of_ty (N' : Value.t) (N : Usize.t) :
    N' = φ N ->
    OfTy.t (Ty.apply (Ty.path "alloy_primitives::bits::fixed::FixedBytes") [ N' ] []).
  Proof.
    intros.
    eapply OfTy.Make with (A := t N).
    now subst.
  Defined.
  Smpl Add unshelve eapply of_ty : of_ty.

  Lemma of_value_with (N' : Value.t) (N : Usize.t) (value : array.t U8.t N) (value' : Value.t) :
    N' = φ N ->
    value' = φ value ->
    Value.StructTuple "alloy_primitives::bits::fixed::FixedBytes" [N'] [] [value'] =
    φ (Build_t N value).
  Proof.
    now intros; subst.
  Qed.
  Smpl Add unshelve eapply of_value_with : of_value.

  Definition of_value (N' : Value.t) (N : Usize.t) (value' : Value.t) (value : array.t U8.t N) :
    N' = φ N ->
    value' = φ value ->
    OfValue.t (Value.StructTuple "alloy_primitives::bits::fixed::FixedBytes" [N'] [] [value']).
  Proof.
    intros.
    eapply OfValue.Make with (A := t N) (value := Build_t N value).
    now subst.
  Defined.
  Smpl Add unshelve eapply of_value : of_value.

  Module SubPointer.
    Definition get_0 (N : Usize.t) : SubPointer.Runner.t (t N)
      (Pointer.Index.StructTuple "alloy_primitives::bits::fixed::FixedBytes" 0) :=
    {|
      SubPointer.Runner.projection x := Some x.(value);
      SubPointer.Runner.injection x y := Some (x <| value := y |>);
    |}.

    Lemma get_0_is_valid {N : Usize.t} :
      SubPointer.Runner.Valid.t (get_0 N).
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_0_is_valid : run_sub_pointer.
  End SubPointer.
End FixedBytes.
