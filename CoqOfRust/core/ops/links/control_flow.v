Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.ops.control_flow.

(*
pub enum ControlFlow<B, C = ()> {
    Continue(C),
    Break(B),
}
*)
Module ControlFlow.
  Inductive t {B C : Set} : Set :=
  | Continue (c : C)
  | Break (b : B).
  Arguments t : clear implicits.

  Global Instance IsLink (B C : Set) `{Link B} `{Link C} : Link (t B C) := {
    Φ := Ty.apply (Ty.path "core::ops::control_flow::ControlFlow") [] [Φ B; Φ C];
    φ x := match x with
    | Continue c => Value.StructTuple "core::ops::control_flow::ControlFlow::Continue" [] [Φ B; Φ C] [φ c]
    | Break b => Value.StructTuple "core::ops::control_flow::ControlFlow::Break" [] [Φ B; Φ C] [φ b]
    end;
  }.

  Definition of_ty B_ty C_ty :
    OfTy.t B_ty ->
    OfTy.t C_ty ->
    OfTy.t (Ty.apply (Ty.path "core::ops::control_flow::ControlFlow") [] [B_ty; C_ty]).
  Proof.
    intros [B] [C]; eapply OfTy.Make with (A := t B C); subst; reflexivity.
  Defined.
  Smpl Add apply of_ty : of_ty.

  Lemma of_value_with_Continue {B C : Set} `{Link B} `{Link C}
    (c : C) c' :
    c' = φ c ->
    Value.StructTuple "core::ops::control_flow::ControlFlow::Continue" [] [Φ B; Φ C] [c'] =
    φ (Continue (B := B) (C := C) c).
  Proof.
    intros; subst; reflexivity.
  Qed.
  Smpl Add apply of_value_with_Continue : of_value.

  Lemma of_value_with_Break {B C : Set} `{Link B} `{Link C}
    (b : B) b' :
    b' = φ b ->
    Value.StructTuple "core::ops::control_flow::ControlFlow::Break" [] [Φ B; Φ C] [b'] =
    φ (Break (B := B) (C := C) b).
  Proof.
    intros; subst; reflexivity.
  Qed.
  Smpl Add apply of_value_with_Break : of_value.

  Definition of_value_Continue B' C' c' :
    forall
      (of_ty_B : OfTy.t B')
      (of_value_c : OfValue.t c'),
    C' = Φ (OfValue.get_Set of_value_c) ->
    OfValue.t (Value.StructTuple "core::ops::control_flow::ControlFlow::Continue" [] [B'; C'] [c']).
  Proof.
    intros [B] [C ? c] **.
    eapply OfValue.Make with (A := t B C) (value := Continue c).
    subst.
    now eapply of_value_with_Continue.
  Defined.
  Smpl Add unshelve eapply of_value_Continue : of_value.

  Definition of_value_Break B' C' b' :
    forall
      (of_ty_C : OfTy.t C')
      (of_value_b : OfValue.t b'),
    B' = Φ (OfValue.get_Set of_value_b) ->
    OfValue.t (Value.StructTuple "core::ops::control_flow::ControlFlow::Break" [] [B'; C'] [b']).
  Proof.
    intros [C] [B ? b] **.
    eapply OfValue.Make with (A := t B C) (value := Break b).
    subst.
    now eapply of_value_with_Break.
  Defined.
  Smpl Add unshelve eapply of_value_Break : of_value.

  Module SubPointer.
    Definition get_Continue_0 (B C : Set) `{Link B} `{Link C} :
      SubPointer.Runner.t
        (t B C)
        (Pointer.Index.StructTuple "core::ops::control_flow::ControlFlow::Continue" 0) :=
    {|
      SubPointer.Runner.projection (x : t B C) :=
        match x with
        | Continue c => Some c
        | Break _ => None
        end;
      SubPointer.Runner.injection (x : t B C) (v : C) :=
        match x with
        | Continue _ => Some (Continue v)
        | Break _ => None
        end;
    |}.

    Lemma get_Continue_0_is_valid {B C : Set} `{Link B} `{Link C} :
      SubPointer.Runner.Valid.t (get_Continue_0 B C).
    Proof.
      sauto lq: on.
    Qed.
    Smpl Add apply get_Continue_0_is_valid : run_sub_pointer.

    Definition get_Break_0 (B C : Set) `{Link B} `{Link C} :
      SubPointer.Runner.t
        (t B C)
        (Pointer.Index.StructTuple "core::ops::control_flow::ControlFlow::Break" 0) :=
    {|
      SubPointer.Runner.projection (x : t B C) :=
        match x with
        | Continue _ => None
        | Break b => Some b
        end;
      SubPointer.Runner.injection (x : t B C) (v : B) :=
        match x with
        | Continue _ => None
        | Break _ => Some (Break v)
        end;
    |}.

    Lemma get_Break_0_is_valid {B C : Set} `{Link B} `{Link C} :
      SubPointer.Runner.Valid.t (get_Break_0 B C).
    Proof.
      sauto lq: on.
    Qed.
    Smpl Add apply get_Break_0_is_valid : run_sub_pointer.
  End SubPointer.
End ControlFlow.
