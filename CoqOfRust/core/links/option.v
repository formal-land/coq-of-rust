Require Import CoqOfRust.CoqOfRust.
Require Import links.M.

Module Option.
  Global Instance IsLink (A : Set) `{Link A} : Link (option A) := {
    Φ := Ty.apply (Ty.path "core::option::Option") [] [Φ A];
    φ x :=
      match x with
      | None => Value.StructTuple "core::option::Option::None" []
      | Some x => Value.StructTuple "core::option::Option::Some" [φ x]
      end;
  }.

  Definition of_ty ty :
    OfTy.t ty ->
    OfTy.t (Ty.apply (Ty.path "core::option::Option") [] [ty]).
  Proof.
    intros [A]; eapply OfTy.Make with (A := option A).
    subst; reflexivity.
  Defined.
  Smpl Add apply of_ty : of_ty.

  Lemma of_value_with_None {A : Set} `{Link A} :
    Value.StructTuple "core::option::Option::None" [] =
    φ (None (A := A)).
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_None : of_value.

  Lemma of_value_with_Some {A : Set} `{Link A} (value : A) value' :
    value' = φ value ->
    Value.StructTuple "core::option::Option::Some" [value'] =
    φ (Some value).
  Proof. intros; subst; reflexivity. Qed.
  Smpl Add apply of_value_with_Some : of_value.

  Definition of_value_None {A : Set} `{Link A} :
    OfValue.t (Value.StructTuple "core::option::Option::None" []).
  Proof. eapply OfValue.Make with (A := option A); apply of_value_with_None. Defined.
  Smpl Add eapply of_value_None : of_value.

  Definition of_value_Some value' :
    OfValue.t value' ->
    OfValue.t (Value.StructTuple "core::option::Option::Some" [value']).
  Proof.
    intros [A]; eapply OfValue.Make with (A := option A).
    apply of_value_with_Some; eassumption.
  Defined.
  Smpl Add eapply of_value_Some : of_value.

  Module SubPointer.
    Definition get_Some_0 {A : Set} `{Link A} :
      SubPointer.Runner.t (option A) (Pointer.Index.StructTuple "core::option::Option::Some" 0) :=
    {|
      SubPointer.Runner.projection (x : option A) := x;
      SubPointer.Runner.injection (x : option A) (v : A) :=
        match x with
        | Some _ => Some (Some v)
        | None => None
        end;
    |}.

    Lemma get_Some_0_is_valid {A : Set} `{Link A} :
      SubPointer.Runner.Valid.t (get_Some_0 (A := A)).
    Proof.
      sauto lq: on.
    Qed.
    Smpl Add apply get_Some_0_is_valid : run_sub_pointer.
  End SubPointer.
End Option.
