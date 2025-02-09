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
End Option.
