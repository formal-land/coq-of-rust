Require Import CoqOfRust.CoqOfRust.
Require Import links.M.

Record t {A : Set} {length : Usize.t} : Set := {
  value : list A;
}.
Arguments t : clear implicits.

Global Instance IsLink (A : Set) (length : Usize.t) `{Link A} : Link (t A length) := {
  Φ :=
    Ty.apply (Ty.path "array") [ φ length ] [ Φ A ];
  φ x :=
    Value.Array (List.map φ x.(value));
}.

Definition of_ty (length' : Value.t) (length : Usize.t) (A' : Ty.t):
  length' = φ length ->
  OfTy.t A' ->
  OfTy.t (Ty.apply (Ty.path "array") [ length' ] [ A' ]).
Proof. intros ? [A]. eapply OfTy.Make with (A := t A length). now subst. Defined.
Smpl Add eapply of_ty : of_ty.

Lemma of_value_with_0 {A : Set} `{Link A} :
  Value.Array [] =
  φ ({| value := [] |} : t A {| Integer.value := 0 |}).
Proof. now cbn. Qed.
Smpl Add apply of_value_with_0 : of_value.

Lemma of_value_with_1 {A : Set} `{Link A}
    (value1' : Value.t) (value1 : A) :
  value1' = φ value1 ->
  Value.Array [value1'] =
  φ ({| value := [value1] |} : t A {| Integer.value := 1 |}).
Proof. now intros; subst. Qed.
Smpl Add apply of_value_with_1 : of_value.

Definition of_value_1 (value1' : Value.t) :
  OfValue.t value1' ->
  OfValue.t (Value.Array [value1']).
Proof.
  intros [A].
  eapply OfValue.Make with (A := t A {| Integer.value := 1 |}).
  apply of_value_with_1; eassumption.
Defined.
Smpl Add apply of_value_1 : of_value.

(** This lemma is useful when the [repeat_nat] construct (used to build array with repetition)
    appears and to switch it with the [φ] on its parameters. *)
Lemma repeat_nat_φ_eq {A : Set} `{Link A} (times : Z) (value : A) :
  Value.Array (repeat_nat (Z.to_nat times) (φ value)) =
  φ ({| value := repeat_nat (Z.to_nat times) value |} : t A {| Integer.value := times |}).
Proof.
  with_strategy transparent [φ] cbn.
  set (nat_times := Z.to_nat times).
  induction nat_times; cbn; congruence.
Qed.

Lemma repeat_φ_eq {A : Set} `{Link A} (times : Z) (value : A) :
  repeat (φ value) (Value.Integer IntegerKind.Usize times) =
  M.pure (φ ({| value := repeat_nat (Z.to_nat times) value |} : t A {| Integer.value := times |})).
Proof.
  with_strategy transparent [φ repeat] cbn.
  rewrite repeat_nat_φ_eq.
  reflexivity.
Qed.

Lemma of_value_with_repeat {A : Set} `{Link A}
    (times : Z)
    (value' : Value.t) (value : A) :
  value' = φ value ->
  Value.Array (repeat_nat (Z.to_nat times) value') =
  φ ({| value := repeat_nat (Z.to_nat times) value |} : t A {| Integer.value := times |}).
Proof.
  intros; subst.
  now rewrite repeat_nat_φ_eq.
Qed.
Smpl Add eapply of_value_with_repeat : of_value.

Definition of_value_repeat (times : Z) (value' : Value.t) :
  OfValue.t value' ->
  OfValue.t (Value.Array (repeat_nat (Z.to_nat times) value')).
Proof.
  intros [A ? value].
  eapply OfValue.Make with
    (A := t A {| Integer.value := times |})
    (value := {| value := repeat_nat (Z.to_nat times) value |}).
  subst.
  apply repeat_nat_φ_eq.
Defined.
Smpl Add apply of_value_repeat : of_value.

Module SubPointer.
  Definition get_index (A : Set) `{Link A} (length : Usize.t) (index : Z) :
    SubPointer.Runner.t (t A length) (Pointer.Index.Array index) :=
  {|
    SubPointer.Runner.projection x :=
      List.nth_error x.(value) (Z.to_nat index);
    SubPointer.Runner.injection x y :=
      Option.map (List.nth_error x.(value) (Z.to_nat index)) (fun _ =>
      {| value := List.replace_at x.(value) (Z.to_nat index) y |});
  |}.

  Lemma get_index_is_valid {A : Set} `{Link A} {length : Usize.t} (index : Z) :
    SubPointer.Runner.Valid.t (get_index A length index).
  Proof.
    constructor; intros; with_strategy transparent [φ] cbn.
    { now rewrite List.nth_error_map. }
    { rewrite List.nth_error_map.
      destruct List.nth_error; cbn; repeat f_equal.
      now rewrite List.replace_at_map_eq.
    }
  Qed.
  Smpl Add eapply get_index_is_valid : run_sub_pointer.
End SubPointer.
