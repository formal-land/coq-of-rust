Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import examples.default.examples.custom.mutations.

(*
struct Numbers {
  a: u64,
  b: u64,
  c: u64,
}
*)
Module Numbers.
  Record t : Set := {
    a : U64.t;
    b : U64.t;
    c : U64.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "mutations::Numbers";
    φ x :=
      Value.StructRecord "mutations::Numbers" [] [] [
        ("a", φ x.(a));
        ("b", φ x.(b));
        ("c", φ x.(c))
      ];
  }.

  Definition of_ty : OfTy.t (Ty.path "mutations::Numbers").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.

  Lemma of_value_with a a' b b' c c' :
    a' = φ a ->
    b' = φ b ->
    c' = φ c ->
    Value.StructRecord "mutations::Numbers" [] [] [
      ("a", a');
      ("b", b');
      ("c", c')
    ] = φ (Build_t a b c).
  Proof. now intros; subst. Qed.
  Smpl Add apply of_value_with : of_value.

  Definition of_value (a : U64.t) a' (b : U64.t) b' (c : U64.t) c' :
    a' = φ a ->
    b' = φ b ->
    c' = φ c ->
    OfValue.t (
      Value.StructRecord "mutations::Numbers" [] [] [
        ("a", a');
        ("b", b');
        ("c", c')
      ]
    ).
  Proof.
    intros.
    eapply OfValue.Make with (A := t).
    apply of_value_with; eassumption.
  Defined.
  Smpl Add eapply of_value : of_value.

  Module SubPointer.
    Definition get_a : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "mutations::Numbers" "a") :=
    {|
      SubPointer.Runner.projection x := Some x.(a);
      SubPointer.Runner.injection x y := Some (x <| a := y |>);
    |}.

    Lemma get_a_is_valid :
      SubPointer.Runner.Valid.t get_a.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_a_is_valid : run_sub_pointer.

    Definition get_b : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "mutations::Numbers" "b") :=
    {|
      SubPointer.Runner.projection x := Some x.(b);
      SubPointer.Runner.injection x y := Some (x <| b := y |>);
    |}.

    Lemma get_b_is_valid :
      SubPointer.Runner.Valid.t get_b.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_b_is_valid : run_sub_pointer.

    Definition get_c : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "mutations::Numbers" "c") :=
    {|
      SubPointer.Runner.projection x := Some x.(c);
      SubPointer.Runner.injection x y := Some (x <| c := y |>);
    |}.

    Lemma get_c_is_valid :
      SubPointer.Runner.Valid.t get_c.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_c_is_valid : run_sub_pointer.
  End SubPointer.
End Numbers.

(* fn get_a_ref(numbers: &Numbers) -> &u64 *)
Instance run_get_a_ref (numbers : Ref.t Pointer.Kind.Ref Numbers.t) :
  Run.Trait get_a_ref [] [] [φ numbers] (Ref.t Pointer.Kind.Ref U64.t).
Proof.
  constructor.
  run_symbolic.
Defined.

(* fn get_b_mut(numbers: &mut Numbers) -> &mut u64 *)
Instance run_get_b_mut (numbers : Ref.t Pointer.Kind.MutRef Numbers.t) :
  Run.Trait get_b_mut [] [] [φ numbers] (Ref.t Pointer.Kind.MutRef U64.t).
Proof.
  constructor.
  run_symbolic.
Defined.

(* fn duplicate(a: &u64, b: &mut u64, c: &mut u64) *)
Instance run_duplicate
    (a : Ref.t Pointer.Kind.Ref U64.t)
    (b : Ref.t Pointer.Kind.MutRef U64.t)
    (c : Ref.t Pointer.Kind.MutRef U64.t) :
  Run.Trait duplicate [] [] [φ a; φ b; φ c] unit.
Proof.
  constructor.
  run_symbolic.
Defined.

(* fn apply_duplicate(numbers: &mut Numbers) *)
Instance run_apply_duplicate (numbers : Ref.t Pointer.Kind.MutRef Numbers.t) :
  Run.Trait apply_duplicate [] [] [φ numbers] unit.
Proof.
  constructor.
  run_symbolic.
Defined.
