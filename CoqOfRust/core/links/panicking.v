Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.fmt.links.mod.
Require Import core.links.option.
Require Import core.panicking.

(* pub const fn panic_fmt(fmt: fmt::Arguments<'_>) -> ! *)
Instance run_panic_fmt (fmt : Arguments.t) :
  Run.Trait panicking.panic_fmt [] [] [φ fmt] Empty_set.
Proof.
  constructor.
  run_symbolic.
Admitted.

(* pub const fn panic(expr: &'static str) -> ! *)
Instance run_panic (expr : Ref.t Pointer.Kind.Ref string) :
  Run.Trait panicking.panic [] [] [φ expr] Empty_set.
Proof.
  constructor.
  run_symbolic.
Admitted.

(*
pub enum AssertKind {
    Eq,
    Ne,
    Match,
}
*)
Module AssertKind.
  Inductive t : Set :=
  | Eq
  | Ne
  | Match.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "core::panicking::AssertKind";
    φ x :=
      match x with
      | Eq => Value.StructTuple "core::panicking::AssertKind::Eq" []
      | Ne => Value.StructTuple "core::panicking::AssertKind::Ne" []
      | Match => Value.StructTuple "core::panicking::AssertKind::Match" []
      end;
  }.

  Definition of_ty : OfTy.t (Ty.path "core::panicking::AssertKind").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.

  Lemma of_value_with_Eq :
    Value.StructTuple "core::panicking::AssertKind::Eq" [] = φ Eq.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_Eq : of_value.

  Lemma of_value_with_Ne :
    Value.StructTuple "core::panicking::AssertKind::Ne" [] = φ Ne.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_Ne : of_value.

  Lemma of_value_with_Match :
    Value.StructTuple "core::panicking::AssertKind::Match" [] = φ Match.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_Match : of_value.

  Definition of_value_Eq :
    OfValue.t (Value.StructTuple "core::panicking::AssertKind::Eq" []).
  Proof. econstructor; apply of_value_with_Eq. Defined.
  Smpl Add apply of_value_Eq : of_value.

  Definition of_value_Ne :
    OfValue.t (Value.StructTuple "core::panicking::AssertKind::Ne" []).
  Proof. econstructor; apply of_value_with_Ne. Defined.
  Smpl Add apply of_value_Ne : of_value.

  Definition of_value_Match :
    OfValue.t (Value.StructTuple "core::panicking::AssertKind::Match" []).
  Proof. econstructor; apply of_value_with_Match. Defined.
  Smpl Add apply of_value_Match : of_value.
End AssertKind.

(*
pub fn assert_failed<T, U>(
    kind: AssertKind,
    left: &T,
    right: &U,
    args: Option<fmt::Arguments<'_>>,
) -> !
*)
Instance run_assert_failed
  (T : Set) `{Link T}
  (U : Set) `{Link U}
  (kind : AssertKind.t)
  (left : Ref.t Pointer.Kind.Ref T)
  (right : Ref.t Pointer.Kind.Ref U)
  (args : option Arguments.t) :
  Run.Trait
    panicking.assert_failed [] [ Φ T; Φ U ] [φ kind; φ left; φ right; φ args]
    Empty_set.
Proof.
  constructor.
  run_symbolic.
Admitted.
