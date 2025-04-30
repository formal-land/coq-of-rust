Require Import CoqOfRust.CoqOfRust.
Require Import links.M.

(*
    pub enum Ordering {
        Less = -1,
        Equal = 0,
        Greater = 1,
    }
*)
Module Ordering.
  Inductive t : Set :=
  | Less : t
  | Equal : t
  | Greater : t.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "core::cmp::Ordering";
    φ x :=
      match x with
      | Less => Value.StructTuple "core::cmp::Ordering::Less" [] [] []
      | Equal => Value.StructTuple "core::cmp::Ordering::Equal" [] [] []
      | Greater => Value.StructTuple "core::cmp::Ordering::Greater" [] [] []
      end;
  }.

  Definition of_ty : OfTy.t (Ty.path "core::cmp::Ordering").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.

  Lemma of_value_with_Less :
    Value.StructTuple "core::cmp::Ordering::Less" [] [] [] = φ Less.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_Less : of_value.

  Lemma of_value_with_Equal :
    Value.StructTuple "core::cmp::Ordering::Equal" [] [] [] = φ Equal.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_Equal : of_value.

  Lemma of_value_with_Greater :
    Value.StructTuple "core::cmp::Ordering::Greater" [] [] [] = φ Greater.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_Greater : of_value.

  Definition of_value_Less : OfValue.t (Value.StructTuple "core::cmp::Ordering::Less" [] [] []).
  Proof. eapply OfValue.Make with (value := Less); reflexivity. Defined.
  Smpl Add apply of_value_Less : of_value.

  Definition of_value_Equal : OfValue.t (Value.StructTuple "core::cmp::Ordering::Equal" [] [] []).
  Proof. eapply OfValue.Make with (value := Equal); reflexivity. Defined.
  Smpl Add apply of_value_Equal : of_value.

  Definition of_value_Greater : OfValue.t (Value.StructTuple "core::cmp::Ordering::Greater" [] [] []).
  Proof. eapply OfValue.Make with (value := Greater); reflexivity. Defined.
  Smpl Add apply of_value_Greater : of_value.
End Ordering.
