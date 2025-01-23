Require Import CoqOfRust.CoqOfRust.
Require Import links.M.

Module Array.
  Inductive t (length : Z) (A : Set) : Set :=
  | Make : list A -> t length A.
  Arguments Make {_ _} _.

  Global Instance IsLink (length : Z) (A : Set) (_ : Link A) : Link (t length A) := {
    Φ :=
      Ty.apply (Ty.path "array") [Value.Integer IntegerKind.Usize length] [Φ A];
    φ '(Make x) :=
      Value.Array (List.map φ x);
  }.
End Array.
