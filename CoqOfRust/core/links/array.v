Require Import CoqOfRust.CoqOfRust.
Require Import links.M.

Module Array.
  Inductive t (length : Z) (A : Set) : Set :=
  | Make : list A -> t length A.
  Arguments Make {_ _} _.

  Global Instance IsLink (length : Z) (A : Set) (_ : Link A) : Link (t length A) := {
    to_ty :=
      Ty.apply (Ty.path "array") [Value.Integer IntegerKind.Usize length] [to_ty A];
    to_value '(Make x) :=
      Value.Array (List.map to_value x);
  }.
End Array.
