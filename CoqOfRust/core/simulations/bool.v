Require Import Coq.Strings.String.
Require Import CoqOfRust.simulations.M.
Import simulations.M.Notations.
Require Import CoqOfRust.core.simulations.eq.

Module Bool.
  Definition and {State} (x y : MS! State bool) : MS! State bool :=
    letS! a := x in
    if negb a
    then
      returnS! false
    else
      letS! b := y in
      returnS! b.

  Definition or {State} (x y : MS! State bool) : MS! State bool :=
    letS! a := x in
    if a
    then returnS! true
    else
      letS! b := y in
      returnS! (a && b)%bool.

  Definition not {State} (x : MS! State bool) : MS! State bool :=
    letS! a := x in
    returnS! (negb a).

  Definition if_then_else
        {State A}
        (b : MS! State bool)
        (x y : MS! State A) :
        MS! State A :=
    letS! b := b in
    if b
    then x
    else y.
End Bool.

Module Notations.
  Infix "&&S!" := Bool.and (at level 40, left associativity) : bool_scope.
  Infix "||S!" := Bool.or (at level 50, left associativity) : bool_scope.
  Notation "'notS!' b" := (Bool.not b) (at level 60).
  Notation "'ifS!' b 'then' x 'else' y" := (Bool.if_then_else b x y) (at level 200, right associativity).
End Notations.

Module ImplEq.
  Global Instance I :
    Eq.Trait bool := {
      eqb := Bool.eqb;
    }.
End ImplEq.
