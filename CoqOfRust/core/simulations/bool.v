Require Import Coq.Strings.String.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.lib.lib.
Import simulations.M.Notations.

Module Bool.
  Global Instance IsToTy : ToTy bool := {
    Φ := Ty.path "bool";
  }.

  Global Instance IsToValue : ToValue bool := {
    φ := Value.Bool;
  }.

  Definition and {State Error} (x y : MS? State Error bool) : MS? State Error bool :=
    letS? a := x in
    if negb a
    then
      returnS? false
    else
      letS? b := y in
      returnS? b.
  
  Definition or {State Error} (x y : MS? State Error bool) : MS? State Error bool :=
    letS? a := x in
    if a
    then returnS? true
    else
      letS? b := y in
      returnS? (a && b)%bool.

  Definition not {State Error} (x : MS? State Error bool) : MS? State Error bool :=
    letS? a := x in
    returnS? (negb a).

  Definition if_then_else
        {State Error A}
        (b : MS? State Error bool)
        (x y : MS? State Error A) :
        MS? State Error A :=
    letS? b := b in
    if b
    then x
    else y.
End Bool.

Module Notations.
  Infix "&&S?" := Bool.and (at level 40, left associativity) : bool_scope.
  Infix "||S?" := Bool.or (at level 50, left associativity) : bool_scope.
  Notation "'notS?' b" := (Bool.not b) (at level 60).
  Notation "'ifS?' b 'then' x 'else' y" := (Bool.if_then_else b x y) (at level 200, right associativity).
End Notations.
