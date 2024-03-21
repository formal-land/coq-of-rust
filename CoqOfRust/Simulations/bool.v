Require Import Coq.Strings.String.
Require Import CoqOfRust.Simulations.M.
Require Import CoqOfRust.lib.lib.
Import Simulations.M.Notations.

Module Bool.
  Definition and {State} (x y : MS? State bool.t) : MS? State bool.t :=
    letS? a := x in
    if negb a
    then
      returnS? false
    else
      letS? b := y in
      returnS? b.
  
  Definition or {State} (x y : MS? State bool.t) : MS? State bool.t :=
    letS? a := x in
    if a
    then returnS? true
    else
      letS? b := y in
      returnS? (a && b)%bool.

  Definition not {State} (x : MS? State bool.t) : MS? State bool.t :=
    letS? a := x in
    returnS? (negb a).

  Definition if_then_else {State A} (b : MS? State bool.t) (x y : MS? State A) : MS? State A :=
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