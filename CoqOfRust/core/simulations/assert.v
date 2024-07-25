Require Import Coq.Strings.String.
Require Import CoqOfRust.simulations.M.
Import simulations.M.Notations.
Require Import CoqOfRust.core.simulations.bool.
Import simulations.bool.Notations.
Require Import CoqOfRust.core.simulations.eq.
Import simulations.eq.Notations.

Module Assert.
  Module Stateful.
    Definition assert {State : Set} (b : MS? State string bool) :
        MS? State string unit :=
      ifS? b
      then returnS? tt
      else panicS? "assertion failed".

    Definition assert_eq
        {State A : Set} (x y :  MS? State string A) `{Eq.Trait A} :
        MS? State string unit :=
      assert (
        letS? x := x in
        letS? y := y in
        returnS? (x =? y)
      ).
  End Stateful.

  Definition assert {State : Set} (b : bool) :
      MS? State string unit :=
    Stateful.assert (returnS? b).

  Definition assert_eq
      {State A : Set} (x y : A) `{Eq.Trait A} :
      MS? State string unit :=
    Stateful.assert_eq (returnS? x) (returnS? y).

  Definition test {State : Set} (x : MS? State string unit) (s : State) : Prop :=
    fst (x s) = return!? tt.
End Assert.

Module Notations.
  Notation "assertS?" := Assert.assert.
  Notation "assert_eqS?" := Assert.assert_eq.

  Notation "assertS?ofS?" := Assert.Stateful.assert.
  Notation "assert_eqS?ofS?" := Assert.Stateful.assert_eq.

  Notation "testS?" := Assert.test.
End Notations.
