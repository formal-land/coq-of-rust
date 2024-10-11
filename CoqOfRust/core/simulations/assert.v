Require Import Coq.Strings.String.
Require Import CoqOfRust.simulations.M.
Import simulations.M.Notations.
Require Import CoqOfRust.core.simulations.bool.
Import simulations.bool.Notations.
Require Import CoqOfRust.core.simulations.eq.
Import simulations.eq.Notations.

Module Assert.
  Module Stateful.
    Definition assert {State : Set} (b : MS! State bool) :
        MS! State unit :=
      ifS! b
      then returnS! tt
      else panicS! "assertion failed".

    Definition assert_eq
        {State A : Set} (x y :  MS! State A) `{Eq.Trait A} :
        MS! State unit :=
      assert (
        letS! x := x in
        letS! y := y in
        returnS! (x =? y)
      ).
  End Stateful.

  Definition assert_with_message (b : bool) (msg : string) : M! unit :=
    if b then
      return! tt
    else
      panic! msg.

  Definition assert (b : bool) : M! unit :=
    assert_with_message b "assertion failed".

  Definition assert_eq {A : Set} `{Eq.Trait A} (x y : A) : M! unit :=
    assert (x =? y).
End Assert.

Module Notations.
  Notation "assert_with_message!" := Assert.assert_with_message.
  Notation "assert!" := Assert.assert.
  Notation "assert_eq!" := Assert.assert_eq.

  Notation "assertS?ofS?" := Assert.Stateful.assert.
  Notation "assert_eqS?ofS?" := Assert.Stateful.assert_eq.
End Notations.
