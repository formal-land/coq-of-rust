Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.core.simulations.unit.
Require Import CoqOfRust.core.simulations.result.
Require Import CoqOfRust.core.simulations.assert.
Require Import CoqOfRust.move_sui.simulations.move_abstract_stack.lib.
Import simulations.M.Notations.
Import simulations.assert.Notations.

(*
  #[test]
  fn test_empty_stack() {
      let mut empty = AbstractStack::<usize>::new();
      assert!(empty.is_empty());

      // pop on empty stack
      assert_eq!(empty.pop(), Err(AbsStackError::Underflow));
      assert_eq!(empty.pop_any_n(nonzero(1)), Err(AbsStackError::Underflow));
      assert_eq!(empty.pop_any_n(nonzero(100)), Err(AbsStackError::Underflow));
      assert_eq!(empty.pop_eq_n(nonzero(12)), Err(AbsStackError::Underflow));
      assert_eq!(empty.pop_eq_n(nonzero(112)), Err(AbsStackError::Underflow));

      assert!(empty.is_empty());
  }
*)

Definition test_empty_stack :
    MS? (AbstractStack.t Z) string unit :=
  letS? empty := readS? in
  letS? _ := assertS? (AbstractStack.self_is_empty) in
  letS? _ :=
    assert_eqS?
      (AbstractStack.pop)
      (returnS? (Result.Err AbsStackError.Underflow)) in
  letS? _ :=
    assert_eqS?
      (AbstractStack.pop_any_n 1)
      (returnS? (Result.Err AbsStackError.Underflow)) in
  letS? _ :=
    assert_eqS?
      (AbstractStack.pop_any_n 100)
      (returnS? (Result.Err AbsStackError.Underflow)) in
  letS? _ :=
    assert_eqS?
      (AbstractStack.pop_eq_n 12)
      (returnS? (Result.Err AbsStackError.Underflow)) in
  letS? _ :=
    assert_eqS?
      (AbstractStack.pop_eq_n 112)
      (returnS? (Result.Err AbsStackError.Underflow)) in
  assertS? (AbstractStack.self_is_empty).

Lemma test_empty_stack_correct :
  testS? test_empty_stack AbstractStack.new.
Proof.
  reflexivity.
Qed.
