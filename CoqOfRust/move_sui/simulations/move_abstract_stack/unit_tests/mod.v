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
  letS? _ := assertS?ofS? AbstractStack.self_is_empty in
  letS? _ :=
    assert_eqS?ofS?
      (AbstractStack.pop)
      (returnS? (Result.Err AbsStackError.Underflow)) in
  letS? _ :=
    assert_eqS?ofS?
      (AbstractStack.pop_any_n 1)
      (returnS? (Result.Err AbsStackError.Underflow)) in
  letS? _ :=
    assert_eqS?ofS?
      (AbstractStack.pop_any_n 100)
      (returnS? (Result.Err AbsStackError.Underflow)) in
  letS? _ :=
    assert_eqS?ofS?
      (AbstractStack.pop_eq_n 12)
      (returnS? (Result.Err AbsStackError.Underflow)) in
  letS? _ :=
    assert_eqS?ofS?
      (AbstractStack.pop_eq_n 112)
      (returnS? (Result.Err AbsStackError.Underflow)) in
  assertS?ofS? AbstractStack.self_is_empty.

Lemma test_empty_stack_correct :
  testS? test_empty_stack AbstractStack.new.
Proof.
  reflexivity.
Qed.

(*
  #[test]
  fn test_simple_push_pop() {
      let mut s = AbstractStack::new();
      s.push(1).unwrap();
      assert!(!s.is_empty());
      assert_eq!(s.len(), 1);
      s.assert_run_lengths([1]);
      assert_eq!(s.pop(), Ok(1));
      assert!(s.is_empty());
      assert_eq!(s.len(), 0);

      s.push(1).unwrap();
      s.push(2).unwrap();
      s.push(3).unwrap();
      assert!(!s.is_empty());
      assert_eq!(s.len(), 3);
      s.assert_run_lengths([1, 1, 1]);
      assert_eq!(s.pop(), Ok(3));
      assert_eq!(s.pop(), Ok(2));
      assert_eq!(s.pop(), Ok(1));
      assert!(s.is_empty());
      assert_eq!(s.len(), 0);

      s.push_n(1, 1).unwrap();
      s.push_n(2, 2).unwrap();
      s.push_n(3, 3).unwrap();
      assert!(!s.is_empty());
      assert_eq!(s.len(), 6);
      s.assert_run_lengths([1, 2, 3]);
      assert_eq!(s.pop(), Ok(3));
      assert_eq!(s.pop(), Ok(3));
      assert_eq!(s.pop(), Ok(3));
      assert_eq!(s.pop(), Ok(2));
      assert_eq!(s.pop(), Ok(2));
      assert_eq!(s.pop(), Ok(1));
      assert!(s.is_empty());
      assert_eq!(s.len(), 0);

      s.push_n(1, 1).unwrap();
      s.push_n(2, 2).unwrap();
      s.push_n(3, 3).unwrap();
      assert!(!s.is_empty());
      assert_eq!(s.len(), 6);
      s.assert_run_lengths([1, 2, 3]);
      assert_eq!(s.pop_eq_n(nonzero(3)), Ok(3));
      assert_eq!(s.pop_eq_n(nonzero(2)), Ok(2));
      assert_eq!(s.pop_eq_n(nonzero(1)), Ok(1));
      assert!(s.is_empty());
      assert_eq!(s.len(), 0);

      s.push(1).unwrap();
      s.push(2).unwrap();
      s.push(2).unwrap();
      s.push(3).unwrap();
      s.push(3).unwrap();
      s.push(3).unwrap();
      assert!(!s.is_empty());
      s.assert_run_lengths([1, 2, 3]);
      assert_eq!(s.len(), 6);
      assert_eq!(s.pop_eq_n(nonzero(3)), Ok(3));
      assert_eq!(s.pop_eq_n(nonzero(2)), Ok(2));
      assert_eq!(s.pop_eq_n(nonzero(1)), Ok(1));
      assert!(s.is_empty());
      assert_eq!(s.len(), 0);

      s.push_n(1, 1).unwrap();
      s.push_n(2, 2).unwrap();
      s.push_n(3, 3).unwrap();
      assert!(!s.is_empty());
      s.assert_run_lengths([1, 2, 3]);
      assert_eq!(s.len(), 6);
      s.pop_any_n(nonzero(6)).unwrap();
      assert_eq!(s.len(), 0);
      assert!(s.is_empty());

      s.push(1).unwrap();
      s.push(2).unwrap();
      s.push(2).unwrap();
      s.push(3).unwrap();
      s.push(3).unwrap();
      s.push(3).unwrap();
      assert!(!s.is_empty());
      s.assert_run_lengths([1, 2, 3]);
      assert_eq!(s.len(), 6);
      s.pop_any_n(nonzero(4)).unwrap();
      s.pop_any_n(nonzero(2)).unwrap();
      assert!(s.is_empty());
      assert_eq!(s.len(), 0);
  }
*)

Definition test_simple_push_pop :
    MS? (AbstractStack.t Z) string unit :=

  letS? s := readS? in
  letS? _ := AbstractStack.push 1 in
  letS? _ := assertS?ofS? AbstractStack.self_is_not_empty in
  letS? _ := assert_eqS?ofS? AbstractStack.self_len (returnS? 1) in
  letS? _ := AbstractStack.assert_run_lengths [1] in
  letS? _ := assert_eqS?ofS? AbstractStack.pop (returnS? (Result.Ok 1)) in
  letS? _ := assertS?ofS? (AbstractStack.self_is_empty) in
  letS? _ := assert_eqS?ofS? AbstractStack.self_len (returnS? 0) in

  letS? _ := AbstractStack.push 1 in
  letS? _ := AbstractStack.push 2 in
  letS? _ := AbstractStack.push 3 in
  letS? _ := assertS?ofS? AbstractStack.self_is_not_empty in
  letS? _ := assert_eqS?ofS? AbstractStack.self_len (returnS? 3) in
  letS? _ := AbstractStack.assert_run_lengths [1; 1; 1] in
  letS? _ := assert_eqS?ofS? AbstractStack.pop (returnS? (Result.Ok 3)) in
  letS? _ := assert_eqS?ofS? AbstractStack.pop (returnS? (Result.Ok 2)) in
  letS? _ := assert_eqS?ofS? AbstractStack.pop (returnS? (Result.Ok 1)) in
  letS? _ := assertS?ofS? (AbstractStack.self_is_empty) in
  letS? _ := assert_eqS?ofS? AbstractStack.self_len (returnS? 0) in

  letS? _ := AbstractStack.push_n 1 1 in
  letS? _ := AbstractStack.push_n 2 2 in
  letS? _ := AbstractStack.push_n 3 3 in
  letS? _ := assertS?ofS? AbstractStack.self_is_not_empty in
  letS? _ := assert_eqS?ofS? AbstractStack.self_len (returnS? 6) in
  letS? _ := AbstractStack.assert_run_lengths [3; 2; 1] in
  letS? _ := assert_eqS?ofS? AbstractStack.pop (returnS? (Result.Ok 3)) in
  letS? _ := assert_eqS?ofS? AbstractStack.pop (returnS? (Result.Ok 3)) in
  letS? _ := assert_eqS?ofS? AbstractStack.pop (returnS? (Result.Ok 3)) in
  letS? _ := assert_eqS?ofS? AbstractStack.pop (returnS? (Result.Ok 2)) in
  letS? _ := assert_eqS?ofS? AbstractStack.pop (returnS? (Result.Ok 2)) in
  letS? _ := assert_eqS?ofS? AbstractStack.pop (returnS? (Result.Ok 1)) in
  letS? _ := assertS?ofS? (AbstractStack.self_is_empty) in
  letS? _ := assert_eqS?ofS? AbstractStack.self_len (returnS? 0) in

  letS? _ := AbstractStack.push_n 1 1 in
  letS? _ := AbstractStack.push_n 2 2 in
  letS? _ := AbstractStack.push_n 3 3 in
  letS? _ := assertS?ofS? AbstractStack.self_is_not_empty in
  letS? _ := assert_eqS?ofS? AbstractStack.self_len (returnS? 6) in
  letS? _ := AbstractStack.assert_run_lengths [3; 2; 1] in
  letS? _ := assert_eqS?ofS? (AbstractStack.pop_eq_n 3) (returnS? (Result.Ok 3)) in
  letS? _ := assert_eqS?ofS? (AbstractStack.pop_eq_n 2) (returnS? (Result.Ok 2)) in
  letS? _ := assert_eqS?ofS? (AbstractStack.pop_eq_n 1) (returnS? (Result.Ok 1)) in
  letS? _ := assertS?ofS? (AbstractStack.self_is_empty) in
  letS? _ := assert_eqS?ofS? AbstractStack.self_len (returnS? 0) in

  letS? _ := AbstractStack.push 1 in
  letS? _ := AbstractStack.push 2 in
  letS? _ := AbstractStack.push 2 in
  letS? _ := AbstractStack.push 3 in
  letS? _ := AbstractStack.push 3 in
  letS? _ := AbstractStack.push 3 in
  letS? _ := assertS?ofS? AbstractStack.self_is_not_empty in
  letS? _ := AbstractStack.assert_run_lengths [3; 2; 1] in
  letS? _ := assert_eqS?ofS? AbstractStack.self_len (returnS? 6) in
  letS? _ := assert_eqS?ofS? (AbstractStack.pop_eq_n 3) (returnS? (Result.Ok 3)) in
  letS? _ := assert_eqS?ofS? (AbstractStack.pop_eq_n 2) (returnS? (Result.Ok 2)) in
  letS? _ := assert_eqS?ofS? (AbstractStack.pop_eq_n 1) (returnS? (Result.Ok 1)) in
  letS? _ := assertS?ofS? (AbstractStack.self_is_empty) in
  letS? _ := assert_eqS?ofS? AbstractStack.self_len (returnS? 0) in

  letS? _ := AbstractStack.push_n 1 1 in
  letS? _ := AbstractStack.push_n 2 2 in
  letS? _ := AbstractStack.push_n 3 3 in
  letS? _ := assertS?ofS? AbstractStack.self_is_not_empty in
  letS? _ := AbstractStack.assert_run_lengths [3; 2; 1] in
  letS? _ := assert_eqS?ofS? AbstractStack.self_len (returnS? 6) in
  letS? _ := AbstractStack.pop_any_n 6 in
  letS? _ := assert_eqS?ofS? AbstractStack.self_len (returnS? 0) in
  letS? _ := assertS?ofS? (AbstractStack.self_is_empty) in

  letS? _ := AbstractStack.push 1 in
  letS? _ := AbstractStack.push 2 in
  letS? _ := AbstractStack.push 2 in
  letS? _ := AbstractStack.push 3 in
  letS? _ := AbstractStack.push 3 in
  letS? _ := AbstractStack.push 3 in
  letS? _ := assertS?ofS? AbstractStack.self_is_not_empty in
  letS? _ := AbstractStack.assert_run_lengths [3; 2; 1] in
  letS? _ := assert_eqS?ofS? AbstractStack.self_len (returnS? 6) in
  letS? _ := AbstractStack.pop_any_n 4 in
  letS? _ := AbstractStack.pop_any_n 2 in
  letS? _ := assertS?ofS? (AbstractStack.self_is_empty) in
  letS? _ := assert_eqS?ofS? AbstractStack.self_len (returnS? 0) in

  returnS? tt.

Lemma test_simple_push_pop_correct :
  testS? test_simple_push_pop AbstractStack.new.
Proof.
  reflexivity.
Qed.

(*
  #[test]
  fn test_not_eq() {
      let mut s = AbstractStack::new();
      s.push(1).unwrap();
      s.push(2).unwrap();
      s.push(2).unwrap();
      s.push(3).unwrap();
      s.push(3).unwrap();
      s.push(3).unwrap();
      assert_eq!(s.len(), 6);
      s.assert_run_lengths([1, 2, 3]);
      assert_eq!(s.pop_eq_n(nonzero(4)), Err(AbsStackError::ElementNotEqual));
      assert_eq!(s.pop_eq_n(nonzero(5)), Err(AbsStackError::ElementNotEqual));
      assert_eq!(s.len(), 6);
      s.assert_run_lengths([1, 2, 3]);
  }
*)

Definition test_not_eq :
    MS? (AbstractStack.t Z) string unit :=
  letS? s := readS? in
  letS? _ := AbstractStack.push 1 in
  letS? _ := AbstractStack.push 2 in
  letS? _ := AbstractStack.push 2 in
  letS? _ := AbstractStack.push 3 in
  letS? _ := AbstractStack.push 3 in
  letS? _ := AbstractStack.push 3 in
  letS? _ := assert_eqS?ofS? AbstractStack.self_len (returnS? 6) in
  letS? _ := AbstractStack.assert_run_lengths [3; 2; 1] in
  letS? _ :=
    assert_eqS?ofS?
      (AbstractStack.pop_eq_n 4)
      (returnS? (Result.Err AbsStackError.ElementNotEqual)) in
  letS? _ :=
    assert_eqS?ofS?
      (AbstractStack.pop_eq_n 4)
      (returnS? (Result.Err AbsStackError.ElementNotEqual)) in
  letS? _ := assert_eqS?ofS? (AbstractStack.self_len) (returnS? 6) in
  AbstractStack.assert_run_lengths [3; 2; 1].

Lemma test_not_eq_correct :
  testS? test_not_eq AbstractStack.new.
Proof.
  reflexivity.
Qed.

(*
  #[test]
  fn test_not_enough_values() {
      let mut s = AbstractStack::new();
      s.push(1).unwrap();
      s.push(2).unwrap();
      s.push(2).unwrap();
      s.push(3).unwrap();
      s.push(3).unwrap();
      s.push(3).unwrap();
      assert_eq!(s.len(), 6);
      s.assert_run_lengths([1, 2, 3]);
      assert_eq!(s.pop_eq_n(nonzero(7)), Err(AbsStackError::Underflow));
      assert_eq!(s.pop_any_n(nonzero(7)), Err(AbsStackError::Underflow));
      assert_eq!(s.len(), 6);
      s.assert_run_lengths([1, 2, 3]);
  }
*)

Definition test_not_enough_values :
    MS? (AbstractStack.t Z) string unit :=
  letS? s := readS? in
  letS? _ := AbstractStack.push 1 in
  letS? _ := AbstractStack.push 2 in
  letS? _ := AbstractStack.push 2 in
  letS? _ := AbstractStack.push 3 in
  letS? _ := AbstractStack.push 3 in
  letS? _ := AbstractStack.push 3 in
  letS? _ := assert_eqS?ofS? AbstractStack.self_len (returnS? 6) in
  letS? _ := AbstractStack.assert_run_lengths [3; 2; 1] in
  letS? _ :=
    assert_eqS?ofS?
      (AbstractStack.pop_eq_n 7)
      (returnS? (Result.Err AbsStackError.Underflow)) in
  letS? _ :=
    assert_eqS?ofS?
      (AbstractStack.pop_any_n 7)
      (returnS? (Result.Err AbsStackError.Underflow)) in
  letS? _ := assert_eqS?ofS? (AbstractStack.self_len) (returnS? 6) in
  AbstractStack.assert_run_lengths [3; 2; 1].

Lemma test_not_enough_values_correct :
  testS? test_not_enough_values AbstractStack.new.
Proof.
  reflexivity.
Qed.
