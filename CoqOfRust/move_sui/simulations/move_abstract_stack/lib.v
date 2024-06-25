Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.
Import simulations.M.Notations.

(*
  #[derive(Eq, PartialEq, PartialOrd, Ord, Clone, Copy, Debug)]
  pub enum AbsStackError {
      ElementNotEqual,
      Underflow,
      Overflow,
  }
*)

Module AbsStackError.
  Inductive t : Set :=
  | ElementNotEqual
  | Underflow
  | Overflow.
End AbsStackError.

(*
  #[derive(Default, Debug)]
  /// An abstract value that compresses runs of the same value to reduce space usage
  pub struct AbstractStack<T> {
      values: Vec<(u64, T)>,
      len: u64,
  }
*)

Module AbstractStack.
  Record t (A : Set) : Set := {
    values : list (Z * A);
    len : Z;
  }.

  (*
    /// Creates an empty stack
    pub fn new() -> Self {
        Self {
            values: vec![],
            len: 0,
        }
    }
  *)

  Definition new {A : Set} : t A := {|
    values := [];
    len := 0;
  |}.

  (*
    /// Returns true iff the stack is empty
    pub fn is_empty(&self) -> bool {
        // empty ==> len is 0
        debug_assert!(!self.values.is_empty() || self.len == 0);
        // !empty ==> last element len <= len
        debug_assert!(self.values.is_empty() || self.values.last().unwrap().0 <= self.len);
        self.values.is_empty()
    }
  *)

  Definition is_empty {A : Set} (s : t A) : bool :=
    match s with
    | {| values := []; len := _ |} => true
    | _ => false
    end.
End AbstractStack.
