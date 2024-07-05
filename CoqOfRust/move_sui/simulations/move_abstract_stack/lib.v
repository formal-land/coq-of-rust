Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.core.simulations.integers.
Require Import CoqOfRust.core.simulations.vector.
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

  Arguments values {A}%type_scope.
  Arguments len {A}%type_scope.

  Module Lens.
    Definition values {A : Set} : Lens.t (t A) (list (Z * A)) := {|
      Lens.read stack := values stack;
      Lens.write stack vs := stack <| values := vs |>
    |}.
  End Lens.

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

  (*
    /// Push n copies of an item on the stack
    pub fn push_n(&mut self, item: T, n: u64) -> Result<(), AbsStackError> {
        if n == 0 {
            return Ok(());
        }

        let Some(new_len) = self.len.checked_add(n) else {
            return Err(AbsStackError::Overflow);
        };
        self.len = new_len;
        match self.values.last_mut() {
            Some((count, last_item)) if &item == last_item => {
                debug_assert!( *count > 0);
                *count += n
            }
            _ => self.values.push((n, item)),
        }
        Ok(())
    }
  *)

  Definition push_n {A : Set} (item : A) (eq : A -> A -> bool) (n : Z) :
      MS? (t A) string (Result.t unit AbsStackError.t) :=
    if n =? 0
    then returnS? (Result.Ok tt)
    else
      letS? self := readS? in
      match U64.checked_add (len self) n with
      | None => returnS? (Result.Err AbsStackError.Overflow)
      | Some new_len =>
        letS? _ := writeS? (self <| len := new_len |>) in
        letS? _ := liftS? Lens.values (
          letS? result := liftS?of? Vector.first_mut readS? in
          match result with
          | Some (count, last_item) =>
            liftS?of!? (lens!?of? Vector.first_mut) (
              if eq item last_item
              then
                writeS? ((count + n)%Z, last_item)
              else
                returnS? tt
            )
          | None =>
            letS? values := readS? in
            writeS? ((n, item) :: values)
          end
        ) in
        returnS? (Result.Ok tt)
      end.

  (*
    /// Pushes a single value on the stack
    pub fn push(&mut self, item: T) -> Result<(), AbsStackError> {
        self.push_n(item, 1)
    }
  *)

  Definition push {A : Set} (item : A) (eq : A -> A -> bool) :
      MS? (t A) string (Result.t unit AbsStackError.t) :=
    push_n item eq 1.

  (*
    /// Pops a single value off the stack
    pub fn pop(&mut self) -> Result<T, AbsStackError> {
        self.pop_eq_n(NonZeroU64::new(1).unwrap())
    }
  *)
End AbstractStack.
