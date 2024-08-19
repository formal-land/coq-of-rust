Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.core.simulations.integers.
Require Import CoqOfRust.core.simulations.vector.
Require Import CoqOfRust.core.simulations.option.
Require Import CoqOfRust.core.simulations.eq.
Require Import CoqOfRust.core.simulations.assert.
Import simulations.M.Notations.
Import simulations.eq.Notations.
Import simulations.assert.Notations.

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

  Scheme Boolean Equality for t.

  Module ImplEq.
    Global Instance I :
      Eq.Trait AbsStackError.t := {
        eqb := t_beq;
      }.
  End ImplEq.
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

    Definition len {A : Set} : Lens.t (t A) Z := {|
      Lens.read stack := len stack;
      Lens.write stack x := stack <| len := x |>
    |}.
  End Lens.

  Definition self_values {A : Set} :
      MS? (t A) string (list (Z * A)) :=
    liftS? Lens.values readS?.

  Definition self_len {A : Set} :
      MS? (t A) string Z :=
    liftS? Lens.len readS?.

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

  Definition self_is_empty {A : Set} :
      MS? (t A) string bool :=
    letS? s := readS? in
    returnS? (is_empty s).

  Definition self_is_not_empty {A : Set} :
      MS? (t A) string bool :=
    letS? s := readS? in
    returnS? (negb (is_empty s)).

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

  Definition push_n {A : Set} (item : A) `{Eq.Trait A} (n : Z) :
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
            if item =? last_item
            then
              liftS?of!? (lens!?of? Vector.first_mut) (
                writeS? ((count + n)%Z, last_item)
              )
            else
              letS? values := readS? in
              writeS? ((n, item) :: values)
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

  Definition push {A : Set} (item : A) `{Eq.Trait A} :
      MS? (t A) string (Result.t unit AbsStackError.t) :=
    push_n item 1.

  (*
    /// Pops n values off the stack, erroring if there are not enough items or if the n items are
    /// not equal
    pub fn pop_eq_n(&mut self, n: NonZeroU64) -> Result<T, AbsStackError> {
        let n: u64 = n.get();
        if self.is_empty() || n > self.len {
            return Err(AbsStackError::Underflow);
        }
        let (count, last) = self.values.last_mut().unwrap();
        debug_assert!( *count > 0 );
        let ret = match ( *count ).cmp(&n) {
            Ordering::Less => return Err(AbsStackError::ElementNotEqual),
            Ordering::Equal => {
                let (_, last) = self.values.pop().unwrap();
                last
            }
            Ordering::Greater => {
                *count -= n;
                last.clone()
            }
        };
        self.len -= n;
        Ok(ret)
    }
  *)

  Definition pop_eq_n {A : Set} (n : Z) :
      MS? (t A) string (Result.t A AbsStackError.t) :=
    letS? self := readS? in
    if (is_empty self || (n >? len self))%bool 
    then returnS? (Result.Err AbsStackError.Underflow)
    else
      letS? '(count, last) := Option.unwrap (
        liftS? Lens.values (liftS?of? Vector.first_mut readS?)
      ) in
      if count <? n
      then returnS? (Result.Err AbsStackError.ElementNotEqual)
      else
        letS? ret := liftS? Lens.values (
          if count =? n
          then
            letS? '(_, last) := Option.unwrap Vector.pop_front in
            returnS? (Result.Ok last)
          else
            letS? _ := liftS?of!? (lens!?of? Vector.first_mut) (writeS? (count - n, last)) in
            returnS? (Result.Ok last)
        ) in
        letS? _ := liftS? Lens.len (writeS? (len self - n)) in
        returnS? ret.

  (*
    /// Pops a single value off the stack
    pub fn pop(&mut self) -> Result<T, AbsStackError> {
        self.pop_eq_n(NonZeroU64::new(1).unwrap())
    }
  *)

  Definition pop {A : Set} :
      MS? (t A) string (Result.t A AbsStackError.t) :=
    pop_eq_n 1.

  (*
    /// Pop any n items off the stack. Unlike `pop_n`, items do not have to be equal
    pub fn pop_any_n(&mut self, n: NonZeroU64) -> Result<(), AbsStackError> {
        let n: u64 = n.get();
        if self.is_empty() || n > self.len {
            return Err(AbsStackError::Underflow);
        }
        let mut rem: u64 = n;
        while rem > 0 {
            let (count, _last) = self.values.last_mut().unwrap();
            debug_assert!( *count > 0 );
            match ( *count ).cmp(&rem) {
                Ordering::Less | Ordering::Equal => {
                    rem -= *count;
                    self.values.pop().unwrap();
                }
                Ordering::Greater => {
                    *count -= rem;
                    break;
                }
            }
        }
        self.len -= n;
        Ok(())
    }
  *)

  Fixpoint pop_any_n_helper {A : Set} (l : nat) (rem : Z) :
      MS? (list (Z * A)) string unit :=
    if rem >? 0
    then
      letS? '(count, last) := Option.unwrap (liftS?of? Vector.first_mut readS?) in
      if count <=? rem 
      then
        match l with
        | O => panicS? "unreachable"
        | S l' => 
          letS? _ := Vector.pop_front in
          pop_any_n_helper l' (rem - count)
        end
      else
        liftS?of!? (lens!?of? Vector.first_mut) (writeS? (count - rem, last))
    else returnS? tt.

  Definition pop_any_n {A : Set} (n : Z) :
      MS? (t A) string (Result.t unit AbsStackError.t) :=
    letS? self := readS? in
    if (is_empty self || (n >? len self))%bool 
    then returnS? (Result.Err AbsStackError.Underflow)
    else
      letS? _ := liftS? Lens.values (
        letS? values := readS? in
        pop_any_n_helper (List.length values) n
      ) in
      letS? _ := liftS? Lens.len (writeS? (len self - n)) in
      returnS? (Result.Ok tt).
  
  (*
    #[cfg(test)]
    pub(crate) fn assert_run_lengths<Items, Item>(&self, lengths: Items)
    where
        Item: std::borrow::Borrow<u64>,
        Items: IntoIterator<Item = Item>,
        <Items as IntoIterator>::IntoIter: ExactSizeIterator,
    {
        let lengths_iter = lengths.into_iter();
        assert_eq!(self.values.len(), lengths_iter.len());
        let mut sum = 0;
        for ((actual, _), expected) in self.values.iter().zip(lengths_iter) {
            let expected = expected.borrow();
            assert_eq!(actual, expected);
            sum += *expected;
        }
        assert_eq!(self.len, sum);
    }
  *)

  Definition assert_run_lengths {A : Set} (lengths : list Z) :
      MS? (t A) string unit :=
    letS? self := readS? in
    letS? _ := assert_eqS? (List.length (values self)) (List.length lengths) in
    letS? sum :=
      foldS? 0 (List.combine (values self) lengths) (fun acc '((actual, _), expected) =>
        letS? _ := assert_eqS? actual expected in
        returnS? (acc + expected)%Z
      ) in
    assert_eqS? (len self) sum.
End AbstractStack.
