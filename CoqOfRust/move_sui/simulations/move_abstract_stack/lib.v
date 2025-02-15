Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.simulations.integer.
Require CoqOfRust.alloc.simulations.vec.
Require Import CoqOfRust.core.simulations.option.
Require Import CoqOfRust.core.simulations.eq.
Require Import CoqOfRust.core.simulations.assert.
Require Import CoqOfRust.lib.simulations.lib.
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

  Arguments values {_}.
  Arguments len {_}.

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
      MS! (t A) (list (Z * A)) :=
    liftS! Lens.values readS!.

  Definition self_len {A : Set} :
      MS! (t A) Z :=
    liftS! Lens.len readS!.

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
      MS! (t A) bool :=
    letS! s := readS! in
    returnS! (is_empty s).

  Definition self_is_not_empty {A : Set} :
      MS! (t A) bool :=
    letS! s := readS! in
    returnS! (negb (is_empty s)).

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

  Definition push_n {A : Set} `{Eq.Trait A} (item : A) (n : Z) :
      MS! (t A) (Result.t unit AbsStackError.t) :=
    if n =? 0
    then returnS! (Result.Ok tt)
    else
      letS! self := readS! in
      match U64.checked_add (len self) n with
      | None => returnS! (Result.Err AbsStackError.Overflow)
      | Some new_len =>
        letS! _ := writeS! (self <| len := new_len |>) in
        letS! _ := liftS! Lens.values (
          letS! result := liftS!of? vec.first_mut readS! in
          match result with
          | Some (count, last_item) =>
            if item =? last_item
            then
              liftS!of! (lens!of? vec.first_mut) (
                writeS! (BinOp.Wrap.add IntegerKind.U64 count n, last_item)
              )
            else
              letS! values := readS! in
              writeS! ((n, item) :: values)
          | None =>
            letS! values := readS! in
            writeS! ((n, item) :: values)
          end
        ) in
        returnS! (Result.Ok tt)
      end.

  (*
    /// Pushes a single value on the stack
    pub fn push(&mut self, item: T) -> Result<(), AbsStackError> {
        self.push_n(item, 1)
    }
  *)

  Definition push {A : Set} `{Eq.Trait A} (item : A) :
      MS! (t A) (Result.t unit AbsStackError.t) :=
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

  Definition pop_eq_n {A : Set} (n : Z) : MS! (t A) (Result.t A AbsStackError.t) :=
    fun (self : t A) =>
    if (is_empty self || (n >? len self))%bool then
      return! (Result.Err AbsStackError.Underflow, self)
    else
    let! (count, last) := Option.unwrap (List.hd_error self.(values)) in
    if count <? n then
      return! (Result.Err AbsStackError.ElementNotEqual, self)
    else if count =? n then
      let (_, values) := vec.pop_front self.(values) in
      let self := {|
        values := values;
        len := self.(len) - n
      |} in
      return! (Result.Ok last, self)
    else
      let! values :=
        match values self with
        | [] => panic! "unreachable"
        | (_, last) :: values => return! ((count - n, last) :: values)
        end in
      let self := {|
        values := values;
        len := self.(len) - n
      |} in
      return! (Result.Ok last, self).

  (*
    /// Pops a single value off the stack
    pub fn pop(&mut self) -> Result<T, AbsStackError> {
        self.pop_eq_n(NonZeroU64::new(1).unwrap())
    }
  *)

  Definition pop {A : Set} : MS! (t A) (Result.t A AbsStackError.t) :=
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

  Fixpoint pop_any_n_helper {A : Set} (values : list (Z * A)) (rem : Z) :
      M! (list (Z * A)) :=
    if rem >? 0 then
      match values with
      | [] => panic! "unreachable"
      | (count, last) :: values =>
        if count <=? rem then
        pop_any_n_helper values (rem - count)
        else
          return! ((count - rem, last) :: values)
      end
    else return! values.

  Definition pop_any_n {A : Set} (n : Z) : MS! (t A) (Result.t unit AbsStackError.t) :=
    fun (self : t A) =>
    if (is_empty self || (n >? self.(len)))%bool then
      return! (Result.Err AbsStackError.Underflow, self)
    else
      let! values := pop_any_n_helper self.(values) n in
      let self := {|
        values := values;
        len := self.(len) - n
      |} in
      return! (Result.Ok tt, self).

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
      MS! (t A) unit :=
    fun (self : t A) =>
    let! _ :=
      assert_eq!
        (Z.of_nat $ List.length (values self))
        (Z.of_nat $ List.length lengths) in
    let! sum :=
      fold! 0 (List.combine (values self) lengths) (fun acc '((actual, _), expected) =>
        let! _ := assert_eq! actual expected in
        return! (acc + expected)%Z
      ) in
    let! _ := assert_eq! (len self) sum in
    return! (tt, self).
End AbstractStack.
