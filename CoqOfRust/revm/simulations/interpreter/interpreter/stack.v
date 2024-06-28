Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import CoqOfRust.simulations.M.
Import simulations.M.Notations.
Require Import CoqOfRust.core.links.array.
Require Import CoqOfRust.revm.links.dependencies.
Require Import CoqOfRust.revm.links.interpreter.interpreter.instruction_result.
Require Import CoqOfRust.revm.links.interpreter.interpreter.stack.

Module Stack.
  (*
    /// Returns the length of the stack in words.
    #[inline]
    pub fn len(&self) -> usize {
        self.data.len()
    }
  *)
  Definition len '(Stack.data stack) : Z :=
    Z.of_nat (List.length stack).

  (*
    /// Removes the topmost element from the stack and returns it, or `StackUnderflow` if it is
    /// empty.
    #[inline]
    pub fn pop(&mut self) -> Result<U256, InstructionResult> {
        self.data.pop().ok_or(InstructionResult::StackUnderflow)
    }
  *)
  Definition pop :
      MS? Stack.t string (U256.t + InstructionResult.t) :=
    letS? '(Stack.data stack) := readS? in
    match stack with
    | [] => returnS? (inr InstructionResult.StackUnderflow)
    | x :: xs => 
      letS? _ := writeS? (Stack.data xs) in
      returnS? (inl x)
    end.

  (*
    /// Removes the topmost element from the stack and returns it.
    ///
    /// # Safety
    ///
    /// The caller is responsible for checking the length of the stack.
    #[inline]
    pub unsafe fn pop_unsafe(&mut self) -> U256 {
        self.data.pop().unwrap_unchecked()
    }
  *)
  Definition pop_unsafe :
      MS? Stack.t string U256.t :=
    letS? result := pop in
    match result with
    | inl x => returnS? x
    | inr _ => panicS? "Stack underflow"
    end.

  (*
      /// Peeks the top of the stack.
      ///
      /// # Safety
      ///
      /// The caller is responsible for checking the length of the stack.
      #[inline]
      pub unsafe fn top_unsafe(&mut self) -> &mut U256 {
          let len = self.data.len();
          self.data.get_unchecked_mut(len - 1)
      }
  *)

  Definition top_unsafe : LensPanic.t string Stack.t U256.t := {|
    LensPanic.read '(Stack.data stack) :=
      match stack with
      | [] => panic!? "Stack underflow"
      | x :: _ => return!? x
      end;
    LensPanic.write '(Stack.data stack) x :=
      match stack with
      | [] => panic!? "Stack underflow"
      | _ :: xs => return!? (Stack.data (x :: xs))
      end
  |}.

  (*
      /// Pop the topmost value, returning the value and the new topmost value.
      ///
      /// # Safety
      ///
      /// The caller is responsible for checking the length of the stack.
      #[inline]
      pub unsafe fn pop_top_unsafe(&mut self) -> (U256, &mut U256) {
          let pop = self.pop_unsafe();
          let top = self.top_unsafe();
          (pop, top)
      }
  *)
  Definition pop_top_unsafe :
      MS? Stack.t string (U256.t * LensPanic.t string Stack.t U256.t) :=
    letS? pop := pop_unsafe in
    returnS? (pop, top_unsafe).
  
  (*
    /// Pops 2 values from the stack and returns them, in addition to the new topmost value.
    ///
    /// # Safety
    ///
    /// The caller is responsible for checking the length of the stack.
    #[inline]
    pub unsafe fn pop2_top_unsafe(&mut self) -> (U256, U256, &mut U256) {
        let pop1 = self.pop_unsafe();
        let pop2 = self.pop_unsafe();
        let top = self.top_unsafe();

        (pop1, pop2, top)
    }
  *)
  Definition pop2_top_unsafe :
      MS? Stack.t string (U256.t * U256.t * LensPanic.t string Stack.t U256.t) :=
    letS? pop1 := pop_unsafe in
    letS? pop2 := pop_unsafe in
    returnS? (pop1, pop2, top_unsafe).
End Stack.
