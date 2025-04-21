Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import alloc.links.alloc.
Require Import alloc.vec.links.mod.
Require Import alloy_primitives.links.aliases.
Require Import core.fmt.links.mod.
Require Import core.fmt.links.rt.
Require Import core.iter.traits.links.collect.
Require Import core.links.array.
Require Import core.links.hint.
Require Import core.links.option.
Require Import core.links.panicking.
Require Import core.links.result.
Require Import core.slice.links.index.
Require Import core.slice.links.iter.
Require Import core.slice.links.mod.
Require Import revm.revm_interpreter.interpreter.stack.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import ruint.links.lib.

(*
  pub struct Stack {
      data: Vec<U256>,
  }
*)
Module Stack.
  Record t : Set := {
    data : Vec.t aliases.U256.t Global.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter::stack::Stack";
    φ '{| data := data |} :=
      Value.StructRecord "revm_interpreter::interpreter::stack::Stack" [("data", φ data)];
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_interpreter::interpreter::stack::Stack").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.

  Lemma of_value_with
      (data : Vec.t aliases.U256.t Global.t) data' :
    data' = φ data ->
    Value.StructRecord "revm_interpreter::interpreter::stack::Stack" [
      ("data", data')
    ] = φ (Build_t data).
  Proof. now intros; subst. Qed.
  Smpl Add apply of_value_with : of_value.

  Definition of_value (data : Vec.t aliases.U256.t Global.t) data' :
    data' = φ data ->
    OfValue.t (Value.StructRecord "revm_interpreter::interpreter::stack::Stack" [
      ("data", data')
    ]).
  Proof. econstructor; apply of_value_with; eassumption. Defined.
  Smpl Add apply of_value : of_value.

  Module SubPointer.
    Definition get_data : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_interpreter::interpreter::stack::Stack" "data") :=
    {|
      SubPointer.Runner.projection x := Some x.(data);
      SubPointer.Runner.injection x y := Some (x <| data := y |>);
    |}.

    Lemma get_data_is_valid :
      SubPointer.Runner.Valid.t get_data.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_data_is_valid : run_sub_pointer.
  End SubPointer.
End Stack.

Instance run_STACK_LIMIT :
  Run.Trait
    interpreter.stack.value_STACK_LIMIT [] [] []
    (Ref.t Pointer.Kind.Raw Usize.t).
Proof.
  constructor.
  run_symbolic.
Defined.

Module Impl_Stack.
  Definition Self : Set :=
    Stack.t.

  (* pub fn new() -> Self *)
  Instance run_self :
    Run.Trait interpreter.stack.Impl_revm_interpreter_interpreter_stack_Stack.new [] [] [] Self.
  Proof.
    constructor.
    run_symbolic.
  Defined.

  (* pub fn len(&self) -> usize *)
  Instance run_len (self : Ref.t Pointer.Kind.Ref Self) :
    Run.Trait
      interpreter.stack.Impl_revm_interpreter_interpreter_stack_Stack.len [] [] [φ self]
      Usize.t.
  Proof.
    constructor.
    run_symbolic.
  Defined.

  (* pub fn is_empty(&self) -> bool *)
  Instance run_is_empty (self : Ref.t Pointer.Kind.Ref Self) :
    Run.Trait
      interpreter.stack.Impl_revm_interpreter_interpreter_stack_Stack.is_empty [] [] [φ self]
      bool.
  Proof.
    constructor.
    run_symbolic.
  Defined.

  (* pub fn data(&self) -> &Vec<U256> *)
  Instance run_data (self : Ref.t Pointer.Kind.Ref Self) :
    Run.Trait
      interpreter.stack.Impl_revm_interpreter_interpreter_stack_Stack.data [] [] [φ self]
      (Ref.t Pointer.Kind.Ref (Vec.t aliases.U256.t Global.t)).
  Proof.
    constructor.
    run_symbolic.
  Defined.

  (* pub fn data_mut(&mut self) -> &mut Vec<U256> *)
  Instance run_data_mut (self : Ref.t Pointer.Kind.MutRef Self) :
    Run.Trait
      interpreter.stack.Impl_revm_interpreter_interpreter_stack_Stack.data_mut [] [] [φ self]
      (Ref.t Pointer.Kind.MutRef (Vec.t aliases.U256.t Global.t)).
  Proof.
    constructor.
    run_symbolic.
  Defined.

  (* pub fn into_data(self) -> Vec<U256> *)
  Instance run_into_data (self : Self) :
    Run.Trait
      interpreter.stack.Impl_revm_interpreter_interpreter_stack_Stack.into_data [] [] [φ self]
      (Vec.t aliases.U256.t Global.t).
  Proof.
    constructor.
    run_symbolic.
  Defined.

  (* pub fn pop(&mut self) -> Result<U256, InstructionResult> *)
  Instance run_pop (self : Ref.t Pointer.Kind.MutRef Self) :
    Run.Trait
      interpreter.stack.Impl_revm_interpreter_interpreter_stack_Stack.pop [] [] [φ self]
      (Result.t aliases.U256.t InstructionResult.t).
  Proof.
    constructor.
    run_symbolic.
  Defined.

  (* pub unsafe fn pop_unsafe(&mut self) -> U256 *)
  Instance run_pop_unsafe (self : Ref.t Pointer.Kind.MutRef Self) :
    Run.Trait
      interpreter.stack.Impl_revm_interpreter_interpreter_stack_Stack.pop_unsafe [] [] [φ self]
      aliases.U256.t.
  Proof.
    constructor.
    run_symbolic.
  Defined.

  (* pub unsafe fn top_unsafe(&mut self) -> &mut U256 *)
  Instance run_top_unsafe (self : Ref.t Pointer.Kind.MutRef Self) :
    Run.Trait
      interpreter.stack.Impl_revm_interpreter_interpreter_stack_Stack.top_unsafe [] [] [φ self]
      (Ref.t Pointer.Kind.MutRef aliases.U256.t).
  Proof.
    constructor.
    destruct (Impl_DerefMut_for_Vec.run (T := aliases.U256.t) (A := Global.t)).
    run_symbolic.
  Defined.

  (* pub unsafe fn popn<const N: usize>(&mut self) -> [U256; N] *)
  Instance run_popn (N : Usize.t) (self : Ref.t Pointer.Kind.MutRef Self) :
    Run.Trait
      interpreter.stack.Impl_revm_interpreter_interpreter_stack_Stack.popn [φ N] [] [φ self]
      (array.t aliases.U256.t N).
  Proof.
    constructor.
    destruct (Impl_IntoIterator_for_Iterator_I.run (IterMut.t aliases.U256.t) aliases.U256.t).
    run_symbolic.
  Admitted.

  (* pub unsafe fn popn_top<const POPN: usize>(&mut self) -> ([U256; POPN], &mut U256) *)
  Instance run_popn_top (self : Ref.t Pointer.Kind.MutRef Self) (POPN : Usize.t) :
    Run.Trait
      interpreter.stack.Impl_revm_interpreter_interpreter_stack_Stack.popn_top [φ POPN] [] [φ self]
      (array.t aliases.U256.t POPN * Ref.t Pointer.Kind.MutRef aliases.U256.t).
  Proof.
    constructor.
    run_symbolic.
  Defined.

  (* pub fn push(&mut self, value: U256) -> bool *)
  Instance run_push (self : Ref.t Pointer.Kind.MutRef Self) (value : aliases.U256.t) :
    Run.Trait
      interpreter.stack.Impl_revm_interpreter_interpreter_stack_Stack.push [] [] [φ self; φ value]
      bool.
  Proof.
    constructor.
    run_symbolic.
  Defined.

  (* pub fn peek(&self, no_from_top: usize) -> Result<U256, InstructionResult> *)
  Instance run_peek (self : Ref.t Pointer.Kind.Ref Self) (no_from_top : Usize.t) :
    Run.Trait
      interpreter.stack.Impl_revm_interpreter_interpreter_stack_Stack.peek
        [] [] [φ self; φ no_from_top]
      (Result.t aliases.U256.t InstructionResult.t).
  Proof.
    constructor.
    destruct (Impl_Index_for_Vec_T_A.run aliases.U256.t Usize.t Global.t aliases.U256.t).
    run_symbolic.
  Admitted.

  (* pub fn dup(&mut self, n: usize) -> bool *)
  Instance run_dup (self : Ref.t Pointer.Kind.MutRef Self) (n : Usize.t) :
    Run.Trait
      interpreter.stack.Impl_revm_interpreter_interpreter_stack_Stack.dup [] [] [φ self; φ n]
      bool.
  Proof.
    constructor.
    run_symbolic.
  Admitted.

  (* pub fn exchange(&mut self, n: usize, m: usize) -> bool *)
  Instance run_exchange (self : Ref.t Pointer.Kind.MutRef Self) (n m : Usize.t) :
    Run.Trait
      interpreter.stack.Impl_revm_interpreter_interpreter_stack_Stack.exchange
        [] [] [φ self; φ n; φ m]
      bool.
  Proof.
    constructor.
    run_symbolic.
  Admitted.

  (* pub fn swap(&mut self, n: usize) -> bool *)
  Instance run_swap (self : Ref.t Pointer.Kind.MutRef Self) (n : Usize.t) :
    Run.Trait
      interpreter.stack.Impl_revm_interpreter_interpreter_stack_Stack.swap [] [] [φ self; φ n]
      bool.
  Proof.
    constructor.
    run_symbolic.
  Defined.

  (* pub fn push_slice(&mut self, slice: &[u8]) -> Result<(), InstructionResult> *)
  Instance run_push_slice
      (self : Ref.t Pointer.Kind.MutRef Self)
      (slice : Ref.t Pointer.Kind.Ref (list U8.t)) :
    Run.Trait
      interpreter.stack.Impl_revm_interpreter_interpreter_stack_Stack.push_slice
        [] [] [φ self; φ slice]
      (Result.t unit InstructionResult.t).
  Proof.
    constructor.
  Admitted.

  (* pub fn set(&mut self, no_from_top: usize, val: U256) -> Result<(), InstructionResult> *)
  Instance run_set
      (self : Ref.t Pointer.Kind.MutRef Self)
      (no_from_top : Usize.t)
      (val : aliases.U256.t) :
    Run.Trait
      interpreter.stack.Impl_revm_interpreter_interpreter_stack_Stack.set
        [] [] [φ self; φ no_from_top; φ val]
      (Result.t unit InstructionResult.t).
  Proof.
    constructor.
    run_symbolic.
  Admitted.
End Impl_Stack.
