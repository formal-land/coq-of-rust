Require Import CoqOfRust.CoqOfRust.
Require Import links.M.

Module Stack.
  Definition t : Type :=
    list Set.

  Fixpoint to_Set_aux (A : Set) (Stack : t) : Set :=
    match Stack with
    | [] => A
    | B :: Stack => A * to_Set_aux B Stack
    end.

  Definition to_Set (Stack : t) : Set :=
    match Stack with
    | [] => unit
    | A :: Stack => to_Set_aux A Stack
    end.

  Definition nth (Stack : t) (index : nat) : Set :=
    List.nth index Stack unit.

  Fixpoint read_aux {A : Set} {Stack : t}
    (stack : to_Set_aux A Stack)
    (index : nat)
    {struct Stack} :
    nth (A :: Stack) index.
  Proof.
    destruct Stack as [|B Stack], index as [|index]; cbn in *.
    { exact stack. }
    { destruct index; exact tt. }
    { exact (fst stack). }
    { exact (read_aux _ _ (snd stack) index). }
  Defined.

  Definition read {Stack : t} (stack : to_Set Stack) (index : nat) : nth Stack index.
  Proof.
    destruct Stack; cbn in *.
    { destruct index; exact tt. }
    { apply (read_aux stack). }
  Defined.

  Fixpoint write_aux {A : Set} {Stack : t}
    (stack : to_Set_aux A Stack)
    (index : nat)
    (value : nth (A :: Stack) index)
    {struct Stack} :
    to_Set_aux A Stack.
  Proof.
    destruct Stack as [|B Stack], index as [|index]; cbn in *.
    { exact value. }
    { exact stack. }
    { exact (value, snd stack). }
    { exact (fst stack, write_aux _ _ (snd stack) index value). }
  Defined.

  Definition write {Stack : t}
    (stack : to_Set Stack)
    (index : nat)
    (value : nth Stack index) :
    to_Set Stack.
  Proof.
    destruct Stack; cbn in *.
    { exact tt. }
    { apply (write_aux stack index value). }
  Defined.

  Fixpoint alloc_aux {A : Set} {Stack : t} {B : Set}
    (stack : to_Set_aux A Stack)
    (value : B)
    {struct Stack} :
    to_Set_aux A (Stack ++ [B]).
  Proof.
    destruct Stack as [|A' Stack]; cbn in *.
    { exact (stack, value). }
    { exact (fst stack, alloc_aux _ _ _ (snd stack) value). }
  Defined.

  Definition alloc {Stack : t} {A : Set} (stack : to_Set Stack) (value : A) :
    to_Set (Stack ++ [A]).
  Proof.
    destruct Stack; cbn in *.
    { exact value. }
    { apply (alloc_aux stack value). }
  Defined.

  Fixpoint dealloc_aux {A : Set} {Stack : t} {B : Set}
    (stack : to_Set_aux A (Stack ++ [B]))
    {struct Stack} :
    to_Set_aux A Stack * B.
  Proof.
    destruct Stack as [|A' Stack]; cbn in *.
    { exact stack. }
    { exact (
        let '(stack', value) := dealloc_aux _ _ _ (snd stack) in
        ((fst stack, stack'), value)
      ).
    }
  Defined.

  Definition dealloc {Stack : t} {A : Set} (stack : to_Set (Stack ++ [A])) : to_Set Stack * A.
  Proof.
    destruct Stack; cbn in *.
    { exact (tt, stack). }
    { exact (dealloc_aux stack). }
  Defined.

  Module CanAccess.
    Inductive t {A : Set} `{Link A} (Stack : Stack.t) : Ref.Core.t A -> Set :=
    | Mutable
        (index : nat)
        (path : Pointer.Path.t)
        (big_to_value : nth Stack index -> Value.t)
        (projection : nth Stack index -> option A)
        (injection : nth Stack index -> A -> option (nth Stack index)) :
      t Stack (Ref.Core.Mutable (Address := nat) (Big_A := nth Stack index)
        index path big_to_value projection injection
      ).

    Definition runner {Stack : Stack.t} {A : Set} `{Link A} {index : Pointer.Index.t}
        {ref_core : Ref.Core.t A}
        (runner : SubPointer.Runner.t A index)
        (H_ref_core : t Stack ref_core) :
      t Stack (SubPointer.Runner.apply ref_core runner).
    Proof.
      destruct H_ref_core.
      apply Mutable.
    Defined.

    Definition read {A : Set} `{Link A} {Stack : Stack.t}
        {ref_core : Ref.Core.t A}
        (run : t Stack ref_core)
        (stack : to_Set Stack) :
        option A :=
      match run with
      | Mutable _ index _ _ projection _ => projection (read stack index)
      end.

    Definition write {A : Set} `{Link A} {Stack : Stack.t}
        {ref_core : Ref.Core.t A}
        (run : t Stack ref_core)
        (stack : to_Set Stack)
        (value : A) :
        option (to_Set Stack) :=
      match run with
      | Mutable _ index _ _ _ injection =>
        match injection (Stack.read stack index) value with
        | Some value => Some (Stack.write stack index value)
        | None => None
        end
      end.
  End CanAccess.
End Stack.

(** Here we define an execution mode where we keep dynamic cast to retrieve data from the stack. In
    practice, these casts should always be correct as the original Rust code was well typed. *)
Module StackM.
  Inductive t (A : Set) : Set :=
  | Pure (value : A)
  | GetCanAccess {B : Set} `{Link B}
      (Stack : Stack.t)
      (ref_core : Ref.Core.t B)
      (k : Stack.CanAccess.t Stack ref_core -> t A)
  | Call {B : Set} `{Link B} {Stack : Stack.t}
      {f : list Value.t -> M} {args : list Value.t}
      (stack_in : Stack.to_Set Stack)
      (run_f : {{ f args 🔽 B }})
      (k : Output.t B B * Stack.to_Set Stack -> t A).
  Arguments Pure {_}.
  Arguments GetCanAccess {_ _ _}.
  Arguments Call {_ _ _ _ _ _}.

  Fixpoint let_ {A B : Set} (e1 : t A) (e2 : A -> t B) : t B :=
    match e1 with
    | Pure value => e2 value
    | GetCanAccess Stack ref_core k =>
      GetCanAccess Stack ref_core (fun can_access => let_ (k can_access) e2)
    | Call stack_in run_f k => Call stack_in run_f (fun output_stack => let_ (k output_stack) e2)
    end.

  Parameter TodoLoop : forall {A : Set}, t A.

  Fixpoint eval {R Output : Set} {Stack : Stack.t}
      (e : LowM.t R Output)
      (stack : Stack.to_Set Stack)
      {struct e} :
    t (Output.t R Output * Stack.to_Set Stack).
  Proof.
    destruct e.
    { (* Pure *)
      exact (Pure (value, stack)).
    }
    { (* CallPrimitive *)
      destruct primitive.
      { (* StateAlloc *)
        exact (
          let ref_core :=
            Ref.Core.Mutable
              (List.length Stack)
              []
              φ
              Some
              (fun _ => Some) in
          let stack := Stack.alloc stack value in
          let_ (eval _ _ _ (k ref_core) stack) (fun '(output, stack) =>
          let '(stack, _) := Stack.dealloc stack in
          Pure (output, stack)
          )
        ).
      }
      { (* StateRead *)
        refine (
          GetCanAccess Stack ref_core (fun H_access =>
          _)
        ).
        destruct (Stack.CanAccess.read H_access stack) as [value|].
        { exact (eval _ _ _ (k value) stack). }
        { exact (Pure (Output.Exception Output.Exception.BreakMatch, stack)). }
      }
      { (* StateWrite *)
        refine (
          GetCanAccess Stack ref_core (fun H_access =>
          _)
        ).
        destruct (Stack.CanAccess.write H_access stack value) as [stack'|].
        { exact (eval _ _ _ (k tt) stack'). }
        { exact (Pure (Output.panic "StateWrite: invalid reference", stack)). }
      }
      { (* GetSubPointer *)
        exact (eval _ _ _ (k (SubPointer.Runner.apply ref_core runner)) stack).
      }
    }
    { (* Let *)
      exact (
        let_ (eval _ _ _ e stack) (fun '(output, stack) =>
        eval _ _ _ (k output) stack)
      ).
    }
    { (* LetAlloc *)
      exact (
        let_ (eval _ _ _ e stack) (fun '(output, stack) =>
        match output with
        | Output.Success value =>
          let ref_core :=
            Ref.Core.Mutable
              (List.length Stack)
              []
              φ
              Some
              (fun _ => Some) in
          let ref := {| Ref.core := ref_core |} in
          let stack := Stack.alloc stack value in
          let_ (eval _ _ _ (k (Output.Success ref)) stack) (fun '(output, stack) =>
          let '(stack, _) := Stack.dealloc stack in
          Pure (output, stack))
        | Output.Exception exception => eval _ _ _ (k (Output.Exception exception)) stack
        end)
      ).
    }
    { (* Call *)
      exact (
        Call stack run_f0 (fun '(output, stack) =>
        eval _ _ _ (k (SuccessOrPanic.of_output output)) stack)
      ).
    }
    { (* Loop *)
      exact TodoLoop.
    }
  Defined.

  Definition eval_f
      {f : PolymorphicFunction.t}
      {ε : list Value.t}
      {τ : list Ty.t}
      {α : list Value.t}
      {Output : Set} `{Link Output}
      {Stack : Stack.t}
      (run : Run.Trait f ε τ α Output) :
      Stack.to_Set Stack ->
      t (Output.t Output Output * Stack.to_Set Stack) :=
    eval (links.M.evaluate run.(Run.run_f)).
End StackM.

Module Run.
  Reserved Notation "{{ e 🌲 value }}".

  Inductive t {A : Set} (value : A) : StackM.t A -> Prop :=
  | Pure :
    {{ StackM.Pure value 🌲 value }}
  | GetCanAccess {B : Set} `{Link B}
      (Stack : Stack.t)
      (ref_core : Ref.Core.t B)
      (k : Stack.CanAccess.t Stack ref_core -> StackM.t A)
      (H_access : Stack.CanAccess.t Stack ref_core)
    (H_k : {{ k H_access 🌲 value }}) :
    {{ StackM.GetCanAccess Stack ref_core k 🌲 value }}
  | Call {B : Set} `{Link B} {Stack : Stack.t}
      {f : list Value.t -> M} {args : list Value.t}
      (stack_in : Stack.to_Set Stack)
      (run_f : {{ f args 🔽 B }})
      (value_inter : Output.t B B * Stack.to_Set Stack)
      (k : Output.t B B * Stack.to_Set Stack -> StackM.t A)
    (H_f : {{ StackM.eval (links.M.evaluate run_f) stack_in 🌲 value_inter }})
    (H_k : {{ k value_inter 🌲 value }}) :
    {{ StackM.Call stack_in run_f k 🌲 value }}

  where "{{ e 🌲 value }}" := (t value e).
End Run.
Export Run.

Ltac get_can_access :=
  unshelve eapply Run.GetCanAccess; [
    match goal with
    | |- Stack.CanAccess.t ?Stack (Ref.Core.Mutable ?index _ _ _ ?injection) =>
      apply (Stack.CanAccess.Mutable Stack index _ _ _ injection)
    end
  |];
  cbn.
