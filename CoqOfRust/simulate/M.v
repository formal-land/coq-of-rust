Require Import CoqOfRust.CoqOfRust.
Require Import links.M.

Module Stack.
  Definition t : Type :=
    list Set.

  Fixpoint to_Set (Stack : t) : Set :=
    match Stack with
    | [] => unit
    | A :: Stack => A * to_Set Stack
    end.

  Definition nth (Stack : t) (index : nat) : Set :=
    List.nth index Stack unit.

  Fixpoint read {Stack : t}
    (stack : to_Set Stack)
    (index : nat)
    {struct Stack} :
    nth Stack index.
  Proof.
    destruct Stack as [|A Stack], index as [|index]; cbn in *.
    { exact tt. }
    { exact tt. }
    { exact (fst stack). }
    { exact (read _ (snd stack) index). }
  Defined.

  Fixpoint write {Stack : t}
    (stack : to_Set Stack)
    (index : nat)
    (value : nth Stack index)
    {struct Stack} :
    to_Set Stack.
  Proof.
    destruct Stack as [|A Stack], index as [|index]; cbn in *.
    { exact tt. }
    { exact tt. }
    { exact (value, snd stack). }
    { exact (fst stack, write _ (snd stack) index value). }
  Defined.

  Fixpoint alloc {Stack : t} {A : Set}
    (stack : to_Set Stack)
    (value : A)
    {struct Stack} :
    to_Set (Stack ++ [A]).
  Proof.
    destruct Stack as [|A' Stack]; cbn in *.
    { exact (value, tt). }
    { exact (fst stack, alloc _ _ (snd stack) value). }
  Defined.

  Fixpoint dealloc {Stack : t} {A : Set}
    (stack : to_Set (Stack ++ [A]))
    {struct Stack} :
    to_Set Stack * A.
  Proof.
    destruct Stack as [|A' Stack]; cbn in *.
    { exact (tt, fst stack). }
    { exact (
        let '(stack', value) := dealloc _ _ (snd stack) in
        ((fst stack, stack'), value)
      ).
    }
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
Module SimulateM.
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
      (e : LinkM.t R Output)
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
        (* We always allocate an immediate value *)
        exact (eval _ _ _ (k (Ref.Core.Immediate (Some value))) stack).
      }
      { (* StateRead *)
        refine (
          let immediate_value :=
            match ref_core with
            | Ref.Core.Immediate immediate_value => Some immediate_value
            | _ => None
            end in
          _
        ).
        destruct immediate_value as [value|].
        { (* Immediate *)
          destruct value as [value|].
          { exact (eval _ _ _ (k value) stack). }
          { exact (Pure (Output.Exception Output.Exception.BreakMatch, stack)). }
        }
        { (* Mutable *)
          refine (
            GetCanAccess Stack ref_core (fun H_access =>
            _)
          ).
          destruct (Stack.CanAccess.read H_access stack) as [value|].
          { exact (eval _ _ _ (k value) stack). }
          { exact (Pure (Output.Exception Output.Exception.BreakMatch, stack)). }
        }
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
      exact (Call stack run_f0 (fun '(output, stack) =>
        SuccessOrPanic.apply (fun output =>
          eval _ _ _ (k output) stack
        ) output
      )).
    }
    { (* Loop *)
      exact TodoLoop.
    }
    { (* IfThenElse *)
      exact (
        if cond then
          eval _ _ _ e1 stack
        else
          eval _ _ _ e2 stack
      ).
    }
    { (* MatchOutput *)
      exact (
        match output with
        | Output.Success success => eval _ _ _ (k_success success) stack
        | Output.Exception exception =>
          match exception with
          | Output.Exception.Return return_ => eval _ _ _ (k_return return_) stack
          | Output.Exception.Break => eval _ _ _ (k_break tt) stack
          | Output.Exception.Continue => eval _ _ _ (k_continue tt) stack
          | Output.Exception.BreakMatch => eval _ _ _ (k_break_match tt) stack
          | Output.Exception.Panic panic => eval _ _ _ (k_panic panic) stack
          end
        end
      ).
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
End SimulateM.

Module Run.
  Reserved Notation "{{ e 🌲 value }}".

  Inductive t {A : Set} (value : A) : SimulateM.t A -> Prop :=
  | Pure :
    {{ SimulateM.Pure value 🌲 value }}
  | GetCanAccess {B : Set} `{Link B}
      (Stack : Stack.t)
      (ref_core : Ref.Core.t B)
      (k : Stack.CanAccess.t Stack ref_core -> SimulateM.t A)
      (H_access : Stack.CanAccess.t Stack ref_core)
    (H_k : {{ k H_access 🌲 value }}) :
    {{ SimulateM.GetCanAccess Stack ref_core k 🌲 value }}
  | Call {B : Set} `{Link B} {Stack : Stack.t}
      {f : list Value.t -> M} {args : list Value.t}
      (stack_in : Stack.to_Set Stack)
      (run_f : {{ f args 🔽 B }})
      (value_inter : Output.t B B * Stack.to_Set Stack)
      (k : Output.t B B * Stack.to_Set Stack -> SimulateM.t A)
    (H_f : {{ SimulateM.eval (links.M.evaluate run_f) stack_in 🌲 value_inter }})
    (H_k : {{ k value_inter 🌲 value }}) :
    {{ SimulateM.Call stack_in run_f k 🌲 value }}

  where "{{ e 🌲 value }}" := (t value e).
End Run.
Export Run.

Ltac get_can_access :=
  unshelve eapply Run.GetCanAccess; [
    cbn;
    match goal with
    | |- Stack.CanAccess.t ?Stack (Ref.Core.Mutable ?index _ _ _ ?injection) =>
      apply (Stack.CanAccess.Mutable Stack index _ _ _ injection)
    end
  |];
  cbn.

Definition make_ref {A : Set} `{Link A} {kind : Pointer.Kind.t} (index : nat) : Ref.t kind A :=
  {| Ref.core := Ref.Core.Mutable (A := A) index [] φ Some (fun _ => Some) |}.

(** To get a reference to a sub-field from a reference to a larger object. *)
Module RefStub.
  Record t {A Sub_A : Set} `{Link A} `{Link Sub_A} : Set := {
    path : Pointer.Path.t;
    (* We suppose the pointer is valid (no [option] type for the [projection] and [injection]
       functions) *)
    projection : A -> Sub_A;
    injection : A -> Sub_A -> A;
  }.
  Arguments t _ _ {_ _}.

  Definition apply_core {A Sub_A : Set} `{Link A} `{Link Sub_A}
      (ref_core : Ref.Core.t A)
      (stub : t A Sub_A) :
      Ref.Core.t Sub_A.
  Proof.
    destruct ref_core as [| ? ? address path big_to_value projection injection].
    { (* Immediate *)
      exact (
        Ref.Core.Immediate (
          match value with
          | Some a => Some (stub.(projection) a)
          | None => None
          end
        )
      ).
    }
    { (* Mutable *)
      exact (
        Ref.Core.Mutable
          address
          (path ++ stub.(RefStub.path))
          big_to_value
          (fun big_a =>
            match projection big_a with
            | Some a => Some (stub.(RefStub.projection) a)
            | None => None
            end
          )
          (fun big_a new_sub_a =>
            match projection big_a with
            | Some a =>
              let new_a := stub.(RefStub.injection) a new_sub_a in
              injection big_a new_a
            | None => None
            end
          )
      ).
    }
  Defined.

  Definition apply {A Sub_A : Set} `{Link A} `{Link Sub_A}
      {kind_source kind_target : Pointer.Kind.t}
      (ref : Ref.t kind_source A)
      (stub : t A Sub_A) :
      Ref.t kind_target Sub_A :=
    {| Ref.core := apply_core ref.(Ref.core) stub |}.
End RefStub.
