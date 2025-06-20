Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import CoqOfRust.simulate.M.
Require Import alloy_primitives.links.aliases.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.instructions.links.arithmetic.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.

Definition make_ref {A : Set} `{Link A} {kind : Pointer.Kind.t} (index : nat) : Ref.t kind A :=
  {| Ref.core := Ref.Core.Mutable (A := A) index [] φ Some (fun _ => Some) |}.

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

Module Loop.
 Class C
      (WIRE_types : InterpreterTypes.Types.t) `{InterpreterTypes.Types.AreLinks WIRE_types} :
      Set := {
    gas : RefStub.t WIRE_types.(InterpreterTypes.Types.Control) Gas.t;
  }.

  Module Eq.
    Class t
        (WIRE : Set) (WIRE_types : InterpreterTypes.Types.t)
        `{Link WIRE} `{InterpreterTypes.Types.AreLinks WIRE_types}
        (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
        (I : C WIRE_types) :
        Prop := {
      gas
          (Stack : list Set)
          (interpreter : Interpreter.t WIRE WIRE_types)
          (stack_rest : Stack.to_Set Stack) :
        let ref_interpreter : Ref.t Pointer.Kind.MutRef _ := make_ref 0 in
        let ref_self := {| Ref.core :=
            SubPointer.Runner.apply
              ref_interpreter.(Ref.core)
              Interpreter.SubPointer.get_control
        |} in
        {{
          StackM.eval_f (Stack := Interpreter.t WIRE WIRE_types :: Stack)
            (run_InterpreterTypes_for_WIRE.(InterpreterTypes.run_LoopControl_for_Control).(LoopControl.gas).(TraitMethod.run)
              ref_self
            )
            (interpreter, stack_rest) 🌲
          (Output.Success (RefStub.apply ref_self I.(gas)), (interpreter, stack_rest))
        }};
    }.
  End Eq.
End Loop.

Module Stack.
  (* Definition t : Set :=
    list aliases.U256.t. *)

  (* Fixpoint popn_top (POPN : nat) (stack : t) :
      option (array.t aliases.U256.t {| Integer.value := Z.of_nat POPN |}) * t :=
    match POPN, stack with
    | O, [] => (Some {| array.value := [] |}, stack)
    | S POPN, [] => (None, stack)
    | S POPN, x :: xs =>
        match popn_top POPN xs with
        | (Some a, stack') => (Some {| array.value := x:: a.(array.value) |}, stack')
        | (None, _) => (None, stack)
        end
    | _, _ => (None, stack)
    end. *)

  (* Definition pop2_top (stack : t) : option (array.t aliases.U256.t {| Integer.value := 2 |}) * t :=
    match stack with
    | x1 :: x2 :: rest => (Some {| array.value := [x1; x2] |}, rest)
    | _ => (None, stack)
    end. *)

  Class C
      (WIRE_types : InterpreterTypes.Types.t) `{InterpreterTypes.Types.AreLinks WIRE_types} :
      Type := {
    popn_top :
      forall
        (POPN : Usize.t)
        (self : WIRE_types.(InterpreterTypes.Types.Stack)),
      option (
        array.t aliases.U256.t POPN *
        RefStub.t WIRE_types.(InterpreterTypes.Types.Stack) aliases.U256.t
      ) *
      WIRE_types.(InterpreterTypes.Types.Stack);
  }.

  Module Eq.
    Class t
        (WIRE : Set) (WIRE_types : InterpreterTypes.Types.t)
        `{Link WIRE} `{InterpreterTypes.Types.AreLinks WIRE_types}
        (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
        (I : C WIRE_types) :
        Prop := {
      popn_top
          (Stack : list Set)
          (interpreter : Interpreter.t WIRE WIRE_types)
          (stack_rest : Stack.to_Set Stack)
          (POPN : Usize.t) :
        let ref_interpreter : Ref.t Pointer.Kind.MutRef _ := make_ref 0 in
        let ref_self := {| Ref.core :=
          SubPointer.Runner.apply
            ref_interpreter.(Ref.core)
            Interpreter.SubPointer.get_stack
        |} in
        {{
          StackM.eval_f (Stack := Interpreter.t WIRE WIRE_types :: Stack)
            (run_InterpreterTypes_for_WIRE.(InterpreterTypes.run_StackTrait_for_Stack).(StackTrait.popn_top).(TraitMethod.run)
              POPN
              ref_self
            )
            (interpreter, stack_rest) 🌲
          let (result, self) := I.(popn_top) POPN interpreter.(Interpreter.stack) in
          let result :=
            match result with
            | Some (a, stub) => Some (a, RefStub.apply ref_self stub)
            | None => None
            end in
          (Output.Success result, (interpreter <| Interpreter.stack := self |>, stack_rest))
        }};
    }.
  End Eq.
End Stack.

Parameter wrapping_add :
  forall {BITS LIMBS : Usize.t} (x1 x2 : lib.Uint.t BITS LIMBS),
  lib.Uint.t BITS LIMBS.

Lemma wrapping_add_eq (BITS LIMBS : Usize.t) (x1 x2 : lib.Uint.t BITS LIMBS) :
  links.M.evaluate (add.Impl_Uint.run_wrapping_add BITS LIMBS x1 x2).(Run.run_f) =
  links.M.LowM.Pure (Output.Success (wrapping_add x1 x2)).
Admitted.

Axiom ex_falso : False.

Lemma add_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (ILoop : Loop.C WIRE_types)
    (LoopEq : Loop.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE ILoop)
    (IStack : Stack.C WIRE_types)
    (StackEq : Stack.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IStack)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (_host : H) :
  let ref_interpreter := make_ref 0 in
  let ref_host := make_ref 1 in
  {{
    StackM.eval_f (Stack := [_; _]) (run_add run_InterpreterTypes_for_WIRE ref_interpreter ref_host) (interpreter, (_host, tt)) 🌲
    let stack := interpreter.(Interpreter.stack) in
    let (result, stack) := IStack.(Stack.popn_top) {| Integer.value := 1 |} stack in
    match result with
    | Some (arr, top) =>
      match arr.(array.value) with
      | x1 :: _ =>
        let x2 := top.(RefStub.projection) stack in
        let stack := top.(RefStub.injection) stack (wrapping_add x1 x2) in
        (Output.Success tt, (interpreter <| Interpreter.stack := stack |>, (_host, tt)))
      | _ =>
        (* admitted for now, but we should make it impossible by typing *)
        (Output.Exception Output.Exception.BreakMatch, (interpreter, (_host, tt)))
      end
    | None =>
      (
        Output.Exception (Output.Exception.Panic (Panic.Make "no match branches left")),
        (interpreter <| Interpreter.stack := stack |>, (_host, tt))
      )
    end
  }}.
Proof.
  intros.
  destruct LoopEq, StackEq.
  Time unfold run_add, StackM.eval_f, StackM.eval, evaluate.
  Time hnf.
  Time cbn.
  Time get_can_access.
  Time cbn.
  Time eapply Run.Call. {
    apply gas.
  }
  Time cbn.
  Time eapply Run.Call. {
    Time apply Run.Pure.
  }
  Time cbn.
  Time get_can_access.
  Show.
  dsfjlkj.
    apply popn_top.
  }
  Time destruct IStack.(Stack.popn_top) as [[[? ?]|] ?].
  { Time get_can_access.
    Time cbn.
    Time destruct t0.(array.value).
    { Time cbn.
      destruct ex_falso.
    }
    { Time cbn.
      Time repeat get_can_access.
      Time eapply Run.Call. {
        rewrite wrapping_add_eq.
        apply Run.Pure.
      }
      Time cbn.
      (* admit. because slow *)
      Time repeat get_can_access.
      Time apply Run.Pure.
    }
  }
  { Time cbn.
    Time repeat get_can_access.
    Time apply Run.Pure.
  }
Qed.
