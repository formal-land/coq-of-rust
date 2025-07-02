Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import CoqOfRust.simulate.M.
Require Import alloy_primitives.links.aliases.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.

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
