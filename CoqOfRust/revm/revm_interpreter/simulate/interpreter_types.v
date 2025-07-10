Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import CoqOfRust.simulate.M.
Require Import alloy_primitives.links.aliases.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.

Module Stack.
  Class C
      (WIRE_types : InterpreterTypes.Types.t) `{InterpreterTypes.Types.AreLinks WIRE_types} :
      Type := {
    (* fn popn_top<const POPN: usize>(&mut self) -> Option<([U256; POPN], &mut U256)>; *)
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

Module Loop.
 Class C
      (WIRE_types : InterpreterTypes.Types.t) `{InterpreterTypes.Types.AreLinks WIRE_types} :
      Set := {
    (* fn set_instruction_result(&mut self, result: InstructionResult); *)
    set_instruction_result :
      forall
        (self : WIRE_types.(InterpreterTypes.Types.Control))
        (result : InstructionResult.t),
      WIRE_types.(InterpreterTypes.Types.Control);
    (* fn gas(&mut self) -> &mut Gas; *)
    gas : RefStub.t WIRE_types.(InterpreterTypes.Types.Control) Gas.t;
  }.

  Module Eq.
    Class t
        (WIRE : Set) (WIRE_types : InterpreterTypes.Types.t)
        `{Link WIRE} `{InterpreterTypes.Types.AreLinks WIRE_types}
        (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
        (I : C WIRE_types) :
        Prop := {
      set_instruction_result
          (StackRest : list Set)
          (interpreter : Interpreter.t WIRE WIRE_types)
          (stack_rest : Stack.to_Set StackRest)
          (result : InstructionResult.t) :
        let ref_interpreter : Ref.t Pointer.Kind.MutRef _ := make_ref 0 in
        let ref_self := {| Ref.core :=
            SubPointer.Runner.apply
              ref_interpreter.(Ref.core)
              Interpreter.SubPointer.get_control
        |} in
        let control' :=
          I.(set_instruction_result) interpreter.(Interpreter.control) result in
        {{
          StackM.eval_f (Stack := Interpreter.t WIRE WIRE_types :: StackRest)
            (run_InterpreterTypes_for_WIRE.(InterpreterTypes.run_LoopControl_for_Control).(LoopControl.set_instruction_result).(TraitMethod.run)
              ref_self
              result
            )
            (interpreter, stack_rest) 🌲
          (
            Output.Success tt,
            (interpreter <| Interpreter.control := control' |>, stack_rest)
          )
        }};
      gas
          (StackRest : list Set)
          (interpreter : Interpreter.t WIRE WIRE_types)
          (stack_rest : Stack.to_Set StackRest) :
        let ref_interpreter : Ref.t Pointer.Kind.MutRef _ := make_ref 0 in
        let ref_self := {| Ref.core :=
            SubPointer.Runner.apply
              ref_interpreter.(Ref.core)
              Interpreter.SubPointer.get_control
        |} in
        {{
          StackM.eval_f (Stack := Interpreter.t WIRE WIRE_types :: StackRest)
            (run_InterpreterTypes_for_WIRE.(InterpreterTypes.run_LoopControl_for_Control).(LoopControl.gas).(TraitMethod.run)
              ref_self
            )
            (interpreter, stack_rest) 🌲
          (Output.Success (RefStub.apply ref_self I.(gas)), (interpreter, stack_rest))
        }};
    }.
  End Eq.
End Loop.

Module InterpreterTypes.
  Class C
      (WIRE_types : InterpreterTypes.Types.t) `{InterpreterTypes.Types.AreLinks WIRE_types} :
      Type := {
    Stack : Stack.C WIRE_types;
    Loop : Loop.C WIRE_types;
  }.

  Module Eq.
    Class t
        (WIRE : Set) (WIRE_types : InterpreterTypes.Types.t)
        `{Link WIRE} `{InterpreterTypes.Types.AreLinks WIRE_types}
        (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
        (I : C WIRE_types) :
        Prop := {
      Stack : Stack.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE I.(Stack);
      Loop : Loop.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE I.(Loop);
    }.
  End Eq.
End InterpreterTypes.
