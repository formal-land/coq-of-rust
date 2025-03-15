Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import CoqOfRust.simulations.M.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter_types.

Module StackTrait.
  Record Run (Self : Set) `{Link Self} (link : StackTrait.Run Self) : Set := {
    len Stack self :
      Run.Trait Stack (link.(StackTrait.len).(TraitMethod.run) self);
    is_empty Stack self :
      Run.Trait Stack (link.(StackTrait.is_empty).(TraitMethod.run) self);
    push Stack self value :
      Run.Trait Stack (link.(StackTrait.push).(TraitMethod.run) self value);
    push_b256 Stack self value :
      Run.Trait Stack (link.(StackTrait.push_b256).(TraitMethod.run) self value);
    popn Stack N self :
      Run.Trait Stack (link.(StackTrait.popn).(TraitMethod.run) N self);
    popn_top Stack POPN self :
      Run.Trait Stack (link.(StackTrait.popn_top).(TraitMethod.run) POPN self);
    top Stack self :
      Run.Trait Stack (link.(StackTrait.top).(TraitMethod.run) self);
    pop Stack self :
      Run.Trait Stack (link.(StackTrait.pop).(TraitMethod.run) self);
    pop_address Stack self :
      Run.Trait Stack (link.(StackTrait.pop_address).(TraitMethod.run) self);
    exchange Stack self n m :
      Run.Trait Stack (link.(StackTrait.exchange).(TraitMethod.run) self n m);
    dup Stack self n :
      Run.Trait Stack (link.(StackTrait.dup).(TraitMethod.run) self n);
  }.
End StackTrait.

Module LoopControl.
  Record Run (Self : Set) `{Link Self} (link : LoopControl.Run Self) : Set := {
    set_instruction_result Stack self result :
      Run.Trait Stack (link.(LoopControl.set_instruction_result).(TraitMethod.run) self result);
    set_next_action Stack self action result :
      Run.Trait Stack (link.(LoopControl.set_next_action).(TraitMethod.run) self action result);
    gas Stack self :
      Run.Trait Stack (link.(LoopControl.gas).(TraitMethod.run) self);
    instruction_result Stack self :
      Run.Trait Stack (link.(LoopControl.instruction_result).(TraitMethod.run) self);
    take_next_action Stack self :
      Run.Trait Stack (link.(LoopControl.take_next_action).(TraitMethod.run) self);
  }.
End LoopControl.

Module InterpreterTypes.
  Class Run
      (Self : Set) `{Link Self}
      (types : InterpreterTypes.Types.t) `{InterpreterTypes.Types.AreLinks types}
      (link : InterpreterTypes.Run Self types) :
      Set :=
  {
    run_StackTrait_for_Stack :
      StackTrait.Run
        types.(InterpreterTypes.Types.Stack)
        link.(InterpreterTypes.run_StackTrait_for_Stack);
    run_LoopControl_for_Control :
      LoopControl.Run
        types.(InterpreterTypes.Types.Control)
        link.(InterpreterTypes.run_LoopControl_for_Control);
  }.
End InterpreterTypes.
