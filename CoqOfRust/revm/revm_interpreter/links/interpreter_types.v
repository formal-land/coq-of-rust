Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import revm_interpreter.interpreter_types.

Import Run.

(*
pub trait InterpreterTypes {
    type Stack: StackTrait;
    type Memory: MemoryTrait;
    type Bytecode: Jumps + Immediates + LegacyBytecode + EofData + EofContainer + EofCodeInfo;
    type ReturnData: ReturnData;
    type Input: InputsTrait;
    type SubRoutineStack: SubRoutineStack;
    type Control: LoopControl;
    type RuntimeFlag: RuntimeFlag;
    type Extend;
}
*)
Module InterpreterTypes.
  Class Trait (Self : Set) : Type := {
    Stack : Set;
    Memory : Set;
    Bytecode : Set;
    ReturnData : Set;
    Input : Set;
    SubRoutineStack : Set;
    Control : Set;
    RuntimeFlag : Set;
    Extend : Set;
  }.

  Module HasLinks.
    Class t (Self : Set) `{Trait Self} : Set := {
      H_Stack : Link (Stack (Self := Self));
      H_Memory : Link (Memory (Self := Self));
      H_Bytecode : Link (Bytecode (Self := Self));
      H_ReturnData : Link (ReturnData (Self := Self));
      H_Input : Link (Input (Self := Self));
      H_SubRoutineStack : Link (SubRoutineStack (Self := Self));
      H_Control : Link (Control (Self := Self));
      H_RuntimeFlag : Link (RuntimeFlag (Self := Self));
      H_Extend : Link (Extend (Self := Self));
    }.

    Global Instance StackIsLink {Self : Set} `{Trait Self} `{H_t : t Self} :
        Link (Stack (Self := Self)) :=
      H_t.(H_Stack).
    Global Instance MemoryIsLink {Self : Set} `{Trait Self} `{H_t : t Self} :
        Link (Memory (Self := Self)) :=
      H_t.(H_Memory).
    Global Instance BytecodeIsLink {Self : Set} `{Trait Self} `{H_t : t Self} :
        Link (Bytecode (Self := Self)) :=
      H_t.(H_Bytecode).
    Global Instance ReturnDataIsLink {Self : Set} `{Trait Self} `{H_t : t Self} :
        Link (ReturnData (Self := Self)) :=
      H_t.(H_ReturnData).
    Global Instance InputIsLink {Self : Set} `{Trait Self} `{H_t : t Self} :
        Link (Input (Self := Self)) :=
      H_t.(H_Input).
    Global Instance SubRoutineStackIsLink {Self : Set} `{Trait Self} `{H_t : t Self} :
        Link (SubRoutineStack (Self := Self)) :=
      H_t.(H_SubRoutineStack).
    Global Instance ControlIsLink {Self : Set} `{Trait Self} `{H_t : t Self} :
        Link (Control (Self := Self)) :=
      H_t.(H_Control).
    Global Instance RuntimeFlagIsLink {Self : Set} `{Trait Self} `{H_t : t Self} :
        Link (RuntimeFlag (Self := Self)) :=
      H_t.(H_RuntimeFlag).
    Global Instance ExtendIsLink {Self : Set} `{Trait Self} `{H_t : t Self} :
        Link (Extend (Self := Self)) :=
      H_t.(H_Extend).
  End HasLinks.
End InterpreterTypes.