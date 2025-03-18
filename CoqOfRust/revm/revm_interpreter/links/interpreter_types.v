Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require core.links.array.
Require core.ops.links.deref.
Require core.ops.links.range.
Require Import core.links.option.
Require Import revm.revm_bytecode.eof.links.types_section.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.interpreter_types.
Require Import revm.revm_specification.links.hardfork.
Require Import revm.links.dependencies.

Import Run.

(*
pub trait StackTrait {
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool;
    fn push(&mut self, value: U256) -> bool;
    fn push_b256(&mut self, value: B256) -> bool;
    fn popn<const N: usize>(&mut self) -> Option<[U256; N]>;
    fn popn_top<const POPN: usize>(&mut self) -> Option<([U256; POPN], &mut U256)>;
    fn top(&mut self) -> Option<&mut U256>;
    fn pop(&mut self) -> Option<U256>;
    fn pop_address(&mut self) -> Option<Address>;
    fn exchange(&mut self, n: usize, m: usize) -> bool;
    fn dup(&mut self, n: usize) -> bool;
}
*)
Module StackTrait.
  Record Run (Self : Set) `{Link Self} : Set := {
    trait := ("revm_interpreter::interpreter_types::StackTrait", [], [], Φ Self);
    len :
      TraitMethod.C trait "len" (fun method =>
        forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self ] Usize.t
      );
    is_empty :
      TraitMethod.C trait "is_empty" (fun method =>
        forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self ] bool
      );
    push :
      TraitMethod.C trait "push" (fun method =>
        forall (self : Ref.t Pointer.Kind.MutRef Self) (value : U256.t),
        Run.Trait method [] [] [ φ self; φ value ] bool
      );
    push_b256 :
      TraitMethod.C trait "push_b256" (fun method =>
        forall (self : Ref.t Pointer.Kind.MutRef Self) (value : B256.t),
        Run.Trait method [] [] [ φ self; φ value ] bool
      );
    popn :
      TraitMethod.C trait "popn" (fun method =>
        forall (N : Usize.t) (self : Ref.t Pointer.Kind.MutRef Self),
        Run.Trait method [ φ N ] [] [ φ self ] (option (array.t U256.t N))
      );
    popn_top :
      TraitMethod.C trait "popn_top" (fun method =>
        forall (POPN : Usize.t) (self : Ref.t Pointer.Kind.MutRef Self),
        Run.Trait method [ φ POPN ] [] [ φ self ]
          (option (array.t U256.t POPN * Ref.t Pointer.Kind.MutRef U256.t))
      );
    top :
      TraitMethod.C trait "top" (fun method =>
        forall (self : Ref.t Pointer.Kind.MutRef Self),
        Run.Trait method [] [ Φ U256.t ] [ φ self ] (option (Ref.t Pointer.Kind.MutRef U256.t))
      );
    pop :
      TraitMethod.C trait "pop" (fun method =>
        forall (self : Ref.t Pointer.Kind.MutRef Self),
        Run.Trait method [] [ Φ U256.t ] [ φ self ] (option U256.t)
      );
    pop_address :
      TraitMethod.C trait "pop_address" (fun method =>
        forall (self : Ref.t Pointer.Kind.MutRef Self),
        Run.Trait method [] [ Φ alloy_primitives.bits.links.address.Address.t ] [ φ self ] (option alloy_primitives.bits.links.address.Address.t)
      );
    exchange :
      TraitMethod.C trait "exchange" (fun method =>
        forall (self : Ref.t Pointer.Kind.MutRef Self) (n m : Usize.t),
        Run.Trait method [] [] [ φ self; φ n; φ m ] bool
      );
    dup :
      TraitMethod.C trait "dup" (fun method =>
        forall (self : Ref.t Pointer.Kind.MutRef Self) (n : Usize.t),
        Run.Trait method [] [] [ φ self; φ n ] bool
      );
  }. 
End StackTrait.

(*
pub trait MemoryTrait {
    fn set_data(&mut self, memory_offset: usize, data_offset: usize, len: usize, data: &[u8]);
    fn set(&mut self, memory_offset: usize, data: &[u8]);
    fn size(&self) -> usize;
    fn copy(&mut self, destination: usize, source: usize, len: usize);
    fn slice(&self, range: Range<usize>) -> impl Deref<Target = [u8]> + '_;
    fn slice_len(&self, offset: usize, len: usize) -> impl Deref<Target = [u8]> + '_;
    fn resize(&mut self, new_size: usize) -> bool;
}
*)
Module MemoryTrait.
  Record Run (Self : Set) `{Link Self} : Set := {
    trait := ("revm_interpreter::interpreter_types::MemoryTrait", [], [], Φ Self);
    set_data :
      TraitMethod.C trait "set_data" (fun method =>
        forall
          (self : Ref.t Pointer.Kind.MutRef Self)
          (memory_offset data_offset len : Usize.t)
          (data : Ref.t Pointer.Kind.Ref (list U8.t)),
        Run.Trait method [] [] [ φ self; φ memory_offset; φ data_offset; φ len; φ data ] unit
      );
    set :
      TraitMethod.C trait "set" (fun method =>
        forall
          (self : Ref.t Pointer.Kind.MutRef Self)
          (memory_offset : Usize.t)
          (data : Ref.t Pointer.Kind.Ref (list U8.t)),
        Run.Trait method [] [] [ φ self; φ memory_offset; φ data ] unit
      );
    size :
      TraitMethod.C trait "size" (fun method =>
        forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self ] Usize.t
      );
    copy :
      TraitMethod.C trait "copy" (fun method =>
        forall
          (self : Ref.t Pointer.Kind.MutRef Self)
          (destination source len : Usize.t),
        Run.Trait method [] [] [ φ self; φ destination; φ source; φ len ] unit
      );
    slice :
      TraitMethod.C trait "slice" (fun method =>
        forall
          (Output : Set) `(Link Output)
          (run_Deref_for_Output : deref.Deref.Run Output (Target := list U8.t))
          (self : Ref.t Pointer.Kind.Ref Self)
          (range : Ref.t Pointer.Kind.Ref (range.Range.t Usize.t)),
        Run.Trait method [] [ Φ Output ] [ φ self; φ range ] Output
      );
    slice_len :
      TraitMethod.C trait "slice_len" (fun method =>
        forall
          (Output : Set) `(Link Output)
          (run_Deref_for_Output : deref.Deref.Run Output (Target := list U8.t))
          (self : Ref.t Pointer.Kind.Ref Self)
          (offset len : Usize.t),
        Run.Trait method [] [ Φ Output ] [ φ self; φ offset; φ len ] Output
      );
    resize :
      TraitMethod.C trait "resize" (fun method =>
        forall (self : Ref.t Pointer.Kind.MutRef Self) (new_size : Usize.t),
        Run.Trait method [] [] [ φ self; φ new_size ] bool
      );
  }.
End MemoryTrait.

(*
pub trait Jumps {
    fn relative_jump(&mut self, offset: isize);
    fn absolute_jump(&mut self, offset: usize);
    fn is_valid_legacy_jump(&mut self, offset: usize) -> bool;
    fn pc(&self) -> usize;
    fn opcode(&self) -> u8;
}
*)
Module Jumps.
  Record Run (Self : Set) `{Link Self} : Set := {
    trait := ("revm_interpreter::interpreter_types::Jumps", [], [], Φ Self);
    relative_jump :
      TraitMethod.C trait "relative_jump" (fun method =>
        forall (self : Ref.t Pointer.Kind.MutRef Self) (offset : Isize.t),
        Run.Trait method [] [] [ φ self; φ offset ] unit
      );
    absolute_jump :
      TraitMethod.C trait "absolute_jump" (fun method =>
        forall (self : Ref.t Pointer.Kind.MutRef Self) (offset : Usize.t),
        Run.Trait method [] [] [ φ self; φ offset ] unit
      );
    is_valid_legacy_jump :
      TraitMethod.C trait "is_valid_legacy_jump" (fun method =>
        forall (self : Ref.t Pointer.Kind.MutRef Self) (offset : Usize.t),
        Run.Trait method [] [] [ φ self; φ offset ] bool
      );
    pc :
      TraitMethod.C trait "pc" (fun method =>
        forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self ] Usize.t
      );
    opcode :
      TraitMethod.C trait "opcode" (fun method =>
        forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self ] U8.t
      );
  }.
End Jumps.

(*
pub trait Immediates {
    fn read_i16(&self) -> i16;
    fn read_u16(&self) -> u16;
    fn read_i8(&self) -> i8;
    fn read_u8(&self) -> u8;
    fn read_offset_i16(&self, offset: isize) -> i16;
    fn read_offset_u16(&self, offset: isize) -> u16;
    fn read_slice(&self, len: usize) -> &[u8];
}
*)
Module Immediates.
  Record Run (Self : Set) `{Link Self} : Set := {
    trait := ("revm_interpreter::interpreter_types::Immediates", [], [], Φ Self);
    read_i16 :
      TraitMethod.C trait "read_i16" (fun method =>
        forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self ] I16.t
      );
    read_u16 :
      TraitMethod.C trait "read_u16" (fun method =>
        forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self ] U16.t
      );
    read_i8 :
      TraitMethod.C trait "read_i8" (fun method =>
        forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self ] I8.t
      );
    read_u8 :
      TraitMethod.C trait "read_u8" (fun method =>
        forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self ] U8.t
      );
    read_offset_i16 :
      TraitMethod.C trait "read_offset_i16" (fun method =>
        forall (self : Ref.t Pointer.Kind.Ref Self) (offset : Isize.t),
        Run.Trait method [] [] [ φ self; φ offset ] I16.t
      );
    read_offset_u16 :
      TraitMethod.C trait "read_offset_u16" (fun method =>
        forall (self : Ref.t Pointer.Kind.Ref Self) (offset : Isize.t),
        Run.Trait method [] [] [ φ self; φ offset ] U16.t
      );
    read_slice :
      TraitMethod.C trait "read_slice" (fun method =>
        forall (self : Ref.t Pointer.Kind.Ref Self) (len : Usize.t),
        Run.Trait method [] [] [ φ self; φ len ] (Ref.t Pointer.Kind.Ref (list U8.t))
      );
  }.
End Immediates.

(*
pub trait LegacyBytecode {
    fn bytecode_len(&self) -> usize;
    fn bytecode_slice(&self) -> &[u8];
}
*)
Module LegacyBytecode.
  Record Run (Self : Set) `{Link Self} : Set := {
    trait := ("revm_interpreter::interpreter_types::LegacyBytecode", [], [], Φ Self);
    bytecode_len :
      TraitMethod.C trait "bytecode_len" (fun method =>
        forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self ] Usize.t
      );
    bytecode_slice :
      TraitMethod.C trait "bytecode_slice" (fun method =>
        forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self ] (Ref.t Pointer.Kind.Ref (list U8.t))
      );
  }.
End LegacyBytecode.

(*
pub trait EofData {
    fn data(&self) -> &[u8];
    fn data_slice(&self, offset: usize, len: usize) -> &[u8];
    fn data_size(&self) -> usize;
}
*)
Module EofData.
  Record Run (Self : Set) `{Link Self} : Set := {
    trait := ("revm_interpreter::interpreter_types::EofData", [], [], Φ Self);
    data :
      TraitMethod.C trait "data" (fun method =>
        forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self ] (Ref.t Pointer.Kind.Ref (list U8.t))
      );
    data_slice :
      TraitMethod.C trait "data_slice" (fun method =>
        forall (self : Ref.t Pointer.Kind.Ref Self) (offset len : Usize.t),
        Run.Trait method [] [] [ φ self; φ offset; φ len ] (Ref.t Pointer.Kind.Ref (list U8.t))
      );
    data_size :
      TraitMethod.C trait "data_size" (fun method =>
        forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self ] Usize.t
      );
  }.
End EofData.

(*
pub trait EofContainer {
    fn eof_container(&self, index: usize) -> Option<&Bytes>;
}
*)
Module EofContainer.
  Record Run (Self : Set) `{Link Self} : Set := {
    trait := ("revm_interpreter::interpreter_types::EofContainer", [], [], Φ Self);
    eof_container :
      TraitMethod.C trait "eof_container" (fun method =>
        forall (self : Ref.t Pointer.Kind.Ref Self) (index : Usize.t),
        Run.Trait method [] [] [ φ self; φ index ] (option (Ref.t Pointer.Kind.Ref alloy_primitives.links.bytes_.Bytes.t))
      );
  }.
End EofContainer.

(*
pub trait EofCodeInfo {
    fn code_section_info(&self, idx: usize) -> Option<&TypesSection>;
    fn code_section_pc(&self, idx: usize) -> Option<usize>;
}
*)
Module EofCodeInfo.
  Record Run (Self : Set) `{Link Self} : Set := {
    trait := ("revm_interpreter::interpreter_types::EofCodeInfo", [], [], Φ Self);
    code_section_info :
      TraitMethod.C trait "code_section_info" (fun method =>
        forall (self : Ref.t Pointer.Kind.Ref Self) (idx : Usize.t),
        Run.Trait method [] [] [ φ self; φ idx ] (option (Ref.t Pointer.Kind.Ref TypesSection.t))
      );
    code_section_pc :
      TraitMethod.C trait "code_section_pc" (fun method =>
        forall (self : Ref.t Pointer.Kind.Ref Self) (idx : Usize.t),
        Run.Trait method [] [] [ φ self; φ idx ] (option Usize.t)
      );
  }.
End EofCodeInfo.

(*
pub trait ReturnData {
    fn buffer(&self) -> &[u8];
    fn buffer_mut(&mut self) -> &mut Bytes;
}
*)
Module ReturnData.
  Record Run (Self : Set) `{Link Self} : Set := {
    trait := ("revm_interpreter::interpreter_types::ReturnData", [], [], Φ Self);
    buffer :
      TraitMethod.C trait "buffer" (fun method =>
        forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self ] (Ref.t Pointer.Kind.Ref (list U8.t))
      );
    buffer_mut :
      TraitMethod.C trait "buffer_mut" (fun method =>
        forall (self : Ref.t Pointer.Kind.MutRef Self),
        Run.Trait method [] [] [ φ self ] (Ref.t Pointer.Kind.MutRef alloy_primitives.links.bytes_.Bytes.t)
      );
  }.
End ReturnData.

(*
pub trait InputsTrait {
    fn target_address(&self) -> Address;
    fn caller_address(&self) -> Address;
    fn input(&self) -> &[u8];
    fn call_value(&self) -> U256;
}
*)
Module InputsTrait.
  Record Run (Self : Set) `{Link Self} : Set := {
    trait := ("revm_interpreter::interpreter_types::InputsTrait", [], [], Φ Self);
    target_address :
      TraitMethod.C trait "target_address" (fun method =>
        forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self ] alloy_primitives.bits.links.address.Address.t
      );
    caller_address :
      TraitMethod.C trait "caller_address" (fun method =>
        forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self ] alloy_primitives.bits.links.address.Address.t
      );
    input :
      TraitMethod.C trait "input" (fun method =>
        forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self ] (Ref.t Pointer.Kind.Ref (list U8.t))
      );
    call_value :
      TraitMethod.C trait "call_value" (fun method =>
        forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self ] U256.t
      );
  }.
End InputsTrait.

(*
pub trait SubRoutineStack {
    fn len(&self) -> usize;
    fn is_empty(&self) -> bool;
    fn routine_idx(&self) -> usize;
    fn set_routine_idx(&mut self, idx: usize);
    fn push(&mut self, old_program_counter: usize, new_idx: usize) -> bool;
    fn pop(&mut self) -> Option<usize>;
}
*)
Module SubRoutineStack.
  Record Run (Self : Set) `{Link Self} : Set := {
    trait := ("revm_interpreter::interpreter_types::SubRoutineStack", [], [], Φ Self);
    len :
      TraitMethod.C trait "len" (fun method =>
        forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self ] Usize.t
      );
    is_empty :
      TraitMethod.C trait "is_empty" (fun method =>
        forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self ] bool
      );
    routine_idx :
      TraitMethod.C trait "routine_idx" (fun method =>
        forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self ] Usize.t
      );
    set_routine_idx :
      TraitMethod.C trait "set_routine_idx" (fun method =>
        forall (self : Ref.t Pointer.Kind.MutRef Self) (idx : Usize.t),
        Run.Trait method [] [] [ φ self; φ idx ] unit
      );
    push :
      TraitMethod.C trait "push" (fun method =>
        forall (self : Ref.t Pointer.Kind.MutRef Self) (old_program_counter new_idx : Usize.t),
        Run.Trait method [] [] [ φ self; φ old_program_counter; φ new_idx ] bool
      );
    pop :
      TraitMethod.C trait "pop" (fun method =>
        forall (self : Ref.t Pointer.Kind.MutRef Self),
        Run.Trait method [] [] [ φ self ] (option Usize.t)
      );
  }.
End SubRoutineStack.

(*
pub trait LoopControl {
    fn set_instruction_result(&mut self, result: InstructionResult);
    fn set_next_action(&mut self, action: InterpreterAction, result: InstructionResult);
    fn gas(&mut self) -> &mut Gas;
    fn instruction_result(&self) -> InstructionResult;
    fn take_next_action(&mut self) -> InterpreterAction;
}
*)
Module LoopControl.
  Record Run (Self : Set) `{Link Self} : Set := {
    trait := ("revm_interpreter::interpreter_types::LoopControl", [], [], Φ Self);
    set_instruction_result :
      TraitMethod.C trait "set_instruction_result" (fun method =>
        forall (self : Ref.t Pointer.Kind.MutRef Self) (result : InstructionResult.t),
        Run.Trait method [] [] [ φ self; φ result ] unit
      );
    set_next_action :
      TraitMethod.C trait "set_next_action" (fun method =>
        forall
          (self : Ref.t Pointer.Kind.MutRef Self)
          (action : InterpreterAction.t)
          (result : InstructionResult.t),
        Run.Trait method [] [] [ φ self; φ action; φ result ] unit
      );
    gas :
      TraitMethod.C trait "gas" (fun method =>
        forall (self : Ref.t Pointer.Kind.MutRef Self),
        Run.Trait method [] [] [ φ self ] (Ref.t Pointer.Kind.MutRef Gas.t)
      );
    instruction_result :
      TraitMethod.C trait "instruction_result" (fun method =>
        forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self ] InstructionResult.t
      );
    take_next_action :
      TraitMethod.C trait "take_next_action" (fun method =>
        forall (self : Ref.t Pointer.Kind.MutRef Self),
        Run.Trait method [] [] [ φ self ] InterpreterAction.t
      );
  }.
End LoopControl.

(*
pub trait RuntimeFlag {
    fn is_static(&self) -> bool;
    fn is_eof(&self) -> bool;
    fn is_eof_init(&self) -> bool;
    fn spec_id(&self) -> SpecId;
}
*)
Module RuntimeFlag.
  Record Run (Self : Set) `{Link Self} : Set := {
    trait := ("revm_interpreter::interpreter_types::RuntimeFlag", [], [], Φ Self);
    is_static :
      TraitMethod.C trait "is_static" (fun method =>
        forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self ] bool
      );
    is_eof :
      TraitMethod.C trait "is_eof" (fun method =>
        forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self ] bool
      );
    is_eof_init :
      TraitMethod.C trait "is_eof_init" (fun method =>
        forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self ] bool
      );
    spec_id :
      TraitMethod.C trait "spec_id" (fun method =>
        forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self ] SpecId.t
      );
  }.
End RuntimeFlag.

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
  Module Types.
    Record t : Type := {
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

    Class AreLinks (types : t) : Set := {
      H_Stack : Link types.(Stack);
      H_Memory : Link types.(Memory);
      H_Bytecode : Link types.(Bytecode);
      H_ReturnData : Link types.(ReturnData);
      H_Input : Link types.(Input);
      H_SubRoutineStack : Link types.(SubRoutineStack);
      H_Control : Link types.(Control);
      H_RuntimeFlag : Link types.(RuntimeFlag);
      H_Extend : Link types.(Extend);
    }.

    Global Instance IsLinkStack (types : t) (H : AreLinks types) : Link types.(Stack) :=
      H.(H_Stack _).
    Global Instance IsLinkMemory (types : t) (H : AreLinks types) : Link types.(Memory) :=
      H.(H_Memory _).
    Global Instance IsLinkBytecode (types : t) (H : AreLinks types) : Link types.(Bytecode) :=
      H.(H_Bytecode _).
    Global Instance IsLinkReturnData (types : t) (H : AreLinks types) : Link types.(ReturnData) :=
      H.(H_ReturnData _).
    Global Instance IsLinkInput (types : t) (H : AreLinks types) : Link types.(Input) :=
      H.(H_Input _).
    Global Instance IsLinkSubRoutineStack (types : t) (H : AreLinks types) : Link types.(SubRoutineStack) :=
      H.(H_SubRoutineStack _).
    Global Instance IsLinkControl (types : t) (H : AreLinks types) : Link types.(Control) :=
      H.(H_Control _).
    Global Instance IsLinkRuntimeFlag (types : t) (H : AreLinks types) : Link types.(RuntimeFlag) :=
      H.(H_RuntimeFlag _).
    Global Instance IsLinkExtend (types : t) (H : AreLinks types) : Link types.(Extend) :=
      H.(H_Extend _).
  End Types.

  Record Run
      (Self : Set) `{Link Self}
      (types : Types.t) `{Types.AreLinks types} :
      Set := {
    Stack_IsAssociated :
      IsTraitAssociatedType
        "revm_interpreter::interpreter_types::InterpreterTypes" [] [] (Φ Self)
        "Stack" (Φ types.(Types.Stack));
    run_StackTrait_for_Stack : StackTrait.Run types.(Types.Stack);
    Memory_IsAssociated :
      IsTraitAssociatedType
        "revm_interpreter::interpreter_types::InterpreterTypes" [] [] (Φ Self)
        "Memory" (Φ types.(Types.Memory));
    run_MemoryTrait_for_Memory : MemoryTrait.Run types.(Types.Memory);
    Bytecode_IsAssociated :
      IsTraitAssociatedType
        "revm_interpreter::interpreter_types::InterpreterTypes" [] [] (Φ Self)
        "Bytecode" (Φ types.(Types.Bytecode));
    run_Jumps_for_Bytecode : Jumps.Run types.(Types.Bytecode);
    run_Immediates_for_Bytecode : Immediates.Run types.(Types.Bytecode);
    run_LegacyBytecode_for_Bytecode : LegacyBytecode.Run types.(Types.Bytecode);
    run_EofData_for_Bytecode : EofData.Run types.(Types.Bytecode);
    run_EofContainer_for_Bytecode : EofContainer.Run types.(Types.Bytecode);
    run_EofCodeInfo_for_Bytecode : EofCodeInfo.Run types.(Types.Bytecode);
    ReturnData_IsAssociated :
      IsTraitAssociatedType
        "revm_interpreter::interpreter_types::InterpreterTypes" [] [] (Φ Self)
        "ReturnData" (Φ types.(Types.ReturnData));
    run_ReturnData_for_ReturnData : ReturnData.Run types.(Types.ReturnData);
    Input_IsAssociated :
      IsTraitAssociatedType
        "revm_interpreter::interpreter_types::InterpreterTypes" [] [] (Φ Self)
        "Input" (Φ types.(Types.Input));
    run_InputsTrait_for_Input : InputsTrait.Run types.(Types.Input);
    SubRoutineStack_IsAssociated :
      IsTraitAssociatedType
        "revm_interpreter::interpreter_types::InterpreterTypes" [] [] (Φ Self)
        "SubRoutineStack" (Φ types.(Types.SubRoutineStack));
    run_SubRoutineStack_for_SubRoutineStack : SubRoutineStack.Run types.(Types.SubRoutineStack);
    Control_IsAssociated :
      IsTraitAssociatedType
        "revm_interpreter::interpreter_types::InterpreterTypes" [] [] (Φ Self)
        "Control" (Φ types.(Types.Control));
    run_LoopControl_for_Control : LoopControl.Run types.(Types.Control);
    RuntimeFlag_IsAssociated :
      IsTraitAssociatedType
        "revm_interpreter::interpreter_types::InterpreterTypes" [] [] (Φ Self)
        "RuntimeFlag" (Φ types.(Types.RuntimeFlag));
    run_RuntimeFlag_for_RuntimeFlag : RuntimeFlag.Run types.(Types.RuntimeFlag);
  }.
End InterpreterTypes.

Module Impl_RuntimeFlag.

  Parameter spec_id : PolymorphicFunction.t.

  Axiom Implements :
  forall (WIRE_types : InterpreterTypes.Types.t)
         (H2 : InterpreterTypes.Types.AreLinks WIRE_types),
    IsTraitInstance
      "revm_interpreter::interpreter_types::RuntimeFlag"
      []
      []
      (InterpreterTypes.Types.IsLinkRuntimeFlag WIRE_types H2).(Φ _)
      [("spec_id", InstanceField.Method Impl_RuntimeFlag.spec_id)].

  Instance run_spec_id_instance
        (WIRE_types : InterpreterTypes.Types.t)
        (H2 : InterpreterTypes.Types.AreLinks WIRE_types)
        (self : Ref.t Pointer.Kind.MutRef (InterpreterTypes.Types.RuntimeFlag WIRE_types))
        :
        Run.Trait spec_id [] [] [φ self] SpecId.t.
  Proof.
  Admitted.

End Impl_RuntimeFlag.
