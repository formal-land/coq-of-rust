Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.links.aliases.
Require Import core.links.array.
Require Import core.ops.links.deref.
Require Import core.ops.links.range.
Require Import core.links.option.
Require Import revm.revm_bytecode.eof.links.types_section.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.interpreter_types.
Require Import revm.revm_specification.links.hardfork.

Import alloy_primitives.bits.links.address.
Import alloy_primitives.links.bytes_.

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
  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("revm_interpreter::interpreter_types::StackTrait", [], [], Φ Self).

  Definition Run_len (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "len" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] Usize.t
    ).

  Definition Run_is_empty (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "is_empty" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] bool
    ).

  Definition Run_push (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "push" (fun method =>
      forall (self : Ref.t Pointer.Kind.MutRef Self) (value : aliases.U256.t),
      Run.Trait method [] [] [ φ self; φ value ] bool
    ).

  Definition Run_push_b256 (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "push_b256" (fun method =>
      forall (self : Ref.t Pointer.Kind.MutRef Self) (value : aliases.B256.t),
      Run.Trait method [] [] [ φ self; φ value ] bool
    ).

  Definition Run_popn (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "popn" (fun method =>
      forall (N : Usize.t) (self : Ref.t Pointer.Kind.MutRef Self),
      Run.Trait method [ φ N ] [] [ φ self ] (option (array.t aliases.U256.t N))
    ).

  Definition Run_popn_top (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "popn_top" (fun method =>
      forall (POPN : Usize.t) (self : Ref.t Pointer.Kind.MutRef Self),
      Run.Trait method [ φ POPN ] [] [ φ self ]
        (option (array.t aliases.U256.t POPN * Ref.t Pointer.Kind.MutRef aliases.U256.t))
    ).

  Definition Run_top (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "top" (fun method =>
      forall (self : Ref.t Pointer.Kind.MutRef Self),
      Run.Trait method [] [ Φ aliases.U256.t ] [ φ self ] (option (Ref.t Pointer.Kind.MutRef aliases.U256.t))
    ).

  Definition Run_pop (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "pop" (fun method =>
      forall (self : Ref.t Pointer.Kind.MutRef Self),
      Run.Trait method [] [ Φ aliases.U256.t ] [ φ self ] (option aliases.U256.t)
    ).

  Definition Run_pop_address (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "pop_address" (fun method =>
      forall (self : Ref.t Pointer.Kind.MutRef Self),
      Run.Trait method [] [ Φ Address.t ] [ φ self ] (option Address.t)
    ).

  Definition Run_exchange (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "exchange" (fun method =>
      forall (self : Ref.t Pointer.Kind.MutRef Self) (n m : Usize.t),
      Run.Trait method [] [] [ φ self; φ n; φ m ] bool
    ).

  Definition Run_dup (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "dup" (fun method =>
      forall (self : Ref.t Pointer.Kind.MutRef Self) (n : Usize.t),
      Run.Trait method [] [] [ φ self; φ n ] bool
    ).

  Class Run (Self : Set) `{Link Self} : Set := {
    len : Run_len Self;
    is_empty : Run_is_empty Self;
    push : Run_push Self;
    push_b256 : Run_push_b256 Self;
    popn : Run_popn Self;
    popn_top : Run_popn_top Self;
    top : Run_top Self;
    pop : Run_pop Self;
    pop_address : Run_pop_address Self;
    exchange : Run_exchange Self;
    dup : Run_dup Self;
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
  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("revm_interpreter::interpreter_types::MemoryTrait", [], [], Φ Self).

  Definition Run_set_data (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "set_data" (fun method =>
      forall
        (self : Ref.t Pointer.Kind.MutRef Self)
        (memory_offset data_offset len : Usize.t)
        (data : Ref.t Pointer.Kind.Ref (list U8.t)),
      Run.Trait method [] [] [ φ self; φ memory_offset; φ data_offset; φ len; φ data ] unit
    ).

  Definition Run_set (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "set" (fun method =>
      forall
        (self : Ref.t Pointer.Kind.MutRef Self)
        (memory_offset : Usize.t)
        (data : Ref.t Pointer.Kind.Ref (list U8.t)),
      Run.Trait method [] [] [ φ self; φ memory_offset; φ data ] unit
    ).

  Definition Run_size (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "size" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] Usize.t
    ).

  Definition Run_copy (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "copy" (fun method =>
      forall
        (self : Ref.t Pointer.Kind.MutRef Self)
        (destination source len : Usize.t),
      Run.Trait method [] [] [ φ self; φ destination; φ source; φ len ] unit
    ).

  Definition Run_slice (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "slice" (fun method =>
      forall
        (Output : Set) `(Link Output)
        (run_Deref_for_Output : deref.Deref.Run Output (list U8.t))
        (self : Ref.t Pointer.Kind.Ref Self)
        (range : Ref.t Pointer.Kind.Ref (range.Range.t Usize.t)),
      Run.Trait method [] [ Φ Output ] [ φ self; φ range ] Output
    ).

  Definition Run_slice_len (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "slice_len" (fun method =>
      forall
        (Output : Set) `(Link Output)
        (run_Deref_for_Output : deref.Deref.Run Output (list U8.t))
        (self : Ref.t Pointer.Kind.Ref Self)
        (offset len : Usize.t),
      Run.Trait method [] [ Φ Output ] [ φ self; φ offset; φ len ] Output
    ).

  Definition Run_resize (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "resize" (fun method =>
      forall (self : Ref.t Pointer.Kind.MutRef Self) (new_size : Usize.t),
      Run.Trait method [] [] [ φ self; φ new_size ] bool
    ).

  Class Run (Self : Set) `{Link Self} : Set := {
    set_data : Run_set_data Self;
    set : Run_set Self;
    size : Run_size Self;
    copy : Run_copy Self;
    slice : Run_slice Self;
    slice_len : Run_slice_len Self;
    resize : Run_resize Self;
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
  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("revm_interpreter::interpreter_types::Jumps", [], [], Φ Self).

  Definition Run_relative_jump (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "relative_jump" (fun method =>
      forall (self : Ref.t Pointer.Kind.MutRef Self) (offset : Isize.t),
      Run.Trait method [] [] [ φ self; φ offset ] unit
    ).

  Definition Run_absolute_jump (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "absolute_jump" (fun method =>
      forall (self : Ref.t Pointer.Kind.MutRef Self) (offset : Usize.t),
      Run.Trait method [] [] [ φ self; φ offset ] unit
    ).

  Definition Run_is_valid_legacy_jump (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "is_valid_legacy_jump" (fun method =>
      forall (self : Ref.t Pointer.Kind.MutRef Self) (offset : Usize.t),
      Run.Trait method [] [] [ φ self; φ offset ] bool
    ).

  Definition Run_pc (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "pc" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] Usize.t
    ).

  Definition Run_opcode (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "opcode" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] U8.t
    ).

  Class Run (Self : Set) `{Link Self} : Set := {
    relative_jump : Run_relative_jump Self;
    absolute_jump : Run_absolute_jump Self;
    is_valid_legacy_jump : Run_is_valid_legacy_jump Self;
    pc : Run_pc Self;
    opcode : Run_opcode Self;
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
  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("revm_interpreter::interpreter_types::Immediates", [], [], Φ Self).

  Definition Run_read_i16 (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "read_i16" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] I16.t
    ).

  Definition Run_read_u16 (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "read_u16" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] U16.t
    ).

  Definition Run_read_i8 (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "read_i8" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] I8.t
    ).

  Definition Run_read_u8 (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "read_u8" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] U8.t
    ).

  Definition Run_read_offset_i16 (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "read_offset_i16" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self) (offset : Isize.t),
      Run.Trait method [] [] [ φ self; φ offset ] I16.t
    ).

  Definition Run_read_offset_u16 (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "read_offset_u16" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self) (offset : Isize.t),
      Run.Trait method [] [] [ φ self; φ offset ] U16.t
    ).

  Definition Run_read_slice (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "read_slice" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self) (len : Usize.t),
      Run.Trait method [] [] [ φ self; φ len ] (Ref.t Pointer.Kind.Ref (list U8.t))
    ).

  Class Run (Self : Set) `{Link Self} : Set := {
    read_i16 : Run_read_i16 Self;
    read_u16 : Run_read_u16 Self;
    read_i8 : Run_read_i8 Self;
    read_u8 : Run_read_u8 Self;
    read_offset_i16 : Run_read_offset_i16 Self;
    read_offset_u16 : Run_read_offset_u16 Self;
    read_slice : Run_read_slice Self;
  }.
End Immediates.

(*
pub trait LegacyBytecode {
    fn bytecode_len(&self) -> usize;
    fn bytecode_slice(&self) -> &[u8];
}
*)
Module LegacyBytecode.
  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("revm_interpreter::interpreter_types::LegacyBytecode", [], [], Φ Self).

  Definition Run_bytecode_len (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "bytecode_len" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] Usize.t
    ).

  Definition Run_bytecode_slice (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "bytecode_slice" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] (Ref.t Pointer.Kind.Ref (list U8.t))
    ).

  Class Run (Self : Set) `{Link Self} : Set := {
    bytecode_len : Run_bytecode_len Self;
    bytecode_slice : Run_bytecode_slice Self;
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
  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("revm_interpreter::interpreter_types::EofData", [], [], Φ Self).

  Definition Run_data (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "data" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] (Ref.t Pointer.Kind.Ref (list U8.t))
    ).

  Definition Run_data_slice (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "data_slice" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self) (offset len : Usize.t),
      Run.Trait method [] [] [ φ self; φ offset; φ len ] (Ref.t Pointer.Kind.Ref (list U8.t))
    ).

  Definition Run_data_size (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "data_size" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] Usize.t
    ).

  Class Run (Self : Set) `{Link Self} : Set := {
    data : Run_data Self;
    data_slice : Run_data_slice Self;
    data_size : Run_data_size Self;
  }.
End EofData.

(*
pub trait EofContainer {
    fn eof_container(&self, index: usize) -> Option<&Bytes>;
}
*)
Module EofContainer.
  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("revm_interpreter::interpreter_types::EofContainer", [], [], Φ Self).

  Definition Run_eof_container (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "eof_container" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self) (index : Usize.t),
      Run.Trait method [] [] [ φ self; φ index ] (option (Ref.t Pointer.Kind.Ref Bytes.t))
    ).

  Class Run (Self : Set) `{Link Self} : Set := {
    eof_container : Run_eof_container Self;
  }.
End EofContainer.

(*
pub trait EofCodeInfo {
    fn code_section_info(&self, idx: usize) -> Option<&TypesSection>;
    fn code_section_pc(&self, idx: usize) -> Option<usize>;
}
*)
Module EofCodeInfo.
  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("revm_interpreter::interpreter_types::EofCodeInfo", [], [], Φ Self).

  Definition Run_code_section_info (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "code_section_info" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self) (idx : Usize.t),
      Run.Trait method [] [] [ φ self; φ idx ] (option (Ref.t Pointer.Kind.Ref TypesSection.t))
    ).

  Definition Run_code_section_pc (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "code_section_pc" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self) (idx : Usize.t),
      Run.Trait method [] [] [ φ self; φ idx ] (option Usize.t)
    ).

  Class Run (Self : Set) `{Link Self} : Set := {
    code_section_info : Run_code_section_info Self;
    code_section_pc : Run_code_section_pc Self;
  }.
End EofCodeInfo.

(*
pub trait ReturnData {
    fn buffer(&self) -> &[u8];
    fn buffer_mut(&mut self) -> &mut Bytes;
}
*)
Module ReturnData.
  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("revm_interpreter::interpreter_types::ReturnData", [], [], Φ Self).

  Definition Run_buffer (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "buffer" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] (Ref.t Pointer.Kind.Ref (list U8.t))
    ).

  Definition Run_buffer_mut (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "buffer_mut" (fun method =>
      forall (self : Ref.t Pointer.Kind.MutRef Self),
      Run.Trait method [] [] [ φ self ] (Ref.t Pointer.Kind.MutRef Bytes.t)
    ).

  Class Run (Self : Set) `{Link Self} : Set := {
    buffer : Run_buffer Self;
    buffer_mut : Run_buffer_mut Self;
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
  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("revm_interpreter::interpreter_types::InputsTrait", [], [], Φ Self).

  Definition Run_target_address (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "target_address" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] Address.t
    ).

  Definition Run_caller_address (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "caller_address" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] Address.t
    ).

  Definition Run_input (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "input" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] (Ref.t Pointer.Kind.Ref (list U8.t))
    ).

  Definition Run_call_value (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "call_value" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] aliases.U256.t
    ).

  Class Run (Self : Set) `{Link Self} : Set := {
    target_address : Run_target_address Self;
    caller_address : Run_caller_address Self;
    input : Run_input Self;
    call_value : Run_call_value Self;
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
  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("revm_interpreter::interpreter_types::SubRoutineStack", [], [], Φ Self).

  Definition Run_len (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "len" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] Usize.t
    ).

  Definition Run_is_empty (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "is_empty" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] bool
    ).

  Definition Run_routine_idx (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "routine_idx" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] Usize.t
    ).

  Definition Run_set_routine_idx (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "set_routine_idx" (fun method =>
      forall (self : Ref.t Pointer.Kind.MutRef Self) (idx : Usize.t),
      Run.Trait method [] [] [ φ self; φ idx ] unit
    ).

  Definition Run_push (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "push" (fun method =>
      forall (self : Ref.t Pointer.Kind.MutRef Self) (old_program_counter new_idx : Usize.t),
      Run.Trait method [] [] [ φ self; φ old_program_counter; φ new_idx ] bool
    ).

  Definition Run_pop (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "pop" (fun method =>
      forall (self : Ref.t Pointer.Kind.MutRef Self),
      Run.Trait method [] [] [ φ self ] (option Usize.t)
    ).

  Class Run (Self : Set) `{Link Self} : Set := {
    len : Run_len Self;
    is_empty : Run_is_empty Self;
    routine_idx : Run_routine_idx Self;
    set_routine_idx : Run_set_routine_idx Self;
    push : Run_push Self;
    pop : Run_pop Self;
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
  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("revm_interpreter::interpreter_types::LoopControl", [], [], Φ Self).

  Definition Run_set_instruction_result (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "set_instruction_result" (fun method =>
      forall (self : Ref.t Pointer.Kind.MutRef Self) (result : InstructionResult.t),
      Run.Trait method [] [] [ φ self; φ result ] unit
    ).

  Definition Run_set_next_action (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "set_next_action" (fun method =>
      forall
        (self : Ref.t Pointer.Kind.MutRef Self)
        (action : InterpreterAction.t)
        (result : InstructionResult.t),
      Run.Trait method [] [] [ φ self; φ action; φ result ] unit
    ).

  Definition Run_gas (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "gas" (fun method =>
      forall (self : Ref.t Pointer.Kind.MutRef Self),
      Run.Trait method [] [] [ φ self ] (Ref.t Pointer.Kind.MutRef Gas.t)
    ).

  Definition Run_instruction_result (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "instruction_result" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] InstructionResult.t
    ).

  Definition Run_take_next_action (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "take_next_action" (fun method =>
      forall (self : Ref.t Pointer.Kind.MutRef Self),
      Run.Trait method [] [] [ φ self ] InterpreterAction.t
    ).

  Class Run (Self : Set) `{Link Self} : Set := {
    set_instruction_result : Run_set_instruction_result Self;
    set_next_action : Run_set_next_action Self;
    gas : Run_gas Self;
    instruction_result : Run_instruction_result Self;
    take_next_action : Run_take_next_action Self;
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
  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("revm_interpreter::interpreter_types::RuntimeFlag", [], [], Φ Self).

  Definition Run_is_static (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "is_static" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] bool
    ).

  Definition Run_is_eof (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "is_eof" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] bool
    ).

  Definition Run_is_eof_init (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "is_eof_init" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] bool
    ).

  Definition Run_spec_id (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "spec_id" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] SpecId.t
    ).

  Class Run (Self : Set) `{Link Self} : Set := {
    is_static : Run_is_static Self;
    is_eof : Run_is_eof Self;
    is_eof_init : Run_is_eof_init Self;
    spec_id : Run_spec_id Self;
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

  Class Run
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
