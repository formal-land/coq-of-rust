Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require core.links.array.
Require core.ops.links.deref.
Require core.ops.links.range.
Require Import core.links.option.
Require revm.revm_bytecode.eof.links.types_section.
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
  Definition Run_len (Self : Set) `{Link Self} : Set :=
    {len @
      IsTraitMethod.t "revm_interpreter::interpreter_types::StackTrait" [] [] (Φ Self) "len" len *
      forall (self : Ref.t Pointer.Kind.Ref Self),
        {{ len [] [] [ φ self ] 🔽 Usize.t }}
    }.

  Definition Run_is_empty (Self : Set) `{Link Self} : Set :=
    {is_empty @
      IsTraitMethod.t "revm_interpreter::interpreter_types::StackTrait" [] [] (Φ Self) "is_empty" is_empty *
      forall (self : Ref.t Pointer.Kind.Ref Self),
        {{ is_empty [] [] [ φ self ] 🔽 bool }}
    }.

  Definition Run_push (Self : Set) `{Link Self} : Set :=
    {push @
      IsTraitMethod.t "revm_interpreter::interpreter_types::StackTrait" [] [] (Φ Self) "push" push *
      forall (self : Ref.t Pointer.Kind.MutRef Self) (value : U256.t),
        {{ push [] [] [ φ self; φ value ] 🔽 bool }}
    }.

  Definition Run_push_b256 (Self : Set) `{Link Self} : Set :=
    {push_b256 @
      IsTraitMethod.t "revm_interpreter::interpreter_types::StackTrait" [] [] (Φ Self) "push_b256" push_b256 *
      forall (self : Ref.t Pointer.Kind.MutRef Self) (value : B256.t),
        {{ push_b256 [] [] [ φ self; φ value ] 🔽 bool }}
    }.

  Definition Run_popn (Self : Set) `{Link Self} : Set :=
    {popn @
      IsTraitMethod.t "revm_interpreter::interpreter_types::StackTrait" [] [] (Φ Self) "popn" popn *
      forall (N : Usize.t) (self : Ref.t Pointer.Kind.MutRef Self),
        {{ popn [ φ N ] [] [ φ self ] 🔽 option (array.t U256.t N) }}
    }.

  Definition Run_popn_top (Self : Set) `{Link Self} : Set :=
    {popn_top @
      IsTraitMethod.t "revm_interpreter::interpreter_types::StackTrait" [] [] (Φ Self) "popn_top" popn_top *
      forall (POPN : Usize.t) (self : Ref.t Pointer.Kind.MutRef Self),
        {{ popn_top [ φ POPN ] [] [ φ self ] 🔽 option (array.t U256.t POPN * Ref.t Pointer.Kind.MutRef U256.t) }}
    }.

  Definition Run_top (Self : Set) `{Link Self} : Set :=
    {top @
      IsTraitMethod.t "revm_interpreter::interpreter_types::StackTrait" [] [] (Φ Self) "top" top *
      forall (self : Ref.t Pointer.Kind.MutRef Self),
        {{ top [] [] [ φ self ] 🔽 option (Ref.t Pointer.Kind.MutRef U256.t) }}
    }.

  Definition Run_pop (Self : Set) `{Link Self} : Set :=
    {pop @
      IsTraitMethod.t "revm_interpreter::interpreter_types::StackTrait" [] [] (Φ Self) "pop" pop *
      forall (self : Ref.t Pointer.Kind.MutRef Self),
        {{ pop [] [] [ φ self ] 🔽 option U256.t }}
    }.

  Definition Run_pop_address (Self : Set) `{Link Self} : Set :=
    {pop_address @
      IsTraitMethod.t "revm_interpreter::interpreter_types::StackTrait" [] [] (Φ Self) "pop_address" pop_address *
      forall (self : Ref.t Pointer.Kind.MutRef Self),
        {{ pop_address [] [] [ φ self ] 🔽 option alloy_primitives.bits.links.address.Address.t }}
    }.

  Definition Run_exchange (Self : Set) `{Link Self} : Set :=
    {exchange @
      IsTraitMethod.t "revm_interpreter::interpreter_types::StackTrait" [] [] (Φ Self) "exchange" exchange *
      forall (self : Ref.t Pointer.Kind.MutRef Self) (n m : Usize.t),
        {{ exchange [] [] [ φ self; φ n; φ m ] 🔽 bool }}
    }.

  Definition Run_dup (Self : Set) `{Link Self} : Set :=
    {dup @
      IsTraitMethod.t "revm_interpreter::interpreter_types::StackTrait" [] [] (Φ Self) "dup" dup *
      forall (self : Ref.t Pointer.Kind.MutRef Self) (n : Usize.t),
        {{ dup [] [] [ φ self; φ n ] 🔽 bool }}
    }.

  Record Run (Self : Set) `{Link Self} : Set := {
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
  Definition Run_set_data (Self : Set) `{Link Self} : Set :=
    {set_data @
      IsTraitMethod.t "revm_interpreter::interpreter_types::MemoryTrait" [] [] (Φ Self) "set_data" set_data *
      forall
        (self : Ref.t Pointer.Kind.MutRef Self)
        (memory_offset data_offset len : Usize.t)
        (data : Ref.t Pointer.Kind.Ref (list U8.t)),
      {{ set_data [] [] [ φ self; φ memory_offset; φ data_offset; φ len; φ data ] 🔽 unit }}
    }.

  Definition Run_set (Self : Set) `{Link Self} : Set :=
    {set @
      IsTraitMethod.t "revm_interpreter::interpreter_types::MemoryTrait" [] [] (Φ Self) "set" set *
      forall
        (self : Ref.t Pointer.Kind.MutRef Self)
        (memory_offset : Usize.t)
        (data : Ref.t Pointer.Kind.Ref (list U8.t)),
      {{ set [] [] [ φ self; φ memory_offset; φ data ] 🔽 unit }}
    }.

  Definition Run_size (Self : Set) `{Link Self} : Set :=
    {size @
      IsTraitMethod.t "revm_interpreter::interpreter_types::MemoryTrait" [] [] (Φ Self) "size" size *
      forall (self : Ref.t Pointer.Kind.Ref Self),
        {{ size [] [] [ φ self ] 🔽 Usize.t }}
    }.

  Definition Run_copy (Self : Set) `{Link Self} : Set :=
    {copy @
      IsTraitMethod.t "revm_interpreter::interpreter_types::MemoryTrait" [] [] (Φ Self) "copy" copy *
      forall
        (self : Ref.t Pointer.Kind.MutRef Self)
        (destination source len : Usize.t),
      {{ copy [] [] [ φ self; φ destination; φ source; φ len ] 🔽 unit }}
    }.

  Definition Run_slice (Self : Set) `{Link Self} : Set :=
    {slice @
      IsTraitMethod.t "revm_interpreter::interpreter_types::MemoryTrait" [] [] (Φ Self) "slice" slice *
      forall
        (Output : Set) `(Link Output)
        (run_Deref_for_Output : deref.Deref.Run Output (Target := list U8.t))
        (self : Ref.t Pointer.Kind.Ref Self)
        (range : Ref.t Pointer.Kind.Ref (range.Range.t Usize.t)),
      {{ slice [] [] [ φ self; φ range ] 🔽 Output }}
    }.

  Definition Run_slice_len (Self : Set) `{Link Self} : Set :=
    {slice_len @
      IsTraitMethod.t "revm_interpreter::interpreter_types::MemoryTrait" [] [] (Φ Self) "slice_len" slice_len *
      forall
        (Output : Set) `(Link Output)
        (run_Deref_for_Output : deref.Deref.Run Output (Target := list U8.t))
        (self : Ref.t Pointer.Kind.Ref Self)
        (offset len : Usize.t),
      {{ slice_len [] [] [ φ self; φ offset; φ len ] 🔽 Output }}
    }.

  Definition Run_resize (Self : Set) `{Link Self} : Set :=
    {resize @
      IsTraitMethod.t "revm_interpreter::interpreter_types::MemoryTrait" [] [] (Φ Self) "resize" resize *
      forall (self : Ref.t Pointer.Kind.MutRef Self) (new_size : Usize.t),
        {{ resize [] [] [ φ self; φ new_size ] 🔽 bool }}
    }.

  Record Run (Self : Set) `{Link Self} : Set := {
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
  Definition Run_relative_jump (Self : Set) `{Link Self} : Set :=
    {relative_jump @
      IsTraitMethod.t "revm_interpreter::interpreter_types::Jumps" [] [] (Φ Self) "relative_jump" relative_jump *
      forall (self : Ref.t Pointer.Kind.MutRef Self) (offset : Isize.t),
        {{ relative_jump [] [] [ φ self; φ offset ] 🔽 unit }}
    }.

  Definition Run_absolute_jump (Self : Set) `{Link Self} : Set :=
    {absolute_jump @
      IsTraitMethod.t "revm_interpreter::interpreter_types::Jumps" [] [] (Φ Self) "absolute_jump" absolute_jump *
      forall (self : Ref.t Pointer.Kind.MutRef Self) (offset : Usize.t),
        {{ absolute_jump [] [] [ φ self; φ offset ] 🔽 unit }}
    }.

  Definition Run_is_valid_legacy_jump (Self : Set) `{Link Self} : Set :=
    {is_valid_legacy_jump @
      IsTraitMethod.t "revm_interpreter::interpreter_types::Jumps" [] [] (Φ Self) "is_valid_legacy_jump" is_valid_legacy_jump *
      forall (self : Ref.t Pointer.Kind.MutRef Self) (offset : Usize.t),
        {{ is_valid_legacy_jump [] [] [ φ self; φ offset ] 🔽 bool }}
    }.

  Definition Run_pc (Self : Set) `{Link Self} : Set :=
    {pc @
      IsTraitMethod.t "revm_interpreter::interpreter_types::Jumps" [] [] (Φ Self) "pc" pc *
      forall (self : Ref.t Pointer.Kind.Ref Self),
        {{ pc [] [] [ φ self ] 🔽 Usize.t }}
    }.

  Definition Run_opcode (Self : Set) `{Link Self} : Set :=
    {opcode @
      IsTraitMethod.t "revm_interpreter::interpreter_types::Jumps" [] [] (Φ Self) "opcode" opcode *
      forall (self : Ref.t Pointer.Kind.Ref Self),
        {{ opcode [] [] [ φ self ] 🔽 U8.t }}
    }.

  Record Run (Self : Set) `{Link Self} : Set := {
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
  Definition Run_read_i16 (Self : Set) `{Link Self} : Set :=
    {read_i16 @
      IsTraitMethod.t "revm_interpreter::interpreter_types::Immediates" [] [] (Φ Self) "read_i16" read_i16 *
      forall (self : Ref.t Pointer.Kind.Ref Self),
        {{ read_i16 [] [] [ φ self ] 🔽 I16.t }}
    }.

  Definition Run_read_u16 (Self : Set) `{Link Self} : Set :=
    {read_u16 @
      IsTraitMethod.t "revm_interpreter::interpreter_types::Immediates" [] [] (Φ Self) "read_u16" read_u16 *
      forall (self : Ref.t Pointer.Kind.Ref Self),
        {{ read_u16 [] [] [ φ self ] 🔽 U16.t }}
    }.

  Definition Run_read_i8 (Self : Set) `{Link Self} : Set :=
    {read_i8 @
      IsTraitMethod.t "revm_interpreter::interpreter_types::Immediates" [] [] (Φ Self) "read_i8" read_i8 *
      forall (self : Ref.t Pointer.Kind.Ref Self),
        {{ read_i8 [] [] [ φ self ] 🔽 I8.t }}
    }.

  Definition Run_read_u8 (Self : Set) `{Link Self} : Set :=
    {read_u8 @
      IsTraitMethod.t "revm_interpreter::interpreter_types::Immediates" [] [] (Φ Self) "read_u8" read_u8 *
      forall (self : Ref.t Pointer.Kind.Ref Self),
        {{ read_u8 [] [] [ φ self ] 🔽 U8.t }}
    }.

  Definition Run_read_offset_i16 (Self : Set) `{Link Self} : Set :=
    {read_offset_i16 @
      IsTraitMethod.t "revm_interpreter::interpreter_types::Immediates" [] [] (Φ Self) "read_offset_i16" read_offset_i16 *
      forall (self : Ref.t Pointer.Kind.Ref Self) (offset : Isize.t),
        {{ read_offset_i16 [] [] [ φ self; φ offset ] 🔽 I16.t }}
    }.

  Definition Run_read_offset_u16 (Self : Set) `{Link Self} : Set :=
    {read_offset_u16 @
      IsTraitMethod.t "revm_interpreter::interpreter_types::Immediates" [] [] (Φ Self) "read_offset_u16" read_offset_u16 *
      forall (self : Ref.t Pointer.Kind.Ref Self) (offset : Isize.t),
        {{ read_offset_u16 [] [] [ φ self; φ offset ] 🔽 U16.t }}
    }.

  Definition Run_read_slice (Self : Set) `{Link Self} : Set :=
    {read_slice @
      IsTraitMethod.t "revm_interpreter::interpreter_types::Immediates" [] [] (Φ Self) "read_slice" read_slice *
      forall (self : Ref.t Pointer.Kind.Ref Self) (len : Usize.t),
        {{ read_slice [] [] [ φ self; φ len ] 🔽 Ref.t Pointer.Kind.Ref (list U8.t) }}
    }.

  Record Run (Self : Set) `{Link Self} : Set := {
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
  Definition Run_bytecode_len (Self : Set) `{Link Self} : Set :=
    {bytecode_len @
      IsTraitMethod.t "revm_interpreter::interpreter_types::LegacyBytecode" [] [] (Φ Self) "bytecode_len" bytecode_len *
      forall (self : Ref.t Pointer.Kind.Ref Self),
        {{ bytecode_len [] [] [ φ self ] 🔽 Usize.t }}
    }.

  Definition Run_bytecode_slice (Self : Set) `{Link Self} : Set :=
    {bytecode_slice @
      IsTraitMethod.t "revm_interpreter::interpreter_types::LegacyBytecode" [] [] (Φ Self) "bytecode_slice" bytecode_slice *
      forall (self : Ref.t Pointer.Kind.Ref Self),
        {{ bytecode_slice [] [] [ φ self ] 🔽 Ref.t Pointer.Kind.Ref (list U8.t) }}
    }.

  Record Run (Self : Set) `{Link Self} : Set := {
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
  Definition Run_data (Self : Set) `{Link Self} : Set :=
    {data @
      IsTraitMethod.t "revm_interpreter::interpreter_types::EofData" [] [] (Φ Self) "data" data *
      forall (self : Ref.t Pointer.Kind.Ref Self),
        {{ data [] [] [ φ self ] 🔽 Ref.t Pointer.Kind.Ref (list U8.t) }}
    }.

  Definition Run_data_slice (Self : Set) `{Link Self} : Set :=
    {data_slice @
      IsTraitMethod.t "revm_interpreter::interpreter_types::EofData" [] [] (Φ Self) "data_slice" data_slice *
      forall (self : Ref.t Pointer.Kind.Ref Self) (offset len : Usize.t),
        {{ data_slice [] [] [ φ self; φ offset; φ len ] 🔽 Ref.t Pointer.Kind.Ref (list U8.t) }}
    }.

  Definition Run_data_size (Self : Set) `{Link Self} : Set :=
    {data_size @
      IsTraitMethod.t "revm_interpreter::interpreter_types::EofData" [] [] (Φ Self) "data_size" data_size *
      forall (self : Ref.t Pointer.Kind.Ref Self),
        {{ data_size [] [] [ φ self ] 🔽 Usize.t }}
    }.

  Record Run (Self : Set) `{Link Self} : Set := {
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
  Definition Run_eof_container (Self : Set) `{Link Self} : Set :=
    {eof_container @
      IsTraitMethod.t "revm_interpreter::interpreter_types::EofContainer" [] [] (Φ Self) "eof_container" eof_container *
      forall (self : Ref.t Pointer.Kind.Ref Self) (index : Usize.t),
      {{
        eof_container [] [] [ φ self; φ index ] 🔽
        option (Ref.t Pointer.Kind.Ref alloy_primitives.links.bytes_.Bytes.t)
      }}
    }.

  Record Run (Self : Set) `{Link Self} : Set := {
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
  Definition Run_code_section_info (Self : Set) `{Link Self} : Set :=
    {code_section_info @
      IsTraitMethod.t "revm_interpreter::interpreter_types::EofCodeInfo" [] [] (Φ Self) "code_section_info" code_section_info *
      forall (self : Ref.t Pointer.Kind.Ref Self) (idx : Usize.t),
      {{
        code_section_info [] [] [ φ self; φ idx ] 🔽
        option (Ref.t Pointer.Kind.Ref types_section.TypesSection.t)
      }}
    }.

  Definition Run_code_section_pc (Self : Set) `{Link Self} : Set :=
    {code_section_pc @
      IsTraitMethod.t "revm_interpreter::interpreter_types::EofCodeInfo" [] [] (Φ Self) "code_section_pc" code_section_pc *
      forall (self : Ref.t Pointer.Kind.Ref Self) (idx : Usize.t),
      {{ code_section_pc [] [] [ φ self; φ idx ] 🔽 option Usize.t }}
    }.

  Record Run (Self : Set) `{Link Self} : Set := {
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
  Definition Run_buffer (Self : Set) `{Link Self} : Set :=
    {buffer @
      IsTraitMethod.t "revm_interpreter::interpreter_types::ReturnData" [] [] (Φ Self) "buffer" buffer *
      forall (self : Ref.t Pointer.Kind.Ref Self),
        {{ buffer [] [] [ φ self ] 🔽 Ref.t Pointer.Kind.Ref (list U8.t) }}
    }.

  Definition Run_buffer_mut (Self : Set) `{Link Self} : Set :=
    {buffer_mut @
      IsTraitMethod.t "revm_interpreter::interpreter_types::ReturnData" [] [] (Φ Self) "buffer_mut" buffer_mut *
      forall (self : Ref.t Pointer.Kind.MutRef Self),
        {{ buffer_mut [] [] [ φ self ] 🔽 Ref.t Pointer.Kind.MutRef alloy_primitives.links.bytes_.Bytes.t }}
    }.

  Record Run (Self : Set) `{Link Self} : Set := {
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
  Definition Run_target_address (Self : Set) `{Link Self} : Set :=
    {target_address @
      IsTraitMethod.t "revm_interpreter::interpreter_types::InputsTrait" [] [] (Φ Self) "target_address" target_address *
      forall (self : Ref.t Pointer.Kind.Ref Self),
        {{ target_address [] [] [ φ self ] 🔽 alloy_primitives.bits.links.address.Address.t }}
    }.

  Definition Run_caller_address (Self : Set) `{Link Self} : Set :=
    {caller_address @
      IsTraitMethod.t "revm_interpreter::interpreter_types::InputsTrait" [] [] (Φ Self) "caller_address" caller_address *
      forall (self : Ref.t Pointer.Kind.Ref Self),
        {{ caller_address [] [] [ φ self ] 🔽 alloy_primitives.bits.links.address.Address.t }}
    }.

  Definition Run_input (Self : Set) `{Link Self} : Set :=
    {input @
      IsTraitMethod.t "revm_interpreter::interpreter_types::InputsTrait" [] [] (Φ Self) "input" input *
      forall (self : Ref.t Pointer.Kind.Ref Self),
        {{ input [] [] [ φ self ] 🔽 Ref.t Pointer.Kind.Ref (list U8.t) }}
    }.

  Definition Run_call_value (Self : Set) `{Link Self} : Set :=
    {call_value @
      IsTraitMethod.t "revm_interpreter::interpreter_types::InputsTrait" [] [] (Φ Self) "call_value" call_value *
      forall (self : Ref.t Pointer.Kind.Ref Self),
        {{ call_value [] [] [ φ self ] 🔽 U256.t }}
    }.

  Record Run (Self : Set) `{Link Self} : Set := {
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
  Definition Run_len (Self : Set) `{Link Self} : Set :=
    {len @
      IsTraitMethod.t "revm_interpreter::interpreter_types::SubRoutineStack" [] [] (Φ Self) "len" len *
      forall (self : Ref.t Pointer.Kind.Ref Self),
        {{ len [] [] [ φ self ] 🔽 Usize.t }}
    }.

  Definition Run_is_empty (Self : Set) `{Link Self} : Set :=
    {is_empty @
      IsTraitMethod.t "revm_interpreter::interpreter_types::SubRoutineStack" [] [] (Φ Self) "is_empty" is_empty *
      forall (self : Ref.t Pointer.Kind.Ref Self),
        {{ is_empty [] [] [ φ self ] 🔽 bool }}
    }.

  Definition Run_routine_idx (Self : Set) `{Link Self} : Set :=
    {routine_idx @
      IsTraitMethod.t "revm_interpreter::interpreter_types::SubRoutineStack" [] [] (Φ Self) "routine_idx" routine_idx *
      forall (self : Ref.t Pointer.Kind.Ref Self),
        {{ routine_idx [] [] [ φ self ] 🔽 Usize.t }}
    }.

  Definition Run_set_routine_idx (Self : Set) `{Link Self} : Set :=
    {set_routine_idx @
      IsTraitMethod.t "revm_interpreter::interpreter_types::SubRoutineStack" [] [] (Φ Self) "set_routine_idx" set_routine_idx *
      forall (self : Ref.t Pointer.Kind.MutRef Self) (idx : Usize.t),
        {{ set_routine_idx [] [] [ φ self; φ idx ] 🔽 unit }}
    }.

  Definition Run_push (Self : Set) `{Link Self} : Set :=
    {push @
      IsTraitMethod.t "revm_interpreter::interpreter_types::SubRoutineStack" [] [] (Φ Self) "push" push *
      forall (self : Ref.t Pointer.Kind.MutRef Self) (old_program_counter new_idx : Usize.t),
        {{ push [] [] [ φ self; φ old_program_counter; φ new_idx ] 🔽 bool }}
    }.

  Definition Run_pop (Self : Set) `{Link Self} : Set :=
    {pop @
      IsTraitMethod.t "revm_interpreter::interpreter_types::
      SubRoutineStack" [] [] (Φ Self) "pop" pop *
      forall (self : Ref.t Pointer.Kind.MutRef Self),
        {{ pop [] [] [ φ self ] 🔽 option Usize.t }}
    }.

  Record Run (Self : Set) `{Link Self} : Set := {
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
  Definition Run_set_instruction_result (Self : Set) `{Link Self} : Set :=
    {set_instruction_result @
      IsTraitMethod.t "revm_interpreter::interpreter_types::LoopControl" [] [] (Φ Self) "set_instruction_result" set_instruction_result *
      forall (self : Ref.t Pointer.Kind.MutRef Self) (result : InstructionResult.t),
        {{ set_instruction_result [] [] [ φ self; φ result ] 🔽 unit }}
    }.

  Definition Run_set_next_action (Self : Set) `{Link Self} : Set :=
    {set_next_action @
      IsTraitMethod.t "revm_interpreter::interpreter_types::LoopControl" [] [] (Φ Self) "set_next_action" set_next_action *
      forall (self : Ref.t Pointer.Kind.MutRef Self) (action : InterpreterAction.t) (result : InstructionResult.t),
        {{ set_next_action [] [] [ φ self; φ action; φ result ] 🔽 unit }}
    }.

  Definition Run_gas (Self : Set) `{Link Self} : Set :=
    {gas @
      IsTraitMethod.t "revm_interpreter::interpreter_types::LoopControl" [] [] (Φ Self) "gas" gas *
      forall (self : Ref.t Pointer.Kind.MutRef Self),
        {{ gas [] [] [ φ self ] 🔽 Ref.t Pointer.Kind.MutRef Gas.t }}
    }.

  Definition Run_instruction_result (Self : Set) `{Link Self} : Set :=
    {instruction_result @
      IsTraitMethod.t "revm_interpreter::interpreter_types::LoopControl" [] [] (Φ Self) "instruction_result" instruction_result *
      forall (self : Ref.t Pointer.Kind.Ref Self),
        {{ instruction_result [] [] [ φ self ] 🔽 InstructionResult.t }}
    }.

  Definition Run_take_next_action (Self : Set) `{Link Self} : Set :=
    {take_next_action @
      IsTraitMethod.t "revm_interpreter::interpreter_types::LoopControl" [] [] (Φ Self) "take_next_action" take_next_action *
      forall (self : Ref.t Pointer.Kind.MutRef Self),
        {{ take_next_action [] [] [ φ self ] 🔽 InterpreterAction.t }}
    }.

  Record Run (Self : Set) `{Link Self} : Set := {
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
  Definition Run_is_static (Self : Set) `{Link Self} : Set :=
    {is_static @
      IsTraitMethod.t "revm_interpreter::interpreter_types::RuntimeFlag" [] [] (Φ Self) "is_static" is_static *
      forall (self : Ref.t Pointer.Kind.Ref Self),
        {{ is_static [] [] [ φ self ] 🔽 bool }}
    }.

  Definition Run_is_eof (Self : Set) `{Link Self} : Set :=
    {is_eof @
      IsTraitMethod.t "revm_interpreter::interpreter_types::RuntimeFlag" [] [] (Φ Self) "is_eof" is_eof *
      forall (self : Ref.t Pointer.Kind.Ref Self),
        {{ is_eof [] [] [ φ self ] 🔽 bool }}
    }.

  Definition Run_is_eof_init (Self : Set) `{Link Self} : Set :=
    {is_eof_init @
      IsTraitMethod.t "revm_interpreter::interpreter_types::RuntimeFlag" [] [] (Φ Self) "is_eof_init" is_eof_init *
      forall (self : Ref.t Pointer.Kind.Ref Self),
        {{ is_eof_init [] [] [ φ self ] 🔽 bool }}
    }.

  Definition Run_spec_id (Self : Set) `{Link Self} : Set :=
    {spec_id @
      IsTraitMethod.t "revm_interpreter::interpreter_types::RuntimeFlag" [] [] (Φ Self) "spec_id" spec_id *
      forall (self : Ref.t Pointer.Kind.Ref Self),
        {{ spec_id [] [] [ φ self ] 🔽 SpecId.t }}
    }.

  Record Run (Self : Set) `{Link Self} : Set := {
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
