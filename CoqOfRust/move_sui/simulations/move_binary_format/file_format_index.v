(** Part of the `file_format` file that is extracted, with only the index, in order to break a
    mutual dependency cycle. *)
Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.
Require core.simulations.assert.
Require core.simulations.slice.

Require Import CoqOfRust.core.simulations.eq.

Require CoqOfRust.move_sui.simulations.move_binary_format.file_format_common.
Require CoqOfRust.move_sui.simulations.move_core_types.vm_status.

(* pub type TableIndex = u16; *)
Module TableIndex.
  Definition t : Set := Z.
End TableIndex.

(* 
NOTE: 
  Structs defined with `define_index` macro are usually represented
  with `Record t : Set := { a0 : Z; }.`. I name like such because 
  they might be necessity to access them and t.(a0)is convinient for
  such functionality. Other structs defined with a `Make` constructor
  might need to change into this style in the future.
*)

(* DRAFT: Template for `define_index!` macro
pub struct $name(pub TableIndex);

/// Returns an instance of the given `Index`.
impl $name {
    pub fn new(idx: TableIndex) -> Self {
        Self(idx)
    }
}

impl ::std::fmt::Display for $name {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl ::std::fmt::Debug for $name {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "{}({})", stringify!($name), self.0)
    }
}

impl ModuleIndex for $name {
    const KIND: IndexKind = IndexKind::$kind;

    #[inline]
    fn into_index(self) -> usize {
        self.0 as usize
    }
}
*)
Module LocalIndex.
  Record t : Set := { a0 : Z; }.
End LocalIndex.

(* pub type TypeParameterIndex = u16; *)
Module TypeParameterIndex.
  Definition t : Set := Z.
End TypeParameterIndex.

(* pub type CodeOffset = u16; *)
Module CodeOffset.
  Definition t : Set := Z.
End CodeOffset.

Module ModuleHandleIndex.
  Record t : Set := { a0 : Z; }.
End ModuleHandleIndex.

Module IdentifierIndex.
  Record t : Set := { a0 : Z; }.
End IdentifierIndex.

Module StructHandleIndex.
  Record t : Set := { a0 : Z; }.
End StructHandleIndex.

Module StructDefinitionIndex.
  Record t : Set := { a0 : Z; }.
End StructDefinitionIndex.

Module FieldHandleIndex.
  Record t : Set := { a0 : Z; }.
End FieldHandleIndex.

Module FunctionDefinitionIndex.
  Record t : Set := { a0 : Z; }.
End FunctionDefinitionIndex.

Module SignatureIndex.
  Record t : Set := { a0 : Z; }.
End SignatureIndex.

Module StructDefInstantiationIndex.
  Record t : Set := { a0 : Z; }.
End StructDefInstantiationIndex.

Module ConstantPoolIndex.
  Record t : Set := { a0 : Z; }.
End ConstantPoolIndex.

Module FunctionHandleIndex.
  Record t : Set := { a0 : Z; }.
End FunctionHandleIndex.

Module FieldInstantiationIndex.
  Record t : Set := { a0 : Z; }.
End FieldInstantiationIndex.

Module FunctionInstantiationIndex.
  Record t : Set := { a0 : Z; }.
End FunctionInstantiationIndex.

(* **************** *)

Module FieldInstantiation.
  Record t : Set := {
    handle : FieldHandleIndex.t;
    type_parameters : SignatureIndex.t;
  }.
End FieldInstantiation.

Module FunctionInstantiation.
  Record t : Set := {
    handle : FunctionHandleIndex.t;
    type_parameters : SignatureIndex.t;
  }.
End FunctionInstantiation.

Module StructDefInstantiation.
  Record t : Set := {
    def : StructDefinitionIndex.t;
    type_parameters : SignatureIndex.t;
  }.
End StructDefInstantiation.
