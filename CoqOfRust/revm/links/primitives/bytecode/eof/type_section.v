Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.


(*
  /// Types section that contains stack information for matching code section.
  #[derive(Debug, Clone, Default, Hash, PartialEq, Eq, Copy)]
  #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
  pub struct TypesSection {
      /// inputs - 1 byte - `0x00-0x7F`
      /// number of stack elements the code section consumes
      pub inputs: u8,
      /// outputs - 1 byte - `0x00-0x80`
      /// number of stack elements the code section returns or 0x80 for non-returning functions
      pub outputs: u8,
      /// max_stack_height - 2 bytes - `0x0000-0x03FF`
      /// maximum number of elements ever placed onto the stack by the code section
      pub max_stack_size: u16,
  }
*)

Module TypesSection.
  Record t : Set := {
    inputs : Z;
    outputs : Z;
    max_stack_size : Z;
  }.

  Global Instance IsLink : Link t := {
    to_ty := Ty.path "revm_primitives::bytecode::eof::types_section::TypesSection";
    to_value x :=
      Value.StructRecord "revm_primitives::bytecode::eof::types_section::TypesSection" [
        ("inputs", to_value x.(inputs));
        ("outputs", to_value x.(outputs));
        ("max_stack_size", to_value x.(max_stack_size))
      ];
  }.

  Global Instance IsToValue : ToValue t := {
    φ x :=
      Value.StructRecord "revm_primitives::bytecode::eof::types_section::TypesSection" [
        ("inputs", φ x.(inputs));
        ("outputs", φ x.(outputs));
        ("max_stack_size", φ x.(max_stack_size))
      ];
  }.
End TypesSection.
