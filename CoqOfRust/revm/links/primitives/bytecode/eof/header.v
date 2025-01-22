Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import CoqOfRust.alloc.vec.links.mod.
Require Import CoqOfRust.core.links.array.

(*
  /// EOF Header containing
  #[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
  #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
  pub struct EofHeader {
      /// Size of EOF types section.
      /// types section includes num of input and outputs and max stack size.
      pub types_size: u16,
      /// Sizes of EOF code section.
      /// Code size can't be zero.
      pub code_sizes: Vec<u16>,
      /// EOF Container size.
      /// Container size can be zero.
      pub container_sizes: Vec<u16>,
      /// EOF data size.
      pub data_size: u16,
      /// sum code sizes
      pub sum_code_sizes: usize,
      /// sum container sizes
      pub sum_container_sizes: usize,
  }
*)

Module EofHeader.
  Record t : Set := {
    types_size : U16.t;
    code_sizes : Vec.t U16.t;
    container_sizes : Vec.t U16.t;
    data_size : U16.t;
    sum_code_sizes : Usize.t;
    sum_container_sizes : Usize.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_primitives::bytecode::eof::header::EofHeader";
    φ x :=
      Value.StructRecord "revm_primitives::bytecode::eof::header::EofHeader" [
        ("types_size", φ x.(types_size));
        ("code_sizes", φ x.(code_sizes));
        ("container_sizes", φ x.(container_sizes));
        ("data_size", φ x.(data_size));
        ("sum_code_sizes", φ x.(sum_code_sizes));
        ("sum_container_sizes", φ x.(sum_container_sizes))
      ];
  }.
End EofHeader.
