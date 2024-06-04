Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import CoqOfRust.core.simulations.array.

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
    types_size : Z;
    code_sizes : list Z;
    container_sizes : list Z;
    data_size : Z;
    sum_code_sizes : Z;
    sum_container_sizes : Z;
  }.

  Global Instance IsToTy : ToTy t := {
    Φ := Ty.path "revm_primitives::bytecode::eof::header::EofHeader";
  }.

  Global Instance IsToValue : ToValue t := {
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
