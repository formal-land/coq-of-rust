(* Generated file. Do not edit. *)
Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require alloc.links.alloc.
Require alloc.links.vec.
Require Import revm.links.dependencies.

Module EofHeader.
  Record t : Set := {
    types_size: U16.t;
    code_sizes: alloc.links.vec.Vec.t U16.t alloc.links.alloc.Global.t;
    container_sizes: alloc.links.vec.Vec.t U16.t alloc.links.alloc.Global.t;
    data_size: U16.t;
    sum_code_sizes: Usize.t;
    sum_container_sizes: Usize.t;
  }.

  Definition current_to_value (x: t) : Value.t :=
    match x with
    | Build_t types_size code_sizes container_sizes data_size sum_code_sizes sum_container_sizes =>
      Value.StructRecord "revm_bytecode::eof::header::EofHeader" [
        ("types_size", to_value types_size);
        ("code_sizes", to_value code_sizes);
        ("container_sizes", to_value container_sizes);
        ("data_size", to_value data_size);
        ("sum_code_sizes", to_value sum_code_sizes);
        ("sum_container_sizes", to_value sum_container_sizes)
      ]
    end.

  Global Instance IsLink : Link t := {
    to_ty := Ty.path "revm_bytecode::eof::header::EofHeader";
    to_value := to_value
  }.
End EofHeader.
