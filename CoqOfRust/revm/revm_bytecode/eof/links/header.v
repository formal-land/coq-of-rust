Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require alloc.links.alloc.
Require alloc.links.vec.

Module EofHeader.
  Record t : Set := {
    types_size: U16.t;
    code_sizes: alloc.links.vec.Vec.t U16.t alloc.links.alloc.Global.t;
    container_sizes: alloc.links.vec.Vec.t U16.t alloc.links.alloc.Global.t;
    data_size: U16.t;
    sum_code_sizes: Usize.t;
    sum_container_sizes: Usize.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_bytecode::eof::header::EofHeader";
    φ '(Build_t types_size code_sizes container_sizes data_size sum_code_sizes sum_container_sizes) :=
      Value.StructRecord "revm_bytecode::eof::header::EofHeader" [
        ("types_size", φ types_size);
        ("code_sizes", φ code_sizes);
        ("container_sizes", φ container_sizes);
        ("data_size", φ data_size);
        ("sum_code_sizes", φ sum_code_sizes);
        ("sum_container_sizes", φ sum_container_sizes)
      ]
  }.
End EofHeader.
