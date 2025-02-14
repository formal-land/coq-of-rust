Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require alloc.links.alloc.
Require alloc.links.vec.
Require Import revm.links.dependencies.
Require revm.revm_bytecode.eof.links.types_section.

Module EofBody.
  Record t : Set := {
    types_section: alloc.links.vec.Vec.t revm_bytecode.eof.links.types_section.TypesSection.t alloc.links.alloc.Global.t;
    code_section: alloc.links.vec.Vec.t Usize.t alloc.links.alloc.Global.t;
    code: alloy_primitives.links.bytes_.Bytes.t;
    container_section: alloc.links.vec.Vec.t alloy_primitives.links.bytes_.Bytes.t alloc.links.alloc.Global.t;
    data_section: alloy_primitives.links.bytes_.Bytes.t;
    is_data_filled: bool;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_bytecode::eof::body::EofBody";
    φ '(Build_t types_section code_section code container_section data_section is_data_filled) :=
      Value.StructRecord "revm_bytecode::eof::body::EofBody" [
        ("types_section", φ types_section);
        ("code_section", φ code_section);
        ("code", φ code);
        ("container_section", φ container_section);
        ("data_section", φ data_section);
        ("is_data_filled", φ is_data_filled)
      ]
  }.
End EofBody.
