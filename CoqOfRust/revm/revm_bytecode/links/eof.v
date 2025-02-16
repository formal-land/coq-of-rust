Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require alloc.links.alloc.
Require alloc.links.vec.
Require Import revm.links.dependencies.
Require revm.revm_bytecode.eof.links.body.
Require revm.revm_bytecode.eof.links.header.

Module Eof.
  Record t : Set := {
    header: revm_bytecode.eof.links.header.EofHeader.t;
    body: revm_bytecode.eof.links.body.EofBody.t;
    raw: alloy_primitives.links.bytes_.Bytes.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_bytecode::eof::Eof";
    φ '(Build_t header body raw) :=
      Value.StructRecord "revm_bytecode::eof::Eof" [
        ("header", φ header);
        ("body", φ body);
        ("raw", φ raw)
      ]
  }.
End Eof.
