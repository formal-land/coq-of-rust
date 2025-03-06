Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require alloc.links.alloc.
Require Import revm.links.dependencies.
Require Import revm.revm_bytecode.eof.links.body_EofBody.
Require revm.revm_bytecode.eof.links.header.

Module Eof.
  Record t : Set := {
    header: revm_bytecode.eof.links.header.EofHeader.t;
    body: EofBody.t;
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
