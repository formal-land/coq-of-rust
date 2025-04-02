Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require alloc.links.alloc.
Require alloc.vec.links.mod.

Module TypesSection.
  Record t : Set := {
    inputs: U8.t;
    outputs: U8.t;
    max_stack_size: U16.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_bytecode::eof::types_section::TypesSection";
    φ '(Build_t inputs outputs max_stack_size) :=
      Value.StructRecord "revm_bytecode::eof::types_section::TypesSection" [
        ("inputs", φ inputs);
        ("outputs", φ outputs);
        ("max_stack_size", φ max_stack_size)
      ]
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_bytecode::eof::types_section::TypesSection").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.
End TypesSection.
