Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require Import alloc.links.alloc.
Require Import alloc.vec.links.mod.
Require Import alloc.vec.links.mod.
Require Import revm_bytecode.eof.header.

Module EofHeader.
  Record t : Set := {
    types_size: U16.t;
    code_sizes: alloc.vec.links.mod.Vec.t U16.t alloc.links.alloc.Global.t;
    container_sizes: alloc.vec.links.mod.Vec.t U16.t alloc.links.alloc.Global.t;
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

  Definition of_ty : OfTy.t (Ty.path "revm_bytecode::eof::header::EofHeader").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.
End EofHeader.

Module Impl_EofHeader.

  Definition Self : Set := EofHeader.t.

  (*
    pub fn encode(&self, buffer: &mut Vec<u8>)
  *)
  Instance run_encode (self : Ref.t Pointer.Kind.Ref Self) (buffer : Ref.t Pointer.Kind.MutPointer (Vec.t U8.t Global.t)) :
    Run.Trait header.eof.header.Impl_revm_bytecode_eof_header_EofHeader.encode [] [] [φ self; φ buffer] unit.
  Admitted.
End Impl_EofHeader.
