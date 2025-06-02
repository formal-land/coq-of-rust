Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require Import alloc.links.alloc.
Require Import alloc.vec.links.mod.
Require Import alloy_primitives.bytes.links.mod.
Require Import core.links.clone.
Require Import core.links.default.
Require Import core.links.result.
Require Import core.links.option.
Require Export revm.revm_bytecode.eof.links.body_EofBody.
Require Export revm.revm_bytecode.eof.links.header.
Require Import revm.revm_bytecode.eof.links.types_section.
Require Import revm.revm_bytecode.links.eof.
Require Import revm_bytecode.eof.body.
Require Import core.slice.links.mod.

Require Export revm.revm_bytecode.eof.links.body_EofBody.

Module Impl_Clone_for_EofBody.
  Definition run_clone : Clone.Run_clone EofBody.t.
  Proof.
    eexists.
    { eapply IsTraitMethod.Defined.
      { apply body.eof.body.Impl_core_clone_Clone_for_revm_bytecode_eof_body_EofBody.Implements. }
      { reflexivity. }
    }
    { constructor.
      destruct (vec.links.mod.Impl_Clone_for_Vec.run (T := TypesSection.t) (A := Global.t)).
      destruct (vec.links.mod.Impl_Clone_for_Vec.run (T := Usize.t) (A := Global.t)).
      destruct alloy_primitives.bytes.links.mod.Impl_Clone_for_Bytes.run.
      destruct (vec.links.mod.Impl_Clone_for_Vec.run (T := Bytes.t) (A := Global.t)).
      destruct clone.Impl_Clone_for_bool.run.
      run_symbolic.
    }
  Defined.

  Instance run : Clone.Run EofBody.t := {
    Clone.clone := run_clone;
  }.
End Impl_Clone_for_EofBody.
Export Impl_Clone_for_EofBody.

Module Impl_Default_for_EofBody.
  Definition run_default : Default.Run_default EofBody.t.
  Proof.
    eexists.
    { eapply IsTraitMethod.Defined.
      { apply body.eof.body.Impl_core_default_Default_for_revm_bytecode_eof_body_EofBody.Implements. }
      { reflexivity. }
    }
    { constructor.
      destruct (vec.links.mod.Impl_Default_for_Vec.run (T := TypesSection.t) (A := Global.t)).
      destruct (vec.links.mod.Impl_Default_for_Vec.run (T := Usize.t) (A := Global.t)).
      destruct alloy_primitives.bytes.links.mod.Impl_Default_for_Bytes.run.
      destruct (vec.links.mod.Impl_Default_for_Vec.run (T := Bytes.t) (A := Global.t)).
      destruct default.Impl_Default_for_bool.run.
      run_symbolic.
    }
  Defined.

  Instance run : Default.Run EofBody.t := {
    Default.default := run_default;
  }.
End Impl_Default_for_EofBody.
Export Impl_Default_for_EofBody.

Module Impl_EofBody.
  Definition Self : Set := EofBody.t.

  (*
    pub fn code(&self, index: usize) -> Option<Bytes>
  *)
  Instance run_code (self : Ref.t Pointer.Kind.Ref Self) (index : Usize.t) :
    Run.Trait body.eof.body.Impl_revm_bytecode_eof_body_EofBody.code [] [] [φ self; φ index] (option Bytes.t).
  Proof.
    constructor.
    destruct (vec.links.mod.Impl_Index_for_Vec_T_A.run Usize.t Usize.t Global.t Usize.t).
    destruct (vec.links.mod.Impl_Deref_for_Vec.run (T := Usize.t) (A := Global.t)).
    run_symbolic.
  Admitted.

  (*
    pub fn encode(&self, buffer: &mut Vec<u8>)
  *)
  Instance run_encode (self : Ref.t Pointer.Kind.Ref Self) (buffer : Ref.t Pointer.Kind.MutPointer (Vec.t U8.t Global.t)) :
    Run.Trait body.eof.body.Impl_revm_bytecode_eof_body_EofBody.encode [] [] [φ self; φ buffer] unit.
  Proof.
    constructor.
    run_symbolic.
  Admitted.

  (*
    pub fn into_eof(self) -> Eof
  *)
  Instance run_into_eof (self : Self) :
    Run.Trait body.eof.body.Impl_revm_bytecode_eof_body_EofBody.into_eof [] [] [φ self] Eof.t.
  Proof.
    constructor.
    run_symbolic.
  Admitted.

  (*
    pub fn eof_code_section_start(&self, idx: usize) -> Option<usize> 
  *)
  Instance run_eof_code_section_start (self : Ref.t Pointer.Kind.Ref Self) (idx : Usize.t) :
    Run.Trait body.eof.body.Impl_revm_bytecode_eof_body_EofBody.eof_code_section_start [] [] [φ self; φ idx] (option Usize.t).
  Proof.
    constructor.
    destruct (vec.links.mod.Impl_Deref_for_Vec.run (T := Usize.t) (A := Global.t)).
    destruct deref.
    run_symbolic.
  Admitted.

  (*
    pub fn decode(input: &Bytes, header: &EofHeader) -> Result<Self, EofDecodeError>
  *)
  Instance run_decode (input : Ref.t Pointer.Kind.Ref Bytes.t) (header : Ref.t Pointer.Kind.Ref EofHeader.t) :
    Run.Trait body.eof.body.Impl_revm_bytecode_eof_body_EofBody.decode [] [] [φ input; φ header] (Result.t EofBody.t EofDecodeError.t).
  Proof.
    constructor.
    run_symbolic.
  Admitted.
End Impl_EofBody.
