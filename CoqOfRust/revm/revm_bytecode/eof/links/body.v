Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require Import alloc.links.alloc.
Require Import alloc.vec.links.mod.
Require core.links.clone.
Require core.links.default.
Require Import core.links.option.
Require Import core.slice.links.index.
Require Import core.slice.links.mod.
Require Import revm.links.dependencies.
Require Export revm.revm_bytecode.eof.links.body_EofBody.
Require Export revm.revm_bytecode.eof.links.header.
Require Import revm.revm_bytecode.eof.links.types_section.
Require Import revm.revm_bytecode.links.eof.
Require Import revm_bytecode.eof.body.
Require Import core.slice.links.mod.

Import Run.

Require Export revm.revm_bytecode.eof.links.body_EofBody.

Module Impl_Clone_for_EofBody.
  Definition run_clone : clone.Clone.Run_clone EofBody.t.
  Proof.
    eexists; split.
    { eapply IsTraitMethod.Defined.
      { apply body.eof.body.Impl_core_clone_Clone_for_revm_bytecode_eof_body_EofBody.Implements. }
      { reflexivity. }
    }
    { intros.
      destruct (vec.links.mod.Impl_Clone_for_Vec.run (T := TypesSection.t) (A := Global.t)).
      destruct clone.
      destruct (vec.links.mod.Impl_Clone_for_Vec.run (T := Usize.t) (A := Global.t)).
      destruct clone.
      destruct alloy_primitives.links.bytes_.Impl_Clone_for_Bytes.run.
      destruct clone.
      destruct (vec.links.mod.Impl_Clone_for_Vec.run (T := alloy_primitives.links.bytes_.Bytes.t) (A := Global.t)).
      destruct clone.
      destruct clone.Impl_Clone_for_bool.run.
      destruct clone.
      run_symbolic.
      run_symbolic_closure.
      intros []; run_symbolic.
      run_symbolic_closure.
      intros []; run_symbolic.
      run_symbolic_closure.
      intros []; run_symbolic.
      run_symbolic_closure.
      intros []; run_symbolic.
      run_symbolic_closure.
      intros []; run_symbolic.
      run_symbolic_closure.
      intros []; run_symbolic.
    }
  Defined.

  Definition run : clone.Clone.Run EofBody.t.
  Proof.
    constructor.
    { (* clone *)
      exact run_clone.
    }
  Defined.
End Impl_Clone_for_EofBody.

Module Impl_Default_for_EofBody.
  Definition run_default : default.Default.Run_default EofBody.t.
  Proof.
    eexists; split.
    { eapply IsTraitMethod.Defined.
      { apply body.eof.body.Impl_core_default_Default_for_revm_bytecode_eof_body_EofBody.Implements. }
      { reflexivity. }
    }
    { intros.
      destruct (vec.links.mod.Impl_Default_for_Vec.run (T := TypesSection.t) (A := Global.t)).
      destruct default.
      destruct (vec.links.mod.Impl_Default_for_Vec.run (T := Usize.t) (A := Global.t)).
      destruct default.
      destruct alloy_primitives.links.bytes_.Impl_Default_for_Bytes.run.
      destruct default.
      destruct (vec.links.mod.Impl_Default_for_Vec.run (T := alloy_primitives.links.bytes_.Bytes.t) (A := Global.t)).
      destruct default.
      destruct default.Impl_Default_for_bool.run.
      destruct default.
      run_symbolic. 
    }
  Defined.
End Impl_Default_for_EofBody.

Module Impl_EofBody.
  Import Impl_alloc_vec_Vec_T_A.
  Import Impl_EofHeader.
  Import Impl_Slice.

  Definition Self : Set := EofBody.t.

  (*
    pub fn code(&self, index: usize) -> Option<Bytes>
  *)
  Instance run_code (self : Ref.t Pointer.Kind.Ref Self) (index : Usize.t) :
    Run.Trait body.eof.body.Impl_revm_bytecode_eof_body_EofBody.code [] [] [φ self; φ index] (option alloy_primitives.links.bytes_.Bytes.t).
  Proof.
    constructor.
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
End Impl_EofBody.
