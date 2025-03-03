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
Require Import revm.revm_bytecode.eof.links.types_section.
Require Import revm_bytecode.eof.body.
Require Import revm_bytecode.links.eof.

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
End Impl_Default_for_EofBody.

Module Impl_EofBody.
  Definition Self : Set := EofBody.t.

  (*
      pub fn code(&self, index: usize) -> Option<Bytes> {
        if index == 0 {
            // There should be at least one code section.
            return Some(self.code.slice(..self.code_section[0]));
        }
        self.code_section
            .get(index)
            .map(|end| self.code.slice(self.code_section[index - 1]..*end))
      }
  *)
  Definition run_code (self : Ref.t Pointer.Kind.Ref Self) (index : Usize.t) :
    {{ body.eof.body.Impl_revm_bytecode_eof_body_EofBody.code [] [] [φ self; φ index] 🔽 option alloy_primitives.links.bytes_.Bytes.t }}.
  Proof.
    run_symbolic.
    run_symbolic_let. {
      run_symbolic.
      run_symbolic_are_equal_integer; run_symbolic.
      { run_symbolic_are_equal_bool; run_symbolic.
        admit.
      }
      { run_symbolic_are_equal_bool; run_symbolic.
        admit.
      }
    }
    intros [|[]]; run_symbolic.
    destruct (vec.links.mod.Impl_Deref_for_Vec.run (T := Usize.t) (A := Global.t)).
    destruct deref as [deref [H_deref run_deref]].
    run_symbolic.
    run_symbolic_closure. {
      pose proof (Impl_Slice.run_get
        Usize.t
        (I := Usize.t)
        (Output := Ref.t Pointer.Kind.Ref Usize.t)
      ).
      apply H.
      pose proof (Impl_SliceIndex_for_Usize.run Usize.t).
      cbn.
      Print Impl_Slice.Self.
      unfold Impl_Slice.Self.
      cbn.
      admit.
    }
    admit.
  Admitted.

  (*
  pub fn into_eof(self) -> Eof {
        // TODO : Add bounds checks.
        let mut prev_value = 0;
        let header = EofHeader {
            types_size: self.types_section.len() as u16 * 4,
            code_sizes: self
                .code_section
                .iter()
                .map(|x| {
                    let ret = (x - prev_value) as u16;
                    prev_value = *x;
                    ret
                })
                .collect(),
            container_sizes: self
                .container_section
                .iter()
                .map(|x| x.len() as u16)
                .collect(),
            data_size: self.data_section.len() as u16,
            sum_code_sizes: self.code.len(),
            sum_container_sizes: self.container_section.iter().map(|x| x.len()).sum(),
        };
        let mut buffer = Vec::new();
        header.encode(&mut buffer);
        self.encode(&mut buffer);
        Eof {
            header,
            body: self,
            raw: buffer.into(),
        }
    }
  *)
  Definition run_into_eof (self : Self) :
    {{ body.eof.body.Impl_revm_bytecode_eof_body_EofBody.into_eof [] [] [φ self] 🔽 Eof.t }}.
  Proof.
  Admitted.
End Impl_EofBody.
