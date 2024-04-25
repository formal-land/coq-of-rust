Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.proofs.M.
Require Import CoqOfRust.simulations.M.
Require CoqOfRust.core.option.
Require CoqOfRust.core.proofs.default.
Require CoqOfRust.core.simulations.option.

Import Run.

Module Impl_Option_T.
  Lemma run_unwrap_or_default {T : Set}
    {_ : ToValue T}
    {_ : core.simulations.default.Default.Trait T}
    (self : option T) :
    core.proofs.default.Default.TraitHasRun T ->
    Run.pure
      (core.option.option.Impl_core_option_Option_T.unwrap_or_default (Φ T) [] [φ self])
      (inl (φ (core.simulations.option.Impl_Option_T.unwrap_or_default self))).
  Proof.
    intros H_Default.
    destruct H_Default as [[default [H_default H_run_default]]].
    unfold Run.pure; intros.
    run_symbolic.
    destruct self; cbn.
    { run_symbolic. }
    { eapply Run.CallPrimitiveGetTraitMethod. {
        apply H_default.
      }
      eapply Run.CallClosure. {
        apply H_run_default.
      }
      run_symbolic.
    }
  Qed.
End Impl_Option_T.
