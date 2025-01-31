Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.lib.
Require Import CoqOfRust.links.M.
Require Import core.num.mod.
Require Import revm.translations.interpreter.gas.calc.

Import Run.

(*
pub const fn memory_gas(num_words: usize) -> u64 {
    let num_words = num_words as u64;
    MEMORY
        .saturating_mul(num_words)
        .saturating_add(num_words.saturating_mul(num_words) / 512)
}
*)
Lemma run_memory_gas (num_words: Usize.t) :
  {{ gas.calc.memory_gas [] [] [ φ num_words ] 🔽 U64.t }}.
Proof.
  run_symbolic.
  eapply Run.Let. {
    run_symbolic.
    eapply Run.Rewrite. {
      rewrite cast_integer_eq with
        (kind_source := IntegerKind.Usize)
        (kind_target := IntegerKind.U64).
      reflexivity.
    }
    run_symbolic.
  }
  intros []; run_symbolic.
  eapply Run.CallPrimitiveGetAssociatedFunction. {
    apply num.Impl_u64.AssociatedFunction_saturating_add.
  }
  eapply Run.CallPrimitiveGetAssociatedFunction. {
    apply num.Impl_u64.AssociatedFunction_saturating_mul.
  }
  admit.
Admitted.
