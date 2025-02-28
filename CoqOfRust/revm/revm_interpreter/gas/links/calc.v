Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.lib.
Require Import CoqOfRust.links.M.
Require Import core.num.mod.
Require core.num.links.mod.
Require Import revm_interpreter.gas.calc.
Require revm_interpreter.gas.links.constants.

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
  run; try apply links.mod.Impl_u64.run_saturating_mul.
  run_symbolic.
  run_symbolic_closure. {
    apply links.mod.Impl_u64.run_saturating_add.
  }
  intros []; run_symbolic.
Defined.
Smpl Add apply run_memory_gas : run_closure.
