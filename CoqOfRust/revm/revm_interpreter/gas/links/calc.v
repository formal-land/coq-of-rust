Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.num.mod.
Require Import core.num.links.mod.
Require Import revm_specification.links.hardfork.
Require Import CoqOfRust.revm.links.dependencies.
Require revm_interpreter.gas.links.constants.
Require Import revm_interpreter.gas.calc.

Import Impl_u64.

(*
pub const fn memory_gas(num_words: usize) -> u64 {
    let num_words = num_words as u64;
    MEMORY
        .saturating_mul(num_words)
        .saturating_add(num_words.saturating_mul(num_words) / 512)
}
*)
Instance run_memory_gas (num_words: Usize.t) :
  Run.Trait
    gas.calc.memory_gas [] [] [ φ num_words ]
    U64.t.
Proof.
  constructor.
  run_symbolic.
Defined.

(* NOTE: since we don't have U256 for now, we use Usize instead *)
(* pub fn exp_cost(spec_id: SpecId, power: U256) -> Option<u64> *)
Instance run_exp_cost (spec_id : SpecId.t) (power : U256.t) :
  Run.Trait
    gas.calc.exp_cost [] [] [ φ spec_id; φ power ]
    (option U64.t).
Proof.
  constructor.
  run_symbolic.
  (* NOTE: Should I finish the proof? *)
Admitted.
(* Defined. *)
