(* Generated *)
Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import revm.revm_primitives.lib.

Lemma KECCAK_EMPTY_eq :
  M.get_constant "revm_primitives::KECCAK_EMPTY" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U64 0)).
Proof.
  repeat (autorewrite with constant_rewrites || cbn).
Admitted.
Global Hint Rewrite KECCAK_EMPTY_eq : run_constant.
