(* Generated *)
Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import alloy_primitives.bits.links.fixed.
Require Import alloy_primitives.links.aliases.
Require Import revm.revm_primitives.lib.

Import Impl_FixedBytes.

(* pub const KECCAK_EMPTY: B256 *)
Instance run_KECCAK_EMPTY :
  Run.Trait
    value_KECCAK_EMPTY [] [] []
    (Ref.t Pointer.Kind.Raw aliases.B256.t).
Proof.
  constructor.
  run_symbolic.
Admitted.
