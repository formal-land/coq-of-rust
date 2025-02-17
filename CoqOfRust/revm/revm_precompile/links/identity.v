Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.lib.
Require Import CoqOfRust.links.M.
Require core.links.default.
Require Import revm_precompile.identity.

Import Run.
(*
pub const IDENTITY_BASE: u64 = 15;
*)

Definition BASE_eq : M.get_constant "revm_precompile::identity::IDENTITY_BASE" =
  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.U64 15)).
Proof.
  repeat (autorewrite with constant_rewrites || cbn).
  reflexivity.
Defined.
