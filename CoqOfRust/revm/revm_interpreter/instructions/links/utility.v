Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bits.links.fixed.
Require Import alloy_primitives.links.aliases.
Require Import core.convert.links.mod.
Require Import core.fmt.links.mod.
Require Import core.iter.traits.links.collect.
Require Import core.links.panicking.
Require Import core.num.links.mod.
Require Import core.ptr.links.mut_ptr.
Require Import core.slice.links.iter.
Require Import core.slice.links.mod.
Require Import revm.revm_interpreter.instructions.utility.
Require Import ruint.links.bytes.

Import Impl_Arguments.
Import Impl_ChunksExact.
Import Impl_pointer_mut_T.
Import Impl_RChunksExact.
Import Impl_Slice.
Import bytes.Impl_Uint.
Import lib.Impl_Uint.
Import Impl_u64.

(* pub fn cast_slice_to_u256(slice: &[u8], dest: &mut U256) *)
Instance run_cast_slice_to_u256
  (slice : Ref.t Pointer.Kind.Ref (list U8.t))
  (dest : Ref.t Pointer.Kind.MutRef aliases.U256.t) :
  Run.Trait instructions.utility.cast_slice_to_u256 [] [] [ φ slice; φ dest ] unit.
Proof.
  constructor.
  destruct (Impl_IntoIterator_for_Iterator_I.run (ChunksExact.t U8.t) U8.t).
  destruct (Impl_Iterator_for_ChunksExact.run U8.t).
  destruct (Impl_IntoIterator_for_Iterator_I.run (RChunksExact.t U8.t) U8.t).
  destruct (Impl_Iterator_for_RChunksExact.run U8.t).
  run_symbolic.
Admitted.

(*
pub trait IntoU256 {
    fn into_u256(self) -> U256;
}
*)
Module IntoU256.
  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("revm_interpreter::instructions::utility::IntoU256", [], [], Φ Self).

  Definition Run_into_u256 (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "into_u256" (fun method =>
      forall (self : Self),
      Run.Trait method [] [] [ φ self ] aliases.U256.t
    ).

  Class Run (Self : Set) `{Link Self} : Set := {
    into_u256 : Run_into_u256 Self;
  }.
End IntoU256.

(* impl IntoU256 for B256 { *)
Module Impl_IntoU256_for_B256.
  Definition Self : Set :=
    aliases.B256.t.

  (* fn into_u256(self) -> U256 *)
  Definition run_into_u256 : IntoU256.Run_into_u256 Self.
  Proof.
    econstructor.
    { eapply IsTraitMethod.Defined.
      { apply instructions.utility.Impl_revm_interpreter_instructions_utility_IntoU256_for_alloy_primitives_bits_fixed_FixedBytes_Usize_32.Implements. }
      { reflexivity. }
    }
    { intros.
      constructor.
      run_symbolic.
      admit.
    }
  Admitted.

  Instance run : IntoU256.Run Self := {
    IntoU256.into_u256 := run_into_u256;
  }.
End Impl_IntoU256_for_B256.

(* impl IntoU256 for Address { *)
Module Impl_IntoU256_for_Address.
  Definition Self : Set :=
    Address.t.

  (* fn into_u256(self) -> U256 *)
  Definition run_into_u256 : IntoU256.Run_into_u256 Self.
  Proof.
    econstructor.
    { eapply IsTraitMethod.Defined.
      { apply instructions.utility.Impl_revm_interpreter_instructions_utility_IntoU256_for_alloy_primitives_bits_address_Address.Implements. }
      { reflexivity. }
    }
    { intros.
      constructor.
      destruct Impl_IntoU256_for_B256.run.
      run_symbolic; admit.
    }
  Admitted.

  Instance run : IntoU256.Run Self := {
    IntoU256.into_u256 := run_into_u256;
  }.
End Impl_IntoU256_for_Address.

(*
pub trait IntoAddress {
    fn into_address(self) -> Address;
}
*)
Module IntoAddress.
  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("revm_interpreter::instructions::utility::IntoAddress", [], [], Φ Self).

  Definition Run_into_address (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "into_address" (fun method =>
      forall (self : Self),
      Run.Trait method [] [] [ φ self ] Address.t
    ).

  Class Run (Self : Set) `{Link Self} : Set := {
    into_address : Run_into_address Self;
  }.
End IntoAddress.

(* impl IntoAddress for U256 { *)
Module Impl_IntoAddress_for_U256.
  Definition Self : Set :=
    aliases.U256.t.

  (* fn into_address(self) -> Address *)
  Definition run_into_address : IntoAddress.Run_into_address Self.
  Proof.
    econstructor.
    { eapply IsTraitMethod.Defined.
      { apply instructions.utility.Impl_revm_interpreter_instructions_utility_IntoAddress_for_ruint_Uint_Usize_256_Usize_4.Implements. }
      { reflexivity. }
    }
    { intros.
      constructor.
      run_symbolic.
      admit.
    }
  Admitted.

  Instance run : IntoAddress.Run Self := {
    IntoAddress.into_address := run_into_address;
  }.
End Impl_IntoAddress_for_U256.
