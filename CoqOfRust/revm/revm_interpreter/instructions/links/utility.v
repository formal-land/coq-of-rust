Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.convert.links.mod.
Require Import revm.revm_interpreter.instructions.utility.
Require Import revm.links.dependencies.
Require Import ruint.links.bytes.

Import bytes.Impl_Uint.

(* pub fn cast_slice_to_u256(slice: &[u8], dest: &mut U256) *)
Instance run_cast_slice_to_u256
  (slice : Ref.t Pointer.Kind.Ref (list U8.t))
  (dest : Ref.t Pointer.Kind.MutRef U256.t) :
  Run.Trait instructions.utility.cast_slice_to_u256 [] [] [ φ slice; φ dest ] unit.
Proof.
  constructor.
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
      Run.Trait method [] [] [ φ self ] U256.t
    ).

  Class Run (Self : Set) `{Link Self} : Set := {
    into_u256 : Run_into_u256 Self;
  }.
End IntoU256.

(* impl IntoU256 for B256 { *)
Module Impl_IntoU256_for_B256.
  Definition Self : Set :=
    B256.t.

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
    alloy_primitives.bits.links.address.Address.t.

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
      run_symbolic.
      admit.
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
      Run.Trait method [] [] [ φ self ] alloy_primitives.bits.links.address.Address.t
    ).

  Class Run (Self : Set) `{Link Self} : Set := {
    into_address : Run_into_address Self;
  }.
End IntoAddress.

(* impl IntoAddress for U256 { *)
Module Impl_IntoAddress_for_U256.
  Definition Self : Set :=
    U256.t.

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
      destruct (
        alloy_primitives.bits.links.fixed.Impl_From_for_FixedBytes.run {| Integer.value := 32 |}
      ).
      run_symbolic.
    }
  Defined.

  Instance run : IntoAddress.Run Self := {
    IntoAddress.into_address := run_into_address;
  }.
End Impl_IntoAddress_for_U256.
