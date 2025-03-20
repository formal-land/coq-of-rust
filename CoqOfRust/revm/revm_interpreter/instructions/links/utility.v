Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.convert.links.mod.
Require Import revm.revm_interpreter.instructions.utility.
Require Import revm.links.dependencies.
Require Import ruint.links.bytes.

Import bytes.Impl_Uint.

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
