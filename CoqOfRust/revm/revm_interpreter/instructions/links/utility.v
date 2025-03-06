Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.convert.links.mod.
Require Import revm.revm_interpreter.instructions.utility.
Require Import revm.links.dependencies.

(*
pub trait IntoAddress {
    fn into_address(self) -> Address;
}
*)
Module IntoAddress.
  Definition Run_into_address (Self : Set) `{Link Self} : Set :=
    {into_address @
      IsTraitMethod.t "revm_interpreter::instructions::utility::IntoAddress" [] [] (Φ Self) "into_address" into_address *
      forall (self : Self),
        {{ into_address [] [] [ φ self ] 🔽 alloy_primitives.bits.links.address.Address.t }}
    }.

  Record Run (Self : Set) `{Link Self} : Set := {
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
    eexists; split.
    { eapply IsTraitMethod.Defined.
      { apply instructions.utility.Impl_revm_interpreter_instructions_utility_IntoAddress_for_ruint_Uint_Usize_256_Usize_4.Implements. }
      { reflexivity. }
    }
    { intros.
      run_symbolic.
      destruct (
        alloy_primitives.bits.links.fixed.Impl_From_for_FixedBytes.run {| Integer.value := 32 |}
      ).
      destruct from as [from [H_from run_from]].
      run_symbolic.
    }
  Defined.

  Definition run : IntoAddress.Run Self.
  Proof.
    constructor.
    { (* into_address *)
      apply run_into_address.
    }
  Defined.
End Impl_IntoAddress_for_U256.
