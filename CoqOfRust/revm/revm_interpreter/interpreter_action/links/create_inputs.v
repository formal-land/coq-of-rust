Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import revm.links.dependencies.
Require Import revm_context_interface.links.cfg.

(*
  /// Inputs for a create call.
  #[derive(Clone, Debug, PartialEq, Eq, Hash)]
  #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
  pub struct CreateInputs {
      /// Caller address of the EVM.
      pub caller: Address,
      /// The create scheme.
      pub scheme: CreateScheme,
      /// The value to transfer.
      pub value: U256,
      /// The init code of the contract.
      pub init_code: Bytes,
      /// The gas limit of the call.
      pub gas_limit: u64,
  }
*)

Module CreateInputs.
  Record t : Set := {
    caller : Address.t;
    scheme : CreateScheme.t;
    value : U256.t;
    init_code : alloy_primitives.links.bytes_.Bytes.t;
    gas_limit : U64.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter::create_inputs::CreateInputs";
    φ x :=
      Value.StructRecord "revm_interpreter::interpreter::create_inputs::CreateInputs" [
        ("caller", φ x.(caller));
        ("scheme", φ x.(scheme));
        ("value", φ x.(value));
        ("init_code", φ x.(init_code));
        ("gas_limit", φ x.(gas_limit))
      ];
  }.
End CreateInputs.
