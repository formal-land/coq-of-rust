Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import CoqOfRust.core.links.option.
Require Import CoqOfRust.revm.links.dependencies.
Require Import CoqOfRust.revm.links.primitives.bytecode.

(*
  /// EVM contract information.
  #[derive(Clone, Debug, Default)]
  #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
  pub struct Contract {
      /// Contracts data
      pub input: Bytes,
      /// Bytecode contains contract code, size of original code, analysis with gas block and jump table.
      /// Note that current code is extended with push padding and STOP at end.
      pub bytecode: Bytecode,
      /// Bytecode hash for legacy. For EOF this would be None.
      pub hash: Option<B256>,
      /// Target address of the account. Storage of this address is going to be modified.
      pub target_address: Address,
      /// Caller of the EVM.
      pub caller: Address,
      /// Value send to contract from transaction or from CALL opcodes.
      pub call_value: U256,
  }
*)

Module Contract.
  Record t : Set := {
    input : Bytes.t;
    bytecode : Bytecode.t;
    hash : option B256.t;
    target_address : Address.t;
    caller : Address.t;
    call_value : U256.t;
  }.

  Global Instance IsToTy : ToTy t := {
    Φ := Ty.path "revm_interpreter::interpreter::contract::Contract";
  }.

  Global Instance IsToValue : ToValue t := {
    φ x :=
      Value.StructRecord "revm_interpreter::interpreter::contract::Contract" [
        ("input", φ x.(input));
        ("bytecode", φ x.(bytecode));
        ("hash", φ x.(hash));
        ("target_address", φ x.(target_address));
        ("caller", φ x.(caller));
        ("call_value", φ x.(call_value))
      ];
  }.
End Contract.
