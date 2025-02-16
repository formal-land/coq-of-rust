Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import CoqOfRust.revm.links.dependencies.

(*
  /// Call value.
  #[derive(Clone, Debug, PartialEq, Eq, Hash)]
  #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
  pub enum CallValue {
      /// Concrete value, transferred from caller to callee at the end of the transaction.
      Transfer(U256),
      /// Apparent value, that is **not** actually transferred.
      ///
      /// Set when in a `DELEGATECALL` call type, and used by the `CALLVALUE` opcode.
      Apparent(U256),
  }
*)

Module CallValue.
  Inductive t : Set :=
  | Transfer : U256.t -> t
  | Apparent : U256.t -> t.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter_action::call_inputs::CallValue";
    φ x :=
      match x with
      | Transfer x => Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallValue::Transfer" [φ x]
      | Apparent x => Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallValue::Approval" [φ x]
      end;
  }.
End CallValue.

(*
  /// Call scheme.
  #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
  #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
  pub enum CallScheme {
      /// `CALL`.
      Call,
      /// `CALLCODE`
      CallCode,
      /// `DELEGATECALL`
      DelegateCall,
      /// `STATICCALL`
      StaticCall,
  }
*)

Module CallScheme.
  Inductive t : Set :=
  | Call
  | CallCode
  | DelegateCall
  | StaticCall.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter_action::call_inputs::CallScheme";
    φ x :=
      match x with
      | Call => Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::Call" []
      | CallCode => Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::CallCode" []
      | DelegateCall => Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::DelegateCall" []
      | StaticCall => Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::StaticCall" []
      end;
  }.
End CallScheme.

(*
  /// Inputs for a call.
  #[derive(Clone, Debug, PartialEq, Eq, Hash)]
  #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
  pub struct CallInputs {
      /// The call data of the call.
      pub input: Bytes,
      /// The return memory offset where the output of the call is written.
      ///
      /// In EOF, this range is invalid as EOF calls do not write output to memory.
      pub return_memory_offset: Range<usize>,
      /// The gas limit of the call.
      pub gas_limit: u64,
      /// The account address of bytecode that is going to be executed.
      ///
      /// Previously `context.code_address`.
      pub bytecode_address: Address,
      /// Target address, this account storage is going to be modified.
      ///
      /// Previously `context.address`.
      pub target_address: Address,
      /// This caller is invoking the call.
      ///
      /// Previously `context.caller`.
      pub caller: Address,
      /// Call value.
      ///
      /// NOTE: This value may not necessarily be transferred from caller to callee, see [`CallValue`].
      ///
      /// Previously `transfer.value` or `context.apparent_value`.
      pub value: CallValue,
      /// The call scheme.
      ///
      /// Previously `context.scheme`.
      pub scheme: CallScheme,
      /// Whether the call is a static call, or is initiated inside a static call.
      pub is_static: bool,
      /// Whether the call is initiated from EOF bytecode.
      pub is_eof: bool,
  }
*)

(* TODO: Ranges? *)
Module CallInputs.
  Record t : Set := {
    input : alloy_primitives.links.bytes_.Bytes.t;
    return_memory_offset : Usize.t * Usize.t;
    gas_limit : U64.t;
    bytecode_address : alloy_primitives.bits.links.address.Address.t;
    target_address : alloy_primitives.bits.links.address.Address.t;
    caller : alloy_primitives.bits.links.address.Address.t;
    value : CallValue.t;
    scheme : CallScheme.t;
    is_static : bool;
    is_eof : bool;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter::call_inputs::CallInputs";
    φ x :=
      Value.StructRecord "revm_interpreter::interpreter::call_inputs::CallInputs" [
        ("input", φ x.(input));
        ("return_memory_offset", φ x.(return_memory_offset));
        ("gas_limit", φ x.(gas_limit));
        ("bytecode_address", φ x.(bytecode_address));
        ("target_address", φ x.(target_address));
        ("caller", φ x.(caller));
        ("value", φ x.(value));
        ("scheme", φ x.(scheme));
        ("is_static", φ x.(is_static));
        ("is_eof", φ x.(is_eof))
      ];
  }.
End CallInputs.
