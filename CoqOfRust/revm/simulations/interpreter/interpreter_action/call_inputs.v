Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import CoqOfRust.core.simulations.bool.
Require Import CoqOfRust.revm.simulations.dependencies.

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
  | Transfer : Z -> t
  | Apparent : Z -> t.

  Global Instance IsToTy : ToTy t := {
    Φ := Ty.path "revm_interpreter::interpreter_action::call_inputs::CallValue";
  }.

  Global Instance IsToValue : ToValue t := {
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

  Global Instance IsToTy : ToTy t := {
    Φ := Ty.path "revm_interpreter::interpreter_action::call_inputs::CallScheme";
  }.

  Global Instance IsToValue : ToValue t := {
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
    input : Bytes.t;
    return_memory_offset : (Z * Z);
    gas_limit : Z;
    bytecode_address : Address.t;
    target_address : Address.t;
    caller : Address.t;
    value : CallValue.t;
    scheme : CallScheme.t;
    is_static : bool;
    is_eof : bool;
  }.

  Global Instance IsToTy : ToTy t := {
    Φ := Ty.path "revm_interpreter::interpreter::call_inputs::CallInputs";
  }.

  Global Instance IsToValue : ToValue t := {
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
