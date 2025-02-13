Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import revm.links.dependencies.

(*
pub struct Eof {
    pub header: EofHeader,
    pub body: EofBody,
    pub raw: Bytes,
}
*)
Module Eof.
  Parameter t : Set.
  (* Record t : Set := {
    header : EofHeader.t;
    body : EofBody.t;
    raw : Bytes.t;
  }. *)

  Global Instance IsLink : Link t.
  Admitted.

  (* Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_bytecode::eof::Eof";
    φ x :=
      Value.StructRecord "revm_bytecode::eof::Eof" [
        ("header", φ x.(header));
        ("body", φ x.(body));
        ("raw", φ x.(raw))
      ];
  }. *)
End Eof.

(*
  /// Inputs for EOF create call.
  #[derive(Debug, Default, Clone, PartialEq, Eq)]
  #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
  pub struct EOFCreateInput {
      /// Caller of Eof Craate
      pub caller: Address,
      /// New contract address.
      pub created_address: Address,
      /// Values of ether transfered
      pub value: U256,
      /// Init eof code that is going to be executed.
      pub eof_init_code: Eof,
      /// Gas limit for the create call.
      pub gas_limit: u64,
  }
*)

Module EOFCreateInput.
  Record t : Set := {
    caller : Address.t;
    created_address : Address.t;
    value : U256.t;
    eof_init_code : Eof.t;
    gas_limit : U64.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter::eof_create_input::EOFCreateInput";
    φ x :=
      Value.StructRecord "revm_interpreter::interpreter::eof_create_input::EOFCreateInput" [
        ("caller", φ x.(caller));
        ("created_address", φ x.(created_address));
        ("value", φ x.(value));
        ("eof_init_code", φ x.(eof_init_code));
        ("gas_limit", φ x.(gas_limit))
      ];
  }.
End EOFCreateInput.
