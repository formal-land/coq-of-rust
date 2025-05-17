Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.links.aliases.
Require Import revm.revm_bytecode.links.eof.
Require Import revm.revm_interpreter.interpreter_action.eof_create_inputs.

Module EOFCreateKind.
  Inductive t : Set :=
  | Tx
    (initdata : Bytes.t)
  | Opcode
    (initcode : Eof.t)
    (input : Bytes.t)
    (created_address : Address.t)
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "eof_create_inputs::EOFCreateKind";
    φ x :=
      match x with
      | Tx initdata =>
        Value.StructRecord "eof_create_inputs::EOFCreateKind::Tx" [] [] [
          ("initdata", φ initdata)
        ]
      | Opcode initcode input created_address =>
        Value.StructRecord "eof_create_inputs::EOFCreateKind::Opcode" [] [] [
          ("initcode", φ initcode);
          ("input", φ input);
          ("created_address", φ created_address)
        ]
      end
  }.
End EOFCreateKind.

Module EOFCreateInputs.
  Record t : Set := {
    caller: Address.t;
    value: aliases.U256.t;
    gas_limit: U64.t;
    kind: EOFCreateKind.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter_action::eof_create_inputs::EOFCreateInputs";
    φ '(Build_t caller value gas_limit kind) :=
      Value.StructRecord "revm_interpreter::interpreter_action::eof_create_inputs::EOFCreateInputs" [] [] [
        ("caller", φ caller);
        ("value", φ value);
        ("gas_limit", φ gas_limit);
        ("kind", φ kind)
      ]
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_interpreter::interpreter_action::eof_create_inputs::EOFCreateInputs").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.
End EOFCreateInputs.

Module Impl_EOFCreateInputs.
  Definition Self : Set := EOFCreateInputs.t.

  (*
  pub fn new_opcode(
      caller: Address,
      created_address: Address,
      value: U256,
      eof_init_code: Eof,
      gas_limit: u64,
      input: Bytes,
  ) -> EOFCreateInputs
  *)
  Instance run_new_opcode
      (caller : Address.t)
      (created_address : Address.t)
      (value : aliases.U256.t)
      (eof_init_code : Eof.t)
      (gas_limit : U64.t)
      (input : Bytes.t) :
    Run.Trait interpreter_action.eof_create_inputs.Impl_revm_interpreter_interpreter_action_eof_create_inputs_EOFCreateInputs.new_opcode
      [] [] [ φ caller; φ created_address; φ value; φ eof_init_code; φ gas_limit; φ input ]
      EOFCreateInputs.t.
  Admitted.
End Impl_EOFCreateInputs.
Export Impl_EOFCreateInputs.
