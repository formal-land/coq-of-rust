Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.links.aliases.
Require Import revm.revm_bytecode.links.eof.

Module EOFCreateKind.
  Inductive t : Set :=
  | Tx
    (initdata : Bytes.t)
  | Opcode
    (initcode : revm_bytecode.links.eof.Eof.t)
    (input : Bytes.t)
    (created_address : Address.t)
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "eof_create_inputs::EOFCreateKind";
    φ x :=
      match x with
      | Tx initdata =>
        Value.StructRecord "eof_create_inputs::EOFCreateKind::Tx" [
          ("initdata", φ initdata)
        ]
      | Opcode initcode input created_address =>
        Value.StructRecord "eof_create_inputs::EOFCreateKind::Opcode" [
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
      Value.StructRecord "revm_interpreter::interpreter_action::eof_create_inputs::EOFCreateInputs" [
        ("caller", φ caller);
        ("value", φ value);
        ("gas_limit", φ gas_limit);
        ("kind", φ kind)
      ]
  }.
End EOFCreateInputs.
