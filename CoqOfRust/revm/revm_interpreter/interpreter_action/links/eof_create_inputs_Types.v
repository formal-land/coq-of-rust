(* Generated file. Do not edit. *)
Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require Import revm.links.dependencies.
Require revm.revm_bytecode.links.eof.

Module EOFCreateKind.
  Inductive t : Set :=
  | Tx
    (initdata : alloy_primitives.links.bytes_.Bytes.t) :
    t
  | Opcode
    (initcode : revm_bytecode.links.eof.Eof.t)
    (input : alloy_primitives.links.bytes_.Bytes.t)
    (created_address : alloy_primitives.bits.links.address.Address.t) :
    t
  .
End EOFCreateKind.
