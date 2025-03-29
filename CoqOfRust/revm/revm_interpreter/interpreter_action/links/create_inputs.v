Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.links.aliases.
Require Import revm_context_interface.links.cfg.

(*
  pub struct CreateInputs {
      pub caller: Address,
      pub scheme: CreateScheme,
      pub value: U256,
      pub init_code: Bytes,
      pub gas_limit: u64,
  }
*)

Module CreateInputs.
  Record t : Set := {
    caller : Address.t;
    scheme : CreateScheme.t;
    value : aliases.U256.t;
    init_code : Bytes.t;
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
