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
    Φ := Ty.path "revm_interpreter::interpreter_action::create_inputs::CreateInputs";
    φ x :=
      Value.StructRecord "revm_interpreter::interpreter_action::create_inputs::CreateInputs" [] [] [
        ("caller", φ x.(caller));
        ("gas_limit", φ x.(gas_limit));
        ("init_code", φ x.(init_code));
        ("scheme", φ x.(scheme));
        ("value", φ x.(value))
      ];
  }.

  Definition of_ty :
    OfTy.t (Ty.path "revm_interpreter::interpreter_action::create_inputs::CreateInputs").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.

  Lemma of_value_with
    (caller : Address.t) caller'
    (scheme : CreateScheme.t) scheme'
    (value : aliases.U256.t) value'
    (init_code : Bytes.t) init_code'
    (gas_limit : U64.t) gas_limit' :
    caller' = φ caller ->
    scheme' = φ scheme ->
    value' = φ value ->
    init_code' = φ init_code ->
    gas_limit' = φ gas_limit ->
    Value.StructRecord "revm_interpreter::interpreter_action::create_inputs::CreateInputs" [] [] [
      ("caller", caller');
      ("gas_limit", gas_limit');
      ("init_code", init_code');
      ("scheme", scheme');
      ("value", value')
    ] = φ (Build_t caller scheme value init_code gas_limit).
  Proof. now intros; subst. Qed.
  Smpl Add apply of_value_with : of_value.

  Definition of_value
    (caller : Address.t) caller'
    (scheme : CreateScheme.t) scheme'
    (value : aliases.U256.t) value'
    (init_code : Bytes.t) init_code'
    (gas_limit : U64.t) gas_limit' :
    caller' = φ caller ->
    scheme' = φ scheme ->
    value' = φ value ->
    init_code' = φ init_code ->
    gas_limit' = φ gas_limit ->
    OfValue.t (Value.StructRecord "revm_interpreter::interpreter_action::create_inputs::CreateInputs" [] [] [
      ("caller", caller');
      ("gas_limit", gas_limit');
      ("init_code", init_code');
      ("scheme", scheme');
      ("value", value')
    ]).
  Proof. intros; eapply OfValue.Make; apply of_value_with; eassumption. Defined.
  Smpl Add eapply of_value : of_value.
End CreateInputs.
