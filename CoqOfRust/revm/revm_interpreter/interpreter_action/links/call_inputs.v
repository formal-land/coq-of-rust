Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.links.aliases.
Require Import core.ops.links.range.

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
  | Transfer : aliases.U256.t -> t
  | Apparent : aliases.U256.t -> t.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter_action::call_inputs::CallValue";
    φ x :=
      match x with
      | Transfer x => Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallValue::Transfer" [] [] [φ x]
      | Apparent x => Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallValue::Apparent" [] [] [φ x]
      end;
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_interpreter::interpreter_action::call_inputs::CallValue").
  Proof.
    eapply OfTy.Make with (A := t).
    now subst.
  Defined.
  Smpl Add eapply of_ty : of_ty.

  Lemma of_value_with_Transfer x x' :
    x' = φ x ->
    Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallValue::Transfer" [] [] [x'] =
    φ (Transfer x).
  Proof.
    now intros; subst.
  Qed.
  Smpl Add apply of_value_with_Transfer : of_value.

  Lemma of_value_with_Apparent x x' :
    x' = φ x ->
    Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallValue::Apparent" [] [] [x'] =
    φ (Apparent x).
  Proof.
    now intros; subst.
  Qed.
  Smpl Add apply of_value_with_Apparent : of_value.

  Definition of_value_Transfer (x : aliases.U256.t) x' :
    x' = φ x ->
    OfValue.t (Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallValue::Transfer" [] [] [x']).
  Proof.
    econstructor; apply of_value_with_Transfer; eassumption.
  Defined.
  Smpl Add eapply of_value_Transfer : of_value.

  Definition of_value_Apparent (x : aliases.U256.t) x' :
    x' = φ x ->
    OfValue.t (Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallValue::Apparent" [] [] [x']).
  Proof.
    econstructor; apply of_value_with_Apparent; eassumption.
  Defined.
  Smpl Add eapply of_value_Apparent : of_value.
End CallValue.

(*
  pub enum CallScheme {
      /// `CALL`.
      Call,
      /// `CALLCODE`
      CallCode,
      /// `DELEGATECALL`
      DelegateCall,
      /// `STATICCALL`
      StaticCall,
      /// `EXTCALL`
      ExtCall,
      /// `EXTSTATICCALL`
      ExtStaticCall,
      /// `EXTDELEGATECALL`
      ExtDelegateCall,
  }
*)

Module CallScheme.
  Inductive t : Set :=
  | Call
  | CallCode
  | DelegateCall
  | StaticCall
  | ExtCall
  | ExtStaticCall
  | ExtDelegateCall.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter_action::call_inputs::CallScheme";
    φ x :=
      match x with
      | Call => Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::Call" [] [] []
      | CallCode => Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::CallCode" [] [] []
      | DelegateCall => Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::DelegateCall" [] [] []
      | StaticCall => Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::StaticCall" [] [] []
      | ExtCall => Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::ExtCall" [] [] []
      | ExtStaticCall => Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::ExtStaticCall" [] [] []
      | ExtDelegateCall => Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::ExtDelegateCall" [] [] []
      end;
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_interpreter::interpreter_action::call_inputs::CallScheme").
  Proof.
    eapply OfTy.Make with (A := t).
    now subst.
  Defined.
  Smpl Add apply of_ty : of_ty.

  Lemma of_value_with_Call :
    Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::Call" [] [] [] =
    φ Call.
  Proof.
    reflexivity.
  Qed.
  Smpl Add apply of_value_with_Call : of_value.

  Lemma of_value_with_CallCode :
    Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::CallCode" [] [] [] =
    φ CallCode.
  Proof.
    reflexivity.
  Qed.
  Smpl Add apply of_value_with_CallCode : of_value.

  Lemma of_value_with_DelegateCall :
    Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::DelegateCall" [] [] [] =
    φ DelegateCall.
  Proof.
    reflexivity.
  Qed.
  Smpl Add apply of_value_with_DelegateCall : of_value.

  Lemma of_value_with_StaticCall :
    Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::StaticCall" [] [] [] =
    φ StaticCall.
  Proof.
    reflexivity.
  Qed.
  Smpl Add apply of_value_with_StaticCall : of_value.

  Lemma of_value_with_ExtCall :
    Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::ExtCall" [] [] [] =
    φ ExtCall.
  Proof.
    reflexivity.
  Qed.
  Smpl Add apply of_value_with_ExtCall : of_value.

  Lemma of_value_with_ExtStaticCall :
    Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::ExtStaticCall" [] [] [] =
    φ ExtStaticCall.
  Proof.
    reflexivity.
  Qed.
  Smpl Add apply of_value_with_ExtStaticCall : of_value.

  Lemma of_value_with_ExtDelegateCall :
    Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::ExtDelegateCall" [] [] [] =
    φ ExtDelegateCall.
  Proof.
    reflexivity.
  Qed.
  Smpl Add apply of_value_with_ExtDelegateCall : of_value.

  Definition of_value_Call :
    OfValue.t (Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::Call" [] [] []).
  Proof.
    econstructor; apply of_value_with_Call.
  Defined.
  Smpl Add apply of_value_Call : of_value.

  Definition of_value_CallCode :
    OfValue.t (Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::CallCode" [] [] []).
  Proof.
    econstructor; apply of_value_with_CallCode.
  Defined.
  Smpl Add apply of_value_CallCode : of_value.

  Definition of_value_DelegateCall :
    OfValue.t (Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::DelegateCall" [] [] []).
  Proof.
    econstructor; apply of_value_with_DelegateCall.
  Defined.
  Smpl Add apply of_value_DelegateCall : of_value.

  Definition of_value_StaticCall :
    OfValue.t (Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::StaticCall" [] [] []).
  Proof.
    econstructor; apply of_value_with_StaticCall.
  Defined.
  Smpl Add apply of_value_StaticCall : of_value.

  Definition of_value_ExtCall :
    OfValue.t (Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::ExtCall" [] [] []).
  Proof.
    econstructor; apply of_value_with_ExtCall.
  Defined.
  Smpl Add apply of_value_ExtCall : of_value.

  Definition of_value_ExtStaticCall :
    OfValue.t (Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::ExtStaticCall" [] [] []).
  Proof.
    econstructor; apply of_value_with_ExtStaticCall.
  Defined.
  Smpl Add apply of_value_ExtStaticCall : of_value.

  Definition of_value_ExtDelegateCall :
    OfValue.t (Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::ExtDelegateCall" [] [] []).
  Proof.
    econstructor; apply of_value_with_ExtDelegateCall.
  Defined.
  Smpl Add apply of_value_ExtDelegateCall : of_value.
End CallScheme.

(*
  pub struct CallInputs {
      pub input: Bytes,
      pub return_memory_offset: Range<usize>,
      pub gas_limit: u64,
      pub bytecode_address: Address,
      pub target_address: Address,
      pub caller: Address,
      pub value: CallValue,
      pub scheme: CallScheme,
      pub is_static: bool,
      pub is_eof: bool,
  }
*)
Module CallInputs.
  Record t : Set := {
    bytecode_address : Address.t;
    caller : Address.t;
    gas_limit : U64.t;
    input : Bytes.t;
    is_eof : bool;
    is_static : bool;
    return_memory_offset : Range.t Usize.t;
    scheme : CallScheme.t;
    target_address : Address.t;
    value : CallValue.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter_action::call_inputs::CallInputs";
    φ x :=
      Value.StructRecord "revm_interpreter::interpreter_action::call_inputs::CallInputs" [] [] [
        ("bytecode_address", φ x.(bytecode_address));
        ("caller", φ x.(caller));
        ("gas_limit", φ x.(gas_limit));
        ("input", φ x.(input));
        ("is_eof", φ x.(is_eof));
        ("is_static", φ x.(is_static));
        ("return_memory_offset", φ x.(return_memory_offset));
        ("scheme", φ x.(scheme));
        ("target_address", φ x.(target_address));
        ("value", φ x.(value))
      ];
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_interpreter::interpreter_action::call_inputs::CallInputs").
  Proof.
    eapply OfTy.Make with (A := t).
    reflexivity.
  Defined.
  Smpl Add apply of_ty : of_ty.

  Lemma of_value_with
      bytecode_address bytecode_address'
      caller caller'
      gas_limit gas_limit'
      input input'
      is_eof is_eof'
      is_static is_static'
      return_memory_offset return_memory_offset'
      scheme scheme'
      target_address target_address'
      value value' :
    bytecode_address' = φ bytecode_address ->
    caller' = φ caller ->
    gas_limit' = φ gas_limit ->
    input' = φ input ->
    is_eof' = φ is_eof ->
    is_static' = φ is_static ->
    return_memory_offset' = φ return_memory_offset ->
    scheme' = φ scheme ->
    target_address' = φ target_address ->
    value' = φ value ->
    Value.StructRecord "revm_interpreter::interpreter_action::call_inputs::CallInputs" [] [] [
      ("bytecode_address", bytecode_address');
      ("caller", caller');
      ("gas_limit", gas_limit');
      ("input", input');
      ("is_eof", is_eof');
      ("is_static", is_static');
      ("return_memory_offset", return_memory_offset');
      ("scheme", scheme');
      ("target_address", target_address');
      ("value", value')
    ] = φ (Build_t
      bytecode_address
      caller
      gas_limit
      input
      is_eof
      is_static
      return_memory_offset
      scheme
      target_address
      value
    ).
  Proof.
    now intros; subst.
  Qed.
  Smpl Add apply of_value_with : of_value.

  Definition of_value
      (bytecode_address : Address.t) bytecode_address'
      (caller : Address.t) caller'
      (gas_limit : U64.t) gas_limit'
      (input : Bytes.t) input'
      (is_eof : bool) is_eof'
      (is_static : bool) is_static'
      (return_memory_offset : Range.t Usize.t) return_memory_offset'
      (scheme : CallScheme.t) scheme'
      (target_address : Address.t) target_address'
      (value : CallValue.t) value' :
    bytecode_address' = φ bytecode_address ->
    caller' = φ caller ->
    gas_limit' = φ gas_limit ->
    input' = φ input ->
    is_eof' = φ is_eof ->
    is_static' = φ is_static ->
    return_memory_offset' = φ return_memory_offset ->
    scheme' = φ scheme ->
    target_address' = φ target_address ->
    value' = φ value ->
    OfValue.t (
      Value.StructRecord "revm_interpreter::interpreter_action::call_inputs::CallInputs" [] [] [
        ("bytecode_address", bytecode_address');
        ("caller", caller');
        ("gas_limit", gas_limit');
        ("input", input');
        ("is_eof", is_eof');
        ("is_static", is_static');
        ("return_memory_offset", return_memory_offset');
        ("scheme", scheme');
        ("target_address", target_address');
        ("value", value')
      ]
    ).
  Proof.
    econstructor; apply of_value_with; eassumption.
  Defined.
  Smpl Add eapply of_value : of_value.

  Module SubPointer.
    Definition get_input : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_interpreter::interpreter_action::call_inputs::CallInputs" "input") :=
    {|
      SubPointer.Runner.projection x := Some x.(input);
      SubPointer.Runner.injection x y := Some (x <| input := y |>);
    |}.

    Lemma get_input_is_valid :
      SubPointer.Runner.Valid.t get_input.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_input_is_valid : run_sub_pointer.

    Definition get_return_memory_offset : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_interpreter::interpreter_action::call_inputs::CallInputs" "return_memory_offset") :=
    {|
      SubPointer.Runner.projection x := Some x.(return_memory_offset);
      SubPointer.Runner.injection x y := Some (x <| return_memory_offset := y |>);
    |}.

    Lemma get_return_memory_offset_is_valid :
      SubPointer.Runner.Valid.t get_return_memory_offset.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_return_memory_offset_is_valid : run_sub_pointer.

    Definition get_gas_limit : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_interpreter::interpreter_action::call_inputs::CallInputs" "gas_limit") :=
    {|
      SubPointer.Runner.projection x := Some x.(gas_limit);
      SubPointer.Runner.injection x y := Some (x <| gas_limit := y |>);
    |}.

    Lemma get_gas_limit_is_valid :
      SubPointer.Runner.Valid.t get_gas_limit.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_gas_limit_is_valid : run_sub_pointer.

    Definition get_bytecode_address : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_interpreter::interpreter_action::call_inputs::CallInputs" "bytecode_address") :=
    {|
      SubPointer.Runner.projection x := Some x.(bytecode_address);
      SubPointer.Runner.injection x y := Some (x <| bytecode_address := y |>);
    |}.

    Lemma get_bytecode_address_is_valid :
      SubPointer.Runner.Valid.t get_bytecode_address.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_bytecode_address_is_valid : run_sub_pointer.

    Definition get_target_address : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_interpreter::interpreter_action::call_inputs::CallInputs" "target_address") :=
    {|
      SubPointer.Runner.projection x := Some x.(target_address);
      SubPointer.Runner.injection x y := Some (x <| target_address := y |>);
    |}.

    Lemma get_target_address_is_valid :
      SubPointer.Runner.Valid.t get_target_address.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_target_address_is_valid : run_sub_pointer.

    Definition get_caller : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_interpreter::interpreter_action::call_inputs::CallInputs" "caller") :=
    {|
      SubPointer.Runner.projection x := Some x.(caller);
      SubPointer.Runner.injection x y := Some (x <| caller := y |>);
    |}.

    Lemma get_caller_is_valid :
      SubPointer.Runner.Valid.t get_caller.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_caller_is_valid : run_sub_pointer.

    Definition get_value : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_interpreter::interpreter_action::call_inputs::CallInputs" "value") :=
    {|
      SubPointer.Runner.projection x := Some x.(value);
      SubPointer.Runner.injection x y := Some (x <| value := y |>);
    |}.

    Lemma get_value_is_valid :
      SubPointer.Runner.Valid.t get_value.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_value_is_valid : run_sub_pointer.

    Definition get_scheme : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_interpreter::interpreter_action::call_inputs::CallInputs" "scheme") :=
    {|
      SubPointer.Runner.projection x := Some x.(scheme);
      SubPointer.Runner.injection x y := Some (x <| scheme := y |>);
    |}.

    Lemma get_scheme_is_valid :
      SubPointer.Runner.Valid.t get_scheme.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_scheme_is_valid : run_sub_pointer.

    Definition get_is_static : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_interpreter::interpreter_action::call_inputs::CallInputs" "is_static") :=
    {|
      SubPointer.Runner.projection x := Some x.(is_static);
      SubPointer.Runner.injection x y := Some (x <| is_static := y |>);
    |}.

    Lemma get_is_static_is_valid :
      SubPointer.Runner.Valid.t get_is_static.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_is_static_is_valid : run_sub_pointer.

    Definition get_is_eof : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_interpreter::interpreter_action::call_inputs::CallInputs" "is_eof") :=
    {|
      SubPointer.Runner.projection x := Some x.(is_eof);
      SubPointer.Runner.injection x y := Some (x <| is_eof := y |>);
    |}.

    Lemma get_is_eof_is_valid :
      SubPointer.Runner.Valid.t get_is_eof.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_is_eof_is_valid : run_sub_pointer.
  End SubPointer.
End CallInputs.
