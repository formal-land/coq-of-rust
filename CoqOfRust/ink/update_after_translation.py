"""
In this file we apply a list of manual updates to the translated Rust files.
"""
import re


def update_ink_env():
    file_name = "ink_env.v"
    with open(file_name, "r") as f:
        content = f.read()
    pattern = "Require Import CoqOfRust.CoqOfRust."
    content = sub_exactly_once(
        pattern,
        pattern
        + """
Require CoqOfRust.num_traits.

Require CoqOfRust.ink.alloc.
Require CoqOfRust.ink.ink_primitives.
Require CoqOfRust.ink.ink_storage_traits.
Require CoqOfRust.ink.parity_scale_codec.
Require CoqOfRust.ink.scale_decode.
Require CoqOfRust.ink.scale_encode.""",
        # TODO: add Require CoqOfRust.ink.ink_engine.
        content,
    )
    content = content.replace(
        """Parameter invoke_contract :
    forall
      `{H' : State.Trait}
      {E Args R : Set}
      `{ink_env.types.Environment.Trait E}
      `{parity_scale_codec.codec.Encode.Trait Args}
      `{parity_scale_codec.codec.Decode.Trait R},
    (ref
        (ink_env.call.call_builder.CallParams
          E
          (ink_env.call.call_builder.Call E)
          Args
          R))
      ->
      M (H := H') (ink_env.error.Result (ink_primitives.MessageResult R)).""",
        "",
    )
    content = content.replace(
        """Parameter invoke_contract_delegate :
    forall
      `{H' : State.Trait}
      {E Args R : Set}
      `{ink_env.types.Environment.Trait E}
      `{parity_scale_codec.codec.Encode.Trait Args}
      `{parity_scale_codec.codec.Decode.Trait R},
    (ref
        (ink_env.call.call_builder.CallParams
          E
          (ink_env.call.call_builder.DelegateCall E)
          Args
          R))
      ->
      M (H := H') (ink_env.error.Result (ink_primitives.MessageResult R)).""",
        "",
    )
    content = content.replace(
        """Parameter instantiate_contract :
    forall
      `{H' : State.Trait}
      {E ContractRef Args Salt R : Set}
      `{ink_env.types.Environment.Trait E}
      `{ink_env.call.create_builder.FromAccountId.Trait ContractRef (T := E)}
      `{parity_scale_codec.codec.Encode.Trait Args}
      `{core.convert.AsRef.Trait Salt (T := Slice u8)}
      `{ink_env.call.create_builder.ConstructorReturnType.Trait R
          (C := ContractRef)},
    (ref (ink_env.call.create_builder.CreateParams E ContractRef Args Salt R))
      ->
      M (H := H')
        (ink_env.error.Result
          (ink_primitives.ConstructorResult
            ink_env.call.create_builder.ConstructorReturnType.Output)).""",
        "",
    )
    content = content.replace(
        """Module TypedEnvBackend.
  Class Trait (Self : Set) `{ink_env.backend.EnvBackend.Trait Self} : Type := {
    caller
      `{H' : State.Trait}
      {E: Set}
      `{ink_env.types.Environment.Trait E}
      :
      (mut_ref Self) -> (M (H := H') E::type["AccountId"]);
    transferred_value
      `{H' : State.Trait}
      {E: Set}
      `{ink_env.types.Environment.Trait E}
      :
      (mut_ref Self) -> (M (H := H') E::type["Balance"]);
    weight_to_fee
      `{H' : State.Trait}
      {E: Set}
      `{ink_env.types.Environment.Trait E}
      :
      (mut_ref Self) -> u64 -> (M (H := H') E::type["Balance"]);
    gas_left
      `{H' : State.Trait}
      {E: Set}
      `{ink_env.types.Environment.Trait E}
      :
      (mut_ref Self) -> (M (H := H') u64);
    block_timestamp
      `{H' : State.Trait}
      {E: Set}
      `{ink_env.types.Environment.Trait E}
      :
      (mut_ref Self) -> (M (H := H') E::type["Timestamp"]);
    account_id
      `{H' : State.Trait}
      {E: Set}
      `{ink_env.types.Environment.Trait E}
      :
      (mut_ref Self) -> (M (H := H') E::type["AccountId"]);
    balance
      `{H' : State.Trait}
      {E: Set}
      `{ink_env.types.Environment.Trait E}
      :
      (mut_ref Self) -> (M (H := H') E::type["Balance"]);
    block_number
      `{H' : State.Trait}
      {E: Set}
      `{ink_env.types.Environment.Trait E}
      :
      (mut_ref Self) -> (M (H := H') E::type["BlockNumber"]);
    minimum_balance
      `{H' : State.Trait}
      {E: Set}
      `{ink_env.types.Environment.Trait E}
      :
      (mut_ref Self) -> (M (H := H') E::type["Balance"]);
    emit_event
      `{H' : State.Trait}
      {E Event: Set}
      `{ink_env.types.Environment.Trait E}
      `{ink_env.topics.Topics.Trait Event}
      `{parity_scale_codec.codec.Encode.Trait Event}
      :
      (mut_ref Self) -> Event -> (M (H := H') unit);
    invoke_contract
      `{H' : State.Trait}
      {E Args R: Set}
      `{ink_env.types.Environment.Trait E}
      `{parity_scale_codec.codec.Encode.Trait Args}
      `{parity_scale_codec.codec.Decode.Trait R}
      :
      (mut_ref Self) ->
      (ref
        (ink_env.call.call_builder.CallParams
          E
          (ink_env.call.call_builder.Call E)
          Args
          R)) ->
      (M (H := H') (ink_env.error.Result (ink_primitives.MessageResult R)));
    invoke_contract_delegate
      `{H' : State.Trait}
      {E Args R: Set}
      `{ink_env.types.Environment.Trait E}
      `{parity_scale_codec.codec.Encode.Trait Args}
      `{parity_scale_codec.codec.Decode.Trait R}
      :
      (mut_ref Self) ->
      (ref
        (ink_env.call.call_builder.CallParams
          E
          (ink_env.call.call_builder.DelegateCall E)
          Args
          R)) ->
      (M (H := H') (ink_env.error.Result (ink_primitives.MessageResult R)));
    instantiate_contract
      `{H' : State.Trait}
      {E ContractRef Args Salt R: Set}
      `{ink_env.types.Environment.Trait E}
      `{ink_env.call.create_builder.FromAccountId.Trait ContractRef (T := E)}
      `{parity_scale_codec.codec.Encode.Trait Args}
      `{core.convert.AsRef.Trait Salt (T := Slice u8)}
      `{ink_env.call.create_builder.ConstructorReturnType.Trait R
          (C := ContractRef)}
      :
      (mut_ref Self) ->
      (ref
        (ink_env.call.create_builder.CreateParams E ContractRef Args Salt R)) ->
      (M (H := H')
        (ink_env.error.Result
          (ink_primitives.ConstructorResult
            ink_env.call.create_builder.ConstructorReturnType.Output)));
    terminate_contract
      `{H' : State.Trait}
      {E: Set}
      `{ink_env.types.Environment.Trait E}
      :
      (mut_ref Self) -> E::type["AccountId"] -> (M (H := H') Empty_set);
    transfer
      `{H' : State.Trait}
      {E: Set}
      `{ink_env.types.Environment.Trait E}
      :
      (mut_ref Self) ->
      E::type["AccountId"] ->
      E::type["Balance"] ->
      (M (H := H') (ink_env.error.Result unit));
    is_contract
      `{H' : State.Trait}
      {E: Set}
      `{ink_env.types.Environment.Trait E}
      :
      (mut_ref Self) -> (ref E::type["AccountId"]) -> (M (H := H') bool);
    caller_is_origin
      `{H' : State.Trait}
      {E: Set}
      `{ink_env.types.Environment.Trait E}
      :
      (mut_ref Self) -> (M (H := H') bool);
    code_hash
      `{H' : State.Trait}
      {E: Set}
      `{ink_env.types.Environment.Trait E}
      :
      (mut_ref Self) ->
      (ref E::type["AccountId"]) ->
      (M (H := H') (ink_env.error.Result E::type["Hash"]));
    own_code_hash
      `{H' : State.Trait}
      {E: Set}
      `{ink_env.types.Environment.Trait E}
      :
      (mut_ref Self) -> (M (H := H') (ink_env.error.Result E::type["Hash"]));
    call_runtime
      `{H' : State.Trait}
      {E Call: Set}
      `{ink_env.types.Environment.Trait E}
      `{parity_scale_codec.codec.Encode.Trait Call}
      :
      (mut_ref Self) -> (ref Call) -> (M (H := H') (ink_env.error.Result unit));
  }.
  
  Global Instance Method_caller `{H' : State.Trait} `(Trait)
    : Notation.Dot "caller" := {
    Notation.dot {E : Set} `{ink_env.types.Environment.Trait E} := caller;
  }.
  Global Instance Method_transferred_value `{H' : State.Trait} `(Trait)
    : Notation.Dot "transferred_value" := {
    Notation.dot {E : Set} `{ink_env.types.Environment.Trait E}
      :=
      transferred_value;
  }.
  Global Instance Method_weight_to_fee `{H' : State.Trait} `(Trait)
    : Notation.Dot "weight_to_fee" := {
    Notation.dot {E : Set} `{ink_env.types.Environment.Trait E}
      :=
      weight_to_fee;
  }.
  Global Instance Method_gas_left `{H' : State.Trait} `(Trait)
    : Notation.Dot "gas_left" := {
    Notation.dot {E : Set} `{ink_env.types.Environment.Trait E} := gas_left;
  }.
  Global Instance Method_block_timestamp `{H' : State.Trait} `(Trait)
    : Notation.Dot "block_timestamp" := {
    Notation.dot {E : Set} `{ink_env.types.Environment.Trait E}
      :=
      block_timestamp;
  }.
  Global Instance Method_account_id `{H' : State.Trait} `(Trait)
    : Notation.Dot "account_id" := {
    Notation.dot {E : Set} `{ink_env.types.Environment.Trait E} := account_id;
  }.
  Global Instance Method_balance `{H' : State.Trait} `(Trait)
    : Notation.Dot "balance" := {
    Notation.dot {E : Set} `{ink_env.types.Environment.Trait E} := balance;
  }.
  Global Instance Method_block_number `{H' : State.Trait} `(Trait)
    : Notation.Dot "block_number" := {
    Notation.dot {E : Set} `{ink_env.types.Environment.Trait E} := block_number;
  }.
  Global Instance Method_minimum_balance `{H' : State.Trait} `(Trait)
    : Notation.Dot "minimum_balance" := {
    Notation.dot {E : Set} `{ink_env.types.Environment.Trait E}
      :=
      minimum_balance;
  }.
  Global Instance Method_emit_event `{H' : State.Trait} `(Trait)
    : Notation.Dot "emit_event" := {
    Notation.dot
      {E Event : Set}
      `{ink_env.types.Environment.Trait E}
      `{ink_env.topics.Topics.Trait Event}
      `{parity_scale_codec.codec.Encode.Trait Event}
      :=
      emit_event;
  }.
  Global Instance Method_invoke_contract `{H' : State.Trait} `(Trait)
    : Notation.Dot "invoke_contract" := {
    Notation.dot
      {E Args R : Set}
      `{ink_env.types.Environment.Trait E}
      `{parity_scale_codec.codec.Encode.Trait Args}
      `{parity_scale_codec.codec.Decode.Trait R}
      :=
      invoke_contract;
  }.
  Global Instance Method_invoke_contract_delegate `{H' : State.Trait} `(Trait)
    : Notation.Dot "invoke_contract_delegate" := {
    Notation.dot
      {E Args R : Set}
      `{ink_env.types.Environment.Trait E}
      `{parity_scale_codec.codec.Encode.Trait Args}
      `{parity_scale_codec.codec.Decode.Trait R}
      :=
      invoke_contract_delegate;
  }.
  Global Instance Method_instantiate_contract `{H' : State.Trait} `(Trait)
    : Notation.Dot "instantiate_contract" := {
    Notation.dot
      {E ContractRef Args Salt R : Set}
      `{ink_env.types.Environment.Trait E}
      `{ink_env.call.create_builder.FromAccountId.Trait ContractRef (T := E)}
      `{parity_scale_codec.codec.Encode.Trait Args}
      `{core.convert.AsRef.Trait Salt (T := Slice u8)}
      `{ink_env.call.create_builder.ConstructorReturnType.Trait R
          (C := ContractRef)}
      :=
      instantiate_contract;
  }.
  Global Instance Method_terminate_contract `{H' : State.Trait} `(Trait)
    : Notation.Dot "terminate_contract" := {
    Notation.dot {E : Set} `{ink_env.types.Environment.Trait E}
      :=
      terminate_contract;
  }.
  Global Instance Method_transfer `{H' : State.Trait} `(Trait)
    : Notation.Dot "transfer" := {
    Notation.dot {E : Set} `{ink_env.types.Environment.Trait E} := transfer;
  }.
  Global Instance Method_is_contract `{H' : State.Trait} `(Trait)
    : Notation.Dot "is_contract" := {
    Notation.dot {E : Set} `{ink_env.types.Environment.Trait E} := is_contract;
  }.
  Global Instance Method_caller_is_origin `{H' : State.Trait} `(Trait)
    : Notation.Dot "caller_is_origin" := {
    Notation.dot {E : Set} `{ink_env.types.Environment.Trait E}
      :=
      caller_is_origin;
  }.
  Global Instance Method_code_hash `{H' : State.Trait} `(Trait)
    : Notation.Dot "code_hash" := {
    Notation.dot {E : Set} `{ink_env.types.Environment.Trait E} := code_hash;
  }.
  Global Instance Method_own_code_hash `{H' : State.Trait} `(Trait)
    : Notation.Dot "own_code_hash" := {
    Notation.dot {E : Set} `{ink_env.types.Environment.Trait E}
      :=
      own_code_hash;
  }.
  Global Instance Method_call_runtime `{H' : State.Trait} `(Trait)
    : Notation.Dot "call_runtime" := {
    Notation.dot
      {E Call : Set}
      `{ink_env.types.Environment.Trait E}
      `{parity_scale_codec.codec.Encode.Trait Call}
      :=
      call_runtime;
  }.
End TypedEnvBackend.""",
        "",
    )
    content = content.replace(
        """Parameter build_call :
    forall `{H' : State.Trait} {E : Set} `{ink_env.types.Environment.Trait E},
    M (H := H')
        (ink_env.call.call_builder.CallBuilder
          E
          (ink_env.call.common.Unset_ (ink_env.call.call_builder.Call E))
          (ink_env.call.common.Unset_
            (ink_env.call.execution_input.ExecutionInput
              ink_env.call.execution_input.EmptyArgumentList))
          (ink_env.call.common.Unset_ (ink_env.call.common.ReturnType unit))).""",
        "",
    )
    content = content.replace(
        """Parameter build_create :
    forall
      `{H' : State.Trait}
      {ContractRef : Set}
      `{ink_env.contract.ContractEnv.Trait ContractRef},
    M (H := H')
        (ink_env.call.create_builder.CreateBuilder
          ink_env.contract.ContractEnv.Env
          ContractRef
          (ink_env.call.common.Unset_ ink_env.types.Environment.Hash)
          (ink_env.call.common.Unset_ u64)
          (ink_env.call.common.Unset_ ink_env.types.Environment.Balance)
          (ink_env.call.common.Unset_
            (ink_env.call.execution_input.ExecutionInput
              ink_env.call.execution_input.EmptyArgumentList))
          (ink_env.call.common.Unset_ ink_env.call.create_builder.state.Salt)
          (ink_env.call.common.Unset_ (ink_env.call.common.ReturnType unit))).""",
        "",
    )
    content = content.replace(
        """
Module state.
  Module IgnoreErrorCode.
""",
        """
Module state_.
  Module IgnoreErrorCode.
""",
    )
    content = \
        content.replace(
            """HandleErrorCode.t (T := T).
End state.
""",
            """HandleErrorCode.t (T := T).
End state_.
""",
        )
    content = content.replace(
        """Module OnInstance.
  Class Trait
      (Self : Set)
        `{ink_env.backend.EnvBackend.Trait Self}
        `{ink_env.backend.TypedEnvBackend.Trait Self} :
      Type := {
    on_instance
      `{H' : State.Trait}
      {F R: Set}
      `{core.ops.function.FnOnce.Trait F (Args := mut_ref Self)}
      :
      F -> (M (H := H') R);
  }.
  
  Global Instance Method_on_instance `{H' : State.Trait} `(Trait)
    : Notation.Dot "on_instance" := {
    Notation.dot
      {F R : Set}
      `{core.ops.function.FnOnce.Trait F (Args := mut_ref Self)}
      :=
      on_instance;
  }.
End OnInstance.""",
        "",
    )
    content = content.replace(
        """Parameter register_chain_extension :
    forall
      `{H' : State.Trait}
      {E : Set}
      `{ink_engine.chain_extension.ChainExtension.Trait E},
    E -> M (H := H') unit.""",
        "",
    )
    content = content.replace(
        """Parameter recorded_debug_messages :
    forall `{H' : State.Trait},
    M (H := H') ink_engine.test_api.RecordedDebugMessages.""",
        "",
    )
    content = content.replace(
        """Parameter is_contract :
    forall
      `{H' : State.Trait}
      {T : Set}
      `{ink_env.types.Environment.Trait T}
      `{core.convert.From.Trait ink_env.types.Environment.AccountId
          (T := list u8)},
    T::type["AccountId"] -> M (H := H') bool.""",
        "",
    )
    content = content.replace(
        """Parameter run_test :
    forall
      `{H' : State.Trait}
      {T F : Set}
      `{ink_env.types.Environment.Trait T}
      `{core.ops.function.FnOnce.Trait F
          (Args := ink_env.engine.off_chain.test_api.DefaultAccounts T)}
      `{core.convert.From.Trait ink_env.types.Environment.AccountId
          (T := list u8)},
    F -> M (H := H') (ink_env.error.Result unit).""",
        "",
    )
    content = content.replace(
        """Parameter default_accounts :
    forall
      `{H' : State.Trait}
      {T : Set}
      `{ink_env.types.Environment.Trait T}
      `{core.convert.From.Trait ink_env.types.Environment.AccountId
          (T := list u8)},
    M (H := H') (ink_env.engine.off_chain.test_api.DefaultAccounts T).""",
        "",
    )
    content = content.replace(
        """Parameter recorded_events_ret_ty :
    forall `{"""
        + "core.iter.traits.iterator.Iterator"
        + """},
    Set.
Parameter recorded_events :
    forall `{H' : State.Trait},
    M (H := H') recorded_events_ret_ty.""",
        "",
    )
    content = content.replace(
        """Module EnvInstance.
  Unset Primitive Projections.
  Record t : Set := {
    engine : ink_engine.ext.Engine;
  }.
  Global Set Primitive Projections.
  
  Global Instance Get_engine : Notation.Dot "engine" := {
    Notation.dot '(Build_t x0) := x0;
  }.
End EnvInstance.""",
        """Module EnvInstance.
  Unset Primitive Projections.
  Record t : Set := {
  }.
  Global Set Primitive Projections.
End EnvInstance.""",
    )
    content = content.replace(
        """Module private.
  Module Sealed.
    Unset Primitive Projections.
    Class Trait (Self : Set) : Type := {
    }.
    Global Set Primitive Projections.
  End Sealed.
End private.""",
        "",
    )
    content = content.replace(
        """Module TopicsBuilder.
  Section TopicsBuilder.
    Context {S E B : Set}.
    Unset Primitive Projections.
    Record t : Set := {
      backend : B;
      state : core.marker.PhantomData (S * E);
    }.
    Global Set Primitive Projections.
    
    Global Instance Get_backend : Notation.Dot "backend" := {
      Notation.dot '(Build_t x0 _) := x0;
    }.
    Global Instance Get_state : Notation.Dot "state" := {
      Notation.dot '(Build_t _ x1) := x1;
    }.
  End TopicsBuilder.
End TopicsBuilder.
Definition TopicsBuilder""",
        "Definition TopicsBuilder_",
    )
    content = content.replace(
        """Module state.
  Module Uninit.
    Inductive t : Set :=
    .
  End Uninit.
  Definition Uninit := Uninit.t.
  
  Module HasRemainingTopics.
    Inductive t : Set :=
    .
  End HasRemainingTopics.
  Definition HasRemainingTopics := HasRemainingTopics.t.
  
  Module NoRemainingTopics.
    Inductive t : Set :=
    .
  End NoRemainingTopics.
  Definition NoRemainingTopics := NoRemainingTopics.t.
End state.""",
        """Module state__.
  Module Uninit.
    Inductive t : Set :=
    .
  End Uninit.
  Definition Uninit := Uninit.t.
  
  Module HasRemainingTopics.
    Inductive t : Set :=
    .
  End HasRemainingTopics.
  Definition HasRemainingTopics := HasRemainingTopics.t.
  
  Module NoRemainingTopics.
    Inductive t : Set :=
    .
  End NoRemainingTopics.
  Definition NoRemainingTopics := NoRemainingTopics.t.
End state__.""",
    )
    content = \
        content.replace(
            """Definition TopicsBuilder_ (S E B : Set) : Set :=
  TopicsBuilder.t (S := S) (E := E) (B := B).
""",
            "",
        )
    with open(file_name, "w") as f:
        f.write(content)


def sub_exactly_n(pattern, replacement, text, times) -> str:
    regex_flags = re.MULTILINE | re.DOTALL
    matches = list(re.finditer(pattern, text, regex_flags))
    if len(matches) == times:
        return re.sub(
            pattern=pattern,
            repl=replacement,
            string=text,
            flags=regex_flags,
        )
    else:
        raise ValueError(
            f"Pattern {pattern} not found exactly {times} times in text\n"
            + f"It was found {len(matches)} times."
        )


def sub_exactly_once(
    pattern,
    replacement,
    text,
) -> str:
    return sub_exactly_n(pattern, replacement, text, 1)


def update_ink_e2e_macro():
    file_name = "ink_e2e_macro.v"
    with open(file_name, "r") as f:
        content = f.read()
    pattern = "Require Import CoqOfRust.CoqOfRust."
    content = sub_exactly_once(
        pattern,
        pattern
        + """
Require CoqOfRust.ink.proc_macro.
Require CoqOfRust.ink.syn.""",
        content,
    )
    with open(file_name, "w") as f:
        f.write(content)


def update_ink_macro():
    file_name = "ink_macro.v"
    with open(file_name, "r") as f:
        content = f.read()
    pattern = "Require Import CoqOfRust.CoqOfRust."
    content = sub_exactly_once(
        pattern,
        pattern
        + """
Require CoqOfRust.ink.proc_macro.
Require CoqOfRust.ink.proc_macro2.
Require CoqOfRust.ink.syn.
Require CoqOfRust.ink.synstructure.""",
        content,
    )
    content = sub_exactly_once(
        """End storage_item.

Parameter generate""",
        """End storage_item.

(* Parameter generate""",
        content,
    )
    content = sub_exactly_once(
        r"""M \(H := H'\) \(syn.error.Result proc_macro2.TokenStream\).

Module trait_def.""",
        """M (H := H') (syn.error.Result proc_macro2.TokenStream). *)

Module trait_def.""",
        content,
    )
    with open(file_name, "w") as f:
        f.write(content)


def update_ink_primitives():
    file_name = "ink_primitives.v"
    with open(file_name, "r") as f:
        content = f.read()
    # NOTE: Commented out because the generics are being satisfied in newer commits.
    # content = \
    #     sub_exactly_once(
    #         "Definition MessageResult",
    #         "Definition MessageResult (T : Set)",
    #         content,
    #     )
    # content = \
    #     sub_exactly_once(
    #         "Definition ConstructorResult",
    #         "Definition ConstructorResult (T : Set)",
    #         content,
    #     )
    with open(file_name, "w") as f:
        f.write(content)


def update_storage():
    file_name = "ink_storage.v"
    with open(file_name, "r") as f:
        content = f.read()
    pattern = "Require Import CoqOfRust.CoqOfRust."
    content = sub_exactly_once(
        pattern,
        pattern
        + """
Require CoqOfRust.ink.ink_storage_traits.""",
        content,
    )
    with open(file_name, "w") as f:
        f.write(content)


def update_storage_traits():
    file_name = "ink_storage_traits.v"
    with open(file_name, "r") as f:
        content = f.read()
    pattern = "Require Import CoqOfRust.CoqOfRust."
    content = sub_exactly_once(
        pattern,
        pattern
        + """
Require CoqOfRust.ink.ink_metadata.
Require CoqOfRust.ink.ink_primitives.
Require CoqOfRust.ink.parity_scale_codec.""",
        content,
    )
    content = sub_exactly_n(
        "Global Instance Method_key",
        "(* Global Instance Method_key",
        content,
        2,
    )
    content = sub_exactly_n(
        "End StorageKey.",
        "*) End StorageKey.",
        content,
        2,
    )
    with open(file_name, "w") as f:
        f.write(content)


def update_erc20():
    file_name = "erc20.v"
    with open(file_name, "r") as f:
        content = f.read()
    pattern = "Require Import CoqOfRust.CoqOfRust."
    content = sub_exactly_once(
        pattern,
        pattern
        + """

Require CoqOfRust.ink.ink_storage.
Require CoqOfRust.ink.ink_env.
""",
        content,
    )

    for field in ("total_supply", "balances", "allowances"):
        content = sub_exactly_n(
            f"{field} : ink_storage_traits.storage.AutoStorableHint.Type_",
            f"{field} `{{ink_storage_traits.storage.AutoStorableHint.Trait}} : ink_storage_traits.storage.AutoStorableHint.Type_",
            content,
            2,
        )
    with open(file_name, "w") as f:
        f.write(content)


update_ink_e2e_macro()
update_ink_env()
update_ink_macro()
update_ink_primitives()
update_storage_traits()
update_storage()
update_erc20()
