"""
In this file we apply a list of manual updates to the translated Rust files.
"""
import re


def sub_at_least_once(pattern, replacement, text) -> str:
    regex_flags = re.MULTILINE | re.DOTALL
    matches = list(re.finditer(pattern, text, regex_flags))
    if len(matches) >= 1:
        return re.sub(
            pattern=pattern,
            repl=replacement,
            string=text,
            flags=regex_flags,
        )
    else:
        raise ValueError(f"Pattern {pattern} not found in text")


def ignore_module_names(module_names, content):
    for module_name in module_names:
        content = sub_at_least_once(
            fr"Module\s+{module_name}\.",
            f"(* Module {module_name}.",
            content,
        )
        try:
            content = sub_at_least_once(
                fr"Section\s+{module_name}\.",
                f"(* Section {module_name}.",
                content,
            )
        except ValueError:
            pass
        content = sub_at_least_once(
            fr"End\s+{module_name}\.",
            f"End {module_name}. *)",
            content,
        )
    return content


def update_ink():
    file_name = "ink.v"
    with open(file_name, "r") as f:
        content = f.read()

    pattern = "Require Import CoqOfRust.CoqOfRust."
    content = sub_at_least_once(
        pattern,
        pattern
        + """
Require CoqOfRust.ink.ink_env.""",
        content,
    )

    content = ignore_module_names(
        [
            "TraitCallForwarderFor",
            "Impl_ink_chain_extension_Output_for_ink_chain_extension_ValueReturned",
        ],
        content,
    )
#     content = sub_at_least_once(
#         re.escape(
#             """Definition IsResultType (T : Set) `{ℋ : State.Trait} : Set :=
#     M.val (IsResultType.t (T := T))."""
#         ),
#         "",
#         content,
#     )
#     content = sub_at_least_once(
#         re.escape("""Definition IsResultType (T : Set) `{ℋ : State.Trait} : Set :=
#   M.val (IsResultType.t (T := T))."""),
#         """(* Definition IsResultType (T : Set) `{ℋ : State.Trait} : Set :=
#   M.val (IsResultType.t (T := T)). *)""",
#         content,
#     )

    with open(file_name, "w") as f:
        f.write(content)


def update_ink_allocator():
    file_name = "ink_allocator.v"
    with open(file_name, "r") as f:
        content = f.read()

    content = ignore_module_names(
        [
            "Impl_core_fmt_Debug_for_ink_allocator_bump_InnerAlloc",
            "Impl_core_marker_Copy_for_ink_allocator_bump_InnerAlloc",
            "Impl_core_clone_Clone_for_ink_allocator_bump_InnerAlloc",
        ],
        content,
    )

    with open(file_name, "w") as f:
        f.write(content)


def update_ink_engine():
    file_name = "ink_engine.v"
    with open(file_name, "r") as f:
        content = f.read()
    pattern = "Require Import CoqOfRust.CoqOfRust."
    content = sub_at_least_once(
        pattern,
        pattern
        + """

Require CoqOfRust.ink.parity_scale_codec.""",
        content,
    )
    content = sub_at_least_once(
        re.escape("""
Module Error.
  Inductive t `{ℋ : State.Trait} : Set :=
  | CalleeTrapped
  | CalleeReverted
  | KeyNotFound
  | _BelowSubsistenceThreshold
  | TransferFailed
  | _EndowmentTooLow
  | CodeNotFound
  | NotCallable
  | LoggingDisabled
  | EcdsaRecoveryFailed
  | Unknown.
End Error.
Definition Error `{ℋ : State.Trait} : Set := Error.t.
"""),
        "",
        content,
    )

    content = sub_at_least_once(
        re.escape(
            "Definition Dyn_ink_engine_chain_extension_ChainExtension : Set :="),
        "Parameter Dyn_ink_engine_chain_extension_ChainExtension : Set.",
        content,
    )
    content = sub_at_least_once(
        re.escape("Dyn_ink_engine_chain_extension_ChainExtension.t."),
        "",
        content,
    )

    content = ignore_module_names(
        [
            "Impl_core_iter_traits_collect_IntoIterator_for_ink_engine_test_api_RecordedDebugMessages",
            "Impl_core_convert_From_for_ink_engine_ext_Result",
            "Impl_parity_scale_codec_codec_Encode_for_ink_engine_chain_extension_ExtensionId",
            "Impl_parity_scale_codec_encode_like_EncodeLike_for_ink_engine_chain_extension_ExtensionId",
            "Impl_parity_scale_codec_codec_Decode_for_ink_engine_chain_extension_ExtensionId",
            "Dyn_ink_engine_chain_extension_ChainExtension",
        ],
        content,
    )

    with open(file_name, "w") as f:
        f.write(content)


def update_ink_env():
    file_name = "ink_env.v"
    with open(file_name, "r") as f:
        content = f.read()
    pattern = "Require Import CoqOfRust.CoqOfRust."
    content = sub_at_least_once(
        pattern,
        pattern
        + """
Require CoqOfRust.num_traits.

Require CoqOfRust.ink.ink_primitives.
Require CoqOfRust.ink.ink_storage_traits.
Require CoqOfRust.ink.parity_scale_codec.
Require CoqOfRust.ink.scale_decode.
Require CoqOfRust.ink.scale_encode.
Require CoqOfRust.ink.ink_engine.""",
        content,
    )

    content = sub_at_least_once(
        re.escape("Parameter recorded_events_ret_ty :"),
        "(* Parameter recorded_events_ret_ty :",
        content,
    )
    content = sub_at_least_once(
        re.escape("M (projT1 recorded_events_ret_ty)."),
        "M (projT1 recorded_events_ret_ty). *)",
        content,
    )

    content = sub_at_least_once(
        re.escape("ink_env.call.create_builder.CreateBuilder"),
        "ink_env.call.create_builder.CreateBuilder (ℋ_0 := ltac:(sauto lq: on))",
        content,
    )

    content = sub_at_least_once(
        re.escape("Trait T (Rhs := Self)"),
        "Trait T (Rhs := T)",
        content,
    )

    content = sub_at_least_once(
        re.escape("""End TopicsBuilderBackend.

Module TopicsBuilder."""),
        """End TopicsBuilderBackend.

(* Module TopicsBuilder.""",
        content,
    )
    content = sub_at_least_once(
        re.escape("""\n  M.val (TopicsBuilder.t (S := S) (E := E) (B := B))."""),
        """\n  M.val (TopicsBuilder.t (S := S) (E := E) (B := B)). *)""",
        content,
    )

    content = sub_at_least_once(
        re.escape("""Parameter is_contract :
    forall
      `{ℋ : State.Trait}
      {E : Set}
      {ℋ_0 : ink_env.types.Environment.Trait E},
    (ref E::type["AccountId"]) -> M bool."""),
        """(* Parameter is_contract :
    forall
      `{ℋ : State.Trait}
      {E : Set}
      {ℋ_0 : ink_env.types.Environment.Trait E},
    (ref E::type["AccountId"]) -> M bool. *)""",
        content)

    content = sub_at_least_once(
        re.escape("""Parameter build_create :
    forall
      `{ℋ : State.Trait}
      {ContractRef : Set}
      {ℋ_0 : ink_env.contract.ContractEnv.Trait ContractRef},
    M
        (ink_env.call.create_builder.CreateBuilder (ℋ_0 := ltac:(sauto lq: on))
          (ink_env.contract.ContractEnv.Env
            (Self := ContractRef)
            (Trait := ltac:(try clear Trait; hauto l: on)))
          ContractRef
          (ink_env.call.common.Unset_
            (ink_env.types.Environment.Hash
              (Self := ink_env.contract.ContractEnv.Env
                (Self := ContractRef)
                (Trait := ltac:(try clear Trait; hauto l: on)))
              (Trait := ltac:(try clear Trait; hauto l: on))))
          (ink_env.call.common.Unset_ u64)
          (ink_env.call.common.Unset_
            (ink_env.types.Environment.Balance
              (Self := ink_env.contract.ContractEnv.Env
                (Self := ContractRef)
                (Trait := ltac:(try clear Trait; hauto l: on)))
              (Trait := ltac:(try clear Trait; hauto l: on))))
          (ink_env.call.common.Unset_
            (ink_env.call.execution_input.ExecutionInput
              ink_env.call.execution_input.EmptyArgumentList))
          (ink_env.call.common.Unset_ ink_env.call.create_builder.state.Salt)
          (ink_env.call.common.Unset_ (ink_env.call.common.ReturnType unit)))."""),
        "",
        content,
    )

    content = sub_at_least_once(
        re.escape("""Parameter hash :
              (ref (Slice u8)) ->
                (mut_ref
                  (ink_env.hash.HashOutput.Type_
                    (Self := Self)
                    (Trait := ltac:(try clear Trait; hauto l: on))))
                ->
                M unit."""),
        """Parameter hash :
              (ref (Slice u8)) ->
                (mut_ref
                  (ink_env.hash.HashOutput.Type_
                    (Self := Self)
                    (Trait := _)))
                ->
                M unit.""",
        content,
    )

    content = sub_at_least_once(
        re.escape("""Parameter hash :
            (ref (Slice u8)) ->
              (mut_ref
                (ink_env.hash.HashOutput.Type_
                  (Self := Self)
                  (Trait := ltac:(try clear Trait; hauto l: on))))
              ->
              M unit."""),
        """Parameter hash :
            (ref (Slice u8)) ->
              (mut_ref
                (ink_env.hash.HashOutput.Type_
                  (Self := Self)
                  (Trait := _)))
              ->
              M unit.""",
        content,
    )

    content = sub_at_least_once(
        re.escape("""Parameter hash :
          (ref (Slice u8)) ->
            (mut_ref
              (ink_env.hash.HashOutput.Type_
                (Self := Self)
                (Trait := ltac:(try clear Trait; hauto l: on))))
            ->
            M unit."""),
        """Parameter hash :
          (ref (Slice u8)) ->
            (mut_ref
              (ink_env.hash.HashOutput.Type_
                (Self := Self)
                (Trait := _)))
            ->
            M unit.""",
        content,
    )

    content = sub_at_least_once(
        re.escape("""Parameter hash :
        (ref (Slice u8)) ->
          (mut_ref
            (ink_env.hash.HashOutput.Type_
              (Self := Self)
              (Trait := ltac:(try clear Trait; hauto l: on))))
          ->
          M unit."""),
        """Parameter hash :
        (ref (Slice u8)) ->
          (mut_ref
            (ink_env.hash.HashOutput.Type_
              (Self := Self)
              (Trait := _)))
          ->
          M unit.""",
        content
    )

    content = ignore_module_names(
        [
            "Impl_core_convert_From_for_ink_env_backend_and_call_builder_and_engine_and_engine_test_api_and_error_Error",
            "Impl_ink_env_topics_TopicsBuilderBackend_for_ink_env_engine_off_chain_impls_TopicsBuilder",
            "Impl_ink_env_backend_and_call_builder_and_engine_and_engine_test_api_and_error_EnvBackend_for_ink_env_engine_off_chain_EnvInstance",
            "Impl_ink_env_backend_and_call_builder_and_engine_and_engine_test_api_and_error_TypedEnvBackend_for_ink_env_engine_off_chain_EnvInstance",
            "Impl_core_convert_From_for_ink_env_backend_and_call_builder_and_engine_and_engine_test_api_and_error_EmittedEvent",
            "Impl_core_convert_From_for_ink_env_engine_off_chain_AccountError",
            "Impl_ink_env_backend_and_call_builder_and_engine_and_engine_test_api_and_error_OnInstance_for_ink_env_engine_off_chain_EnvInstance",
            "Impl_core_convert_From_for_ink_env_topics_TopicsBuilder_ink_env_topics_state_Uninit_E_B",
            "Impl_ink_env_topics_EventTopicsAmount_for_Array_ink_env_topics_state_HasRemainingTopics",
            "Impl_ink_env_topics_SomeRemainingTopics_for_Array_ink_env_topics_state_HasRemainingTopics",
        ],
        content,
    )

    with open(file_name, "w") as f:
        f.write(content)


def update_ink_e2e():
    file_name = "ink_e2e.v"
    with open(file_name, "r") as f:
        content = f.read()
    pattern = "Require Import CoqOfRust.CoqOfRust."
    content = sub_at_least_once(
        pattern,
        pattern
        + """
Require CoqOfRust.ink.ink_env.
Require CoqOfRust.ink.pallet_contracts_primitives.
Require CoqOfRust.ink.primitive_types.
Require CoqOfRust.ink.serde.
Require CoqOfRust.ink.sp_core.
Require CoqOfRust.ink.sp_keyring.
Require CoqOfRust.ink.subxt.""",
        content,
    )

    content = sub_at_least_once(
        re.escape(
            """Definition CreateBuilderPartial
      `{ℋ : State.Trait} (E ContractRef Args R : Set) :
      Set :="""),
        """Definition CreateBuilderPartial
      `{ℋ : State.Trait} (E ContractRef Args R : Set)
      `{ink_env.types.Environment.Trait E} :
      Set :=""",
        content,
    )
    content = sub_at_least_once(
        re.escape(
            """Definition CallBuilderFinal `{ℋ : State.Trait} (E Args RetType : Set) : Set :="""
        ),
        """Definition CallBuilderFinal `{ℋ : State.Trait} (E Args RetType : Set) `{ink_env.types.Environment.Trait E} : Set :=""",
        content,
    )

    content = ignore_module_names(
        [
            "Impl_core_fmt_Debug_for_ink_e2e_client_ContractInstantiatedEvent_E",
            "Impl_scale_encode_EncodeAsType_for_ink_e2e_client_ContractInstantiatedEvent_E",
            "Impl_scale_encode_EncodeAsFields_for_ink_e2e_client_ContractInstantiatedEvent_E",
            "Impl_subxt_events_StaticEvent_for_ink_e2e_client_ContractInstantiatedEvent_E",
            "Impl_parity_scale_codec_codec_Decode_for_ink_e2e_client_ContractInstantiatedEvent_E",
            "Impl_parity_scale_codec_codec_Encode_for_ink_e2e_client_ContractInstantiatedEvent_E",
            "Impl_parity_scale_codec_encode_like_EncodeLike_for_ink_e2e_client_ContractInstantiatedEvent_E",
            "Impl_scale_decode_IntoVisitor_for_ink_e2e_client_ContractInstantiatedEvent_E",
            "Impl_scale_decode_visitor_Visitor_for_ink_e2e_client___Visitor_E",
            "Impl_scale_decode_DecodeAsFields_for_ink_e2e_client_ContractInstantiatedEvent_E",
            "Impl_core_fmt_Debug_for_ink_e2e_client_CodeStoredEvent_E",
            "Impl_scale_encode_EncodeAsType_for_ink_e2e_client_CodeStoredEvent_E",
            "Impl_scale_encode_EncodeAsFields_for_ink_e2e_client_CodeStoredEvent_E",
            "Impl_subxt_events_StaticEvent_for_ink_e2e_client_CodeStoredEvent_E",
            "Impl_parity_scale_codec_codec_Decode_for_ink_e2e_client_CodeStoredEvent_E",
            "Impl_parity_scale_codec_codec_Encode_for_ink_e2e_client_CodeStoredEvent_E",
            "Impl_parity_scale_codec_encode_like_EncodeLike_for_ink_e2e_client_CodeStoredEvent_E",
            "Impl_scale_decode_IntoVisitor_for_ink_e2e_client_CodeStoredEvent_E",
            "Impl_scale_decode_DecodeAsFields_for_ink_e2e_client_CodeStoredEvent_E",
            "Impl_core_ops_drop_Drop_for_ink_e2e_node_proc_TestNodeProcess_R",
            "Impl_parity_scale_codec_max_encoded_len_MaxEncodedLen_for_ink_e2e_xts_Weight",
            "Impl_serde_de_Visitor_for_ink_e2e_xts___deserialize___FieldVisitor",
            "Impl_serde_de_Deserialize_for_ink_e2e_xts___deserialize___Field",
            "Impl_serde_de_Visitor_for_ink_e2e_xts___deserialize___Visitor",
            "Impl_serde_ser_Serialize_for_ink_e2e_xts_RpcInstantiateRequest_C_E",
            "Impl_parity_scale_codec_codec_Encode_for_ink_e2e_xts_RpcInstantiateRequest_C_E",
            "Impl_parity_scale_codec_encode_like_EncodeLike_for_ink_e2e_xts_RpcInstantiateRequest_C_E",
            "Impl_serde_ser_Serialize_for_ink_e2e_xts_RpcCodeUploadRequest_C_E",
            "Impl_parity_scale_codec_codec_Encode_for_ink_e2e_xts_RpcCodeUploadRequest_C_E",
            "Impl_parity_scale_codec_encode_like_EncodeLike_for_ink_e2e_xts_RpcCodeUploadRequest_C_E",
            "Impl_serde_ser_Serialize_for_ink_e2e_xts_RpcCallRequest_C_E",
            "Impl_parity_scale_codec_codec_Encode_for_ink_e2e_xts_RpcCallRequest_C_E",
            "Impl_parity_scale_codec_encode_like_EncodeLike_for_ink_e2e_xts_RpcCallRequest_C_E",
            "Impl_serde_ser_Serialize_for_ink_e2e_xts_Code",
            "Impl_parity_scale_codec_codec_Encode_for_ink_e2e_xts_Code",
            "Impl_parity_scale_codec_encode_like_EncodeLike_for_ink_e2e_xts_Code",
        ],
        content,
    )

    with open(file_name, "w") as f:
        f.write(content)


def update_ink_e2e_macro():
    file_name = "ink_e2e_macro.v"
    with open(file_name, "r") as f:
        content = f.read()
    pattern = "Require Import CoqOfRust.CoqOfRust."
    content = sub_at_least_once(
        pattern,
        pattern
        + """
Require CoqOfRust.ink.ink_ir.
Require CoqOfRust.ink.proc_macro.
Require CoqOfRust.ink.syn.""",
        content,
    )

    content = ignore_module_names(
        [
            "Impl_core_fmt_Debug_for_ink_e2e_macro_codegen_ContractManifests",
        ],
        content,
    )

    content = sub_at_least_once(
        re.escape("""M unit.

Module InkE2ETest."""),
        """M unit.

(* Module InkE2ETest.""",
        content,
    )
    content = sub_at_least_once(
        re.escape("""Definition InkE2ETest `{ℋ : State.Trait} : Set := M.val InkE2ETest.t.

Module Impl_core_convert_From_for_ink_e2e_macro_codegen_InkE2ETest."""),
        """Definition InkE2ETest `{ℋ : State.Trait} : Set := M.val InkE2ETest.t. *)

Module Impl_core_convert_From_for_ink_e2e_macro_codegen_InkE2ETest.""",
        content,
    )

    with open(file_name, "w") as f:
        f.write(content)


def update_ink_macro():
    file_name = "ink_macro.v"
    with open(file_name, "r") as f:
        content = f.read()
    pattern = "Require Import CoqOfRust.CoqOfRust."
    content = sub_at_least_once(
        pattern,
        pattern
        + """
Require CoqOfRust.ink.proc_macro.
Require CoqOfRust.ink.proc_macro2.
Require CoqOfRust.ink.syn.
Require CoqOfRust.ink.synstructure.""",
        content,
    )
    content = sub_at_least_once(
        """End storage_item.

Parameter generate""",
        """End storage_item.

(* Parameter generate""",
        content,
    )
    content = sub_at_least_once(
        re.escape("""M (syn.error.Result proc_macro2.TokenStream).

Module trait_def."""),
        """M (syn.error.Result proc_macro2.TokenStream). *)

Module trait_def.""",
        content,
    )
    with open(file_name, "w") as f:
        f.write(content)


def update_ink_primitives():
    file_name = "ink_primitives.v"
    with open(file_name, "r") as f:
        content = f.read()
    pattern = "Require Import CoqOfRust.CoqOfRust."
    content = sub_at_least_once(
        pattern,
        pattern
        + """
Require CoqOfRust.ink.parity_scale_codec.
Require CoqOfRust.ink.scale_encode.
Require CoqOfRust.ink.scale_info.""",
        content,
    )

    content = sub_at_least_once(
        """End Impl_core_convert_AsMut_for_ink_primitives_types_AccountId.
  
  Module Impl_core_convert_AsRef_for_ink_primitives_types_AccountId.""",
        """End Impl_core_convert_AsMut_for_ink_primitives_types_AccountId.
  
  (* Module Impl_core_convert_AsRef_for_ink_primitives_types_AccountId.""",
        content,
    )

    content = sub_at_least_once(
        """End Impl_core_convert_AsMut_for_ink_primitives_types_AccountId.
  
  Module Impl_core_convert_TryFrom_for_ink_primitives_types_AccountId.""",
        """End Impl_core_convert_AsMut_for_ink_primitives_types_AccountId. *)
  
  Module Impl_core_convert_TryFrom_for_ink_primitives_types_AccountId.""",
        content,
    )

    content = ignore_module_names(
        [
            "Impl_ink_primitives_types_Clear_for_Array_u8",
            "Impl_ink_primitives_types_Clear_for_ink_primitives_types_Hash",
            "Impl_scale_decode_IntoVisitor_for_ink_primitives_types_AccountId",
            "Impl_scale_decode_visitor_Visitor_for_ink_primitives_types___Visitor",
            "Impl_scale_decode_DecodeAsFields_for_ink_primitives_types_AccountId",
            "Impl_parity_scale_codec_codec_Decode_for_ink_primitives_types_AccountId",
            "Impl_parity_scale_codec_codec_Encode_for_ink_primitives_types_AccountId",
            "Impl_parity_scale_codec_encode_like_EncodeLike_for_ink_primitives_types_AccountId",
            "Impl_core_convert_AsRef_for_ink_primitives_types_AccountId",
            "Impl_core_convert_AsMut_for_ink_primitives_types_AccountId",
            "Impl_scale_decode_IntoVisitor_for_ink_primitives_types_Hash",
            "Impl_scale_decode_visitor_Visitor_for_ink_primitives_types___Visitor",
            "Impl_scale_decode_DecodeAsFields_for_ink_primitives_types_Hash",
            "Impl_parity_scale_codec_codec_Decode_for_ink_primitives_types_Hash",
            "Impl_parity_scale_codec_codec_Encode_for_ink_primitives_types_Hash",
            "Impl_parity_scale_codec_encode_like_EncodeLike_for_ink_primitives_types_Hash",
            "Impl_parity_scale_codec_codec_Encode_for_ink_primitives_LangError",
            "Impl_parity_scale_codec_encode_like_EncodeLike_for_ink_primitives_LangError",
            "Impl_parity_scale_codec_codec_Decode_for_ink_primitives_LangError",
        ],
        content,
    )

    with open(file_name, "w") as f:
        f.write(content)


def update_storage():
    file_name = "ink_storage.v"
    with open(file_name, "r") as f:
        content = f.read()
    pattern = "Require Import CoqOfRust.CoqOfRust."
    content = sub_at_least_once(
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
    content = sub_at_least_once(
        pattern,
        pattern
        + """
Require CoqOfRust.ink.ink_metadata.
Require CoqOfRust.ink.ink_primitives.
Require CoqOfRust.ink.parity_scale_codec.""",
        content,
    )

    content = sub_at_least_once(
        r"\w+ :: core.marker.Sized.Trait Self;",
        "(* _ :: core.marker.Sized.Trait Self; *)",
        content,
    )

    content = ignore_module_names(
        [
            "Impl_ink_storage_traits_storage_Storable_for_P",
            "Impl_ink_storage_traits_storage_StorageKey_for_ink_storage_traits_impls_AutoKey",
            "Impl_ink_storage_traits_storage_StorageKey_for_ink_storage_traits_impls_ManualKey_ParentKey",
            "Impl_ink_storage_traits_storage_StorageKey_for_ink_storage_traits_impls_ResolverKey_L_R",
            "Impl_ink_storage_traits_storage_Packed_for_P",
            "Impl_ink_storage_traits_storage_StorageKey_for_P",
            "Impl_ink_storage_traits_storage_StorableHint_for_P",
            "Impl_ink_storage_traits_layout_StorageLayout_for_alloc_collections_btree_map_BTreeMap_K_V_alloc_collections_btree_map_BTreeMap_Default_A",
            "Impl_ink_storage_traits_layout_StorageLayout_for_alloc_collections_btree_set_BTreeSet_T_alloc_collections_btree_set_BTreeSet_Default_A",
            "Impl_ink_storage_traits_layout_StorageLayout_for_alloc_collections_vec_deque_VecDeque_T_alloc_collections_vec_deque_VecDeque_Default_A",
        ],
        content,
    )

    with open(file_name, "w") as f:
        f.write(content)


def update_erc20():
    file_name = "erc20.v"
    with open(file_name, "r") as f:
        content = f.read()
    pattern = "Require Import CoqOfRust.CoqOfRust."
    content = sub_at_least_once(
        pattern,
        pattern
        + """

Require CoqOfRust.ink.ink_storage.
Require CoqOfRust.ink.ink_env.
Require CoqOfRust.ink.ink.""",
        content,
    )

#     content = sub_at_least_once(
#         r"""Module Impl_core_default_Default_for_erc20_erc20_Erc20.
#     Definition Self `{ℋ : State.Trait} := erc20.erc20.Erc20.""",
#         """Module Impl_core_default_Default_for_erc20_erc20_Erc20.
#     Definition Self `{ℋ : State.Trait} := erc20.erc20.Erc20.

#     Global Instance Default_for_AutoStorableHint_Type_ : default.Default.Trait
#      (forall (Self Key : Set) (H : ink_storage_traits.storage.StorageKey.Trait Key)
#         (H0 : ink_storage_traits.storage.AutoStorableHint.Trait Self),
#       H0.(ink_storage_traits.storage.AutoStorableHint.Type_)). Admitted.
# """,
#         content,
#     )

#     content = sub_at_least_once(
#         re.escape("""  End Erc20.
#   Definition Erc20 `{ℋ : State.Trait} : Set := M.val (Erc20.t).
# """),
#         """    Global Instance Erc20_New `{ℋ : State.Trait} : Notation.DoubleColon t "new" (T := unit -> M t).
#     Admitted.
#   End Erc20.
#   Definition Erc20 `{ℋ : State.Trait} : Set := M.val (Erc20.t).
# """,
#         content,
#     )

#     content = sub_at_least_once(
#         """Module erc20.""",
#         """Module erc20.
#   Module Impl_ink_env_types_Environment_for_ink_env_types_DefaultEnvironment.
#     Definition Self := ink_env.types.DefaultEnvironment.

#     Definition MAX_EVENT_TOPICS := 4.

#     Global Instance AssociatedFunction_MAX_EVENT_TOPICS `{H' : State.Trait} :
#       Notation.DoubleColon Self "MAX_EVENT_TOPICS" := {
#       Notation.double_colon := MAX_EVENT_TOPICS;
#     }.

#     Definition AccountId : Set := ink_primitives.types.AccountId.

#     Definition Balance : Set := ink_env.types.Balance.

#     Definition Hash : Set := ink_primitives.types.Hash.

#     Definition Timestamp : Set := ink_env.types.Timestamp.

#     Definition BlockNumber : Set := ink_env.types.BlockNumber.

#     Definition ChainExtension : Set := ink_env.types.NoChainExtension.

#     #[refine]
#     Global Instance I : ink_env.types.Environment.Trait Self := {
#       ink_env.types.Environment.MAX_EVENT_TOPICS `{H' : State.Trait}
#         :=
#         MAX_EVENT_TOPICS;
#       ink_env.types.Environment.AccountId := AccountId;
#       ink_env.types.Environment.Balance := Balance;
#       ink_env.types.Environment.Hash := Hash;
#       ink_env.types.Environment.Timestamp := Timestamp;
#       ink_env.types.Environment.BlockNumber := BlockNumber;
#       ink_env.types.Environment.ChainExtension := ChainExtension;
#     }.
#     eauto.
#     Defined.
#     Global Hint Resolve I : core.
#   End Impl_ink_env_types_Environment_for_ink_env_types_DefaultEnvironment.
# """,
#         content,
#     )

    content = sub_at_least_once(
        re.escape(
            "ink_env.contract.ContractEnv.Env (Self := erc20.erc20.Erc20)"
        ),
        "ink_env.types.DefaultEnvironment",
        content,
    )

    with open(file_name, "w") as f:
        f.write(content)


update_ink()
update_ink_allocator()
update_ink_e2e()
update_ink_e2e_macro()
update_ink_engine()
update_ink_env()
update_ink_macro()
update_ink_primitives()
update_storage_traits()
update_storage()
update_erc20()
