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
            "IsResultType",
            "TraitCallForwarderFor",
        ],
        content,
    )
    content = sub_at_least_once(
        re.escape(
            "Definition IsResultType (T : Set) : Set := IsResultType.t (T := T)."
        ),
        "",
        content,
    )

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
    content = content.replace(
        """
Module Error.
  Inductive t : Set :=
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
Definition Error := Error.t.
""",
        "",
    )

    content = sub_at_least_once(
        "core.hash.Hash.hash `{H' : State.Trait} := hash;",
        "core.hash.Hash.hash `{H' : State.Trait} (__H : Set) `{H' : core.hash.Hasher.Trait __H} := hash (__H := __H);",
        content,
    )

    content = ignore_module_names(
        [
            "Impl_core_iter_traits_collect_IntoIterator_for_ink_engine_test_api_RecordedDebugMessages",
            "Impl_core_convert_From_for_ink_engine_ext_Result",
            "Impl_parity_scale_codec_codec_Encode_for_ink_engine_chain_extension_ExtensionId",
            "Impl_parity_scale_codec_encode_like_EncodeLike_for_ink_engine_chain_extension_ExtensionId",
            "Impl_parity_scale_codec_codec_Decode_for_ink_engine_chain_extension_ExtensionId",
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

Require CoqOfRust.ink.alloc.
Require CoqOfRust.ink.ink_primitives.
Require CoqOfRust.ink.ink_storage_traits.
Require CoqOfRust.ink.parity_scale_codec.
Require CoqOfRust.ink.scale_decode.
Require CoqOfRust.ink.scale_encode.
Require CoqOfRust.ink.ink_engine.""",
        content,
    )
    content = content.replace(
        """
Parameter build_create :
    forall
      `{H' : State.Trait}
      {ContractRef : Set}
      `{ink_env.contract.ContractEnv.Trait ContractRef},
    M (H := H')
        (ink_env.call.create_builder.CreateBuilder
          (ink_env.contract.ContractEnv.Env (Self := ContractRef))
          ContractRef
          (ink_env.call.common.Unset_
            (ink_env.types.Environment.Hash
              (Self := ink_env.contract.ContractEnv.Env (Self := ContractRef))))
          (ink_env.call.common.Unset_ u64)
          (ink_env.call.common.Unset_
            (ink_env.types.Environment.Balance
              (Self := ink_env.contract.ContractEnv.Env (Self := ContractRef))))
          (ink_env.call.common.Unset_
            (ink_env.call.execution_input.ExecutionInput
              ink_env.call.execution_input.EmptyArgumentList))
          (ink_env.call.common.Unset_ ink_env.call.create_builder.state.Salt)
          (ink_env.call.common.Unset_ (ink_env.call.common.ReturnType unit))).
""",
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
        """Parameter is_contract :
    forall
      `{H' : State.Trait}
      {T : Set}
      `{ink_env.types.Environment.Trait T}
      `{core.convert.From.Trait
            (ink_env.types.Environment.AccountId (Self := T))
          (T := list u8)},
    T::type["AccountId"] -> M (H := H') bool.""",
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
    Global Instance Get_AF_backend : Notation.DoubleColon t "backend" := {
      Notation.double_colon '(Build_t x0 _) := x0;
    }.
    Global Instance Get_state : Notation.Dot "state" := {
      Notation.dot '(Build_t _ x1) := x1;
    }.
    Global Instance Get_AF_state : Notation.DoubleColon t "state" := {
      Notation.double_colon '(Build_t _ x1) := x1;
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


def update_ink_e2e_macro():
    file_name = "ink_e2e_macro.v"
    with open(file_name, "r") as f:
        content = f.read()
    pattern = "Require Import CoqOfRust.CoqOfRust."
    content = sub_at_least_once(
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
        "core.hash.Hash.hash `{H' : State.Trait} := hash;",
        "core.hash.Hash.hash `{H' : State.Trait} (__H : Set) `{H' : core.hash.Hasher.Trait __H} := hash (__H := __H);",
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
        "Global Instance Method_key",
        "(* Global Instance Method_key",
        content,
    )
    content = sub_at_least_once(
        "End StorageKey.",
        "*) End StorageKey.",
        content,
    )

    content = sub_at_least_once(
        "Global Instance I",
        "Global Instance I'",
        content,
    )
    content = sub_at_least_once(
        "Global Hint Resolve I : core.",
        "Global Hint Resolve I' : core.",
        content,
    )

    content = ignore_module_names(
        [
            "Impl_ink_storage_traits_storage_Storable_for_P",
            "Impl_ink_storage_traits_storage_StorageKey_for_ink_storage_traits_impls_AutoKey",
            "Impl_ink_storage_traits_storage_StorageKey_for_ink_storage_traits_impls_ManualKey_ParentKey",
            "Impl_ink_storage_traits_storage_StorageKey_for_ink_storage_traits_impls_ResolverKey_L_R",
            "Impl_ink_storage_traits_storage_AutoStorableHint_for_T",
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

    content = sub_at_least_once(
        r"""Module Impl_core_default_Default_for_erc20_erc20_Erc20.
    Definition Self := erc20.erc20.Erc20.""",
        """Module Impl_core_default_Default_for_erc20_erc20_Erc20.
    Definition Self := erc20.erc20.Erc20.

    Global Instance Default_for_AutoStorableHint_Type_ : default.Default.Trait
     (forall (Self Key : Set) (H : ink_storage_traits.storage.StorageKey.Trait Key)
        (H0 : ink_storage_traits.storage.AutoStorableHint.Trait Self),
      H0.(ink_storage_traits.storage.AutoStorableHint.Type_)). Admitted.
""",
        content,
    )

    content = sub_at_least_once(
        r"""  End Erc20.
  Definition Erc20 : Set := Erc20.t.
""",
        r"""    Global Instance Erc20_New `{State.Trait} : Notation.DoubleColon t "new" (T := unit -> M t).
    Admitted.
  End Erc20.
  Definition Erc20 : Set := Erc20.t.
""",
        content,
    )

    content = sub_at_least_once(
        """Module erc20.""",
        """Module erc20.
  Module Impl_ink_env_types_Environment_for_ink_env_types_DefaultEnvironment.
    Definition Self := ink_env.types.DefaultEnvironment.
    
    Definition MAX_EVENT_TOPICS := 4.
    
    Global Instance AssociatedFunction_MAX_EVENT_TOPICS `{H' : State.Trait} :
      Notation.DoubleColon Self "MAX_EVENT_TOPICS" := {
      Notation.double_colon := MAX_EVENT_TOPICS;
    }.
    
    Definition AccountId : Set := ink_primitives.types.AccountId.
    
    Definition Balance : Set := ink_env.types.Balance.
    
    Definition Hash : Set := ink_primitives.types.Hash.
    
    Definition Timestamp : Set := ink_env.types.Timestamp.
    
    Definition BlockNumber : Set := ink_env.types.BlockNumber.
    
    Definition ChainExtension : Set := ink_env.types.NoChainExtension.
    
    #[refine]
    Global Instance I : ink_env.types.Environment.Trait Self := {
      ink_env.types.Environment.MAX_EVENT_TOPICS `{H' : State.Trait}
        :=
        MAX_EVENT_TOPICS;
      ink_env.types.Environment.AccountId := AccountId;
      ink_env.types.Environment.Balance := Balance;
      ink_env.types.Environment.Hash := Hash;
      ink_env.types.Environment.Timestamp := Timestamp;
      ink_env.types.Environment.BlockNumber := BlockNumber;
      ink_env.types.Environment.ChainExtension := ChainExtension;
    }.
    eauto.
    Defined.
    Global Hint Resolve I : core.
  End Impl_ink_env_types_Environment_for_ink_env_types_DefaultEnvironment.
""",
        content,
    )

    content = sub_at_least_once(
        """    Global Instance I : ink_env.contract.ContractEnv.Trait Self := {
      ink_env.contract.ContractEnv.Env := Env;
    }.""",
        """    #[refine]
    Global Instance I : ink_env.contract.ContractEnv.Trait Self := {
      ink_env.contract.ContractEnv.Env := Env;
    }.
    eauto.
    Defined.
    Global Hint Resolve I : core.""",
        content,
    )

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
update_ink_e2e_macro()
update_ink_engine()
update_ink_env()
update_ink_macro()
update_ink_primitives()
update_storage_traits()
update_storage()
update_erc20()
