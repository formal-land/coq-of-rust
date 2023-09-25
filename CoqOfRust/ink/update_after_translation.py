"""
In this file we apply a list of manual updates to the translated Rust files.
"""
import re


def update_ink():
    file_name = "ink.v"
    with open(file_name, "r") as f:
        content = f.read()
    pattern = "Require Import CoqOfRust.CoqOfRust."
    content = sub_exactly_once(
        pattern,
        pattern
        + """
Require CoqOfRust.ink.ink_env.""",
        content,
    )
    content = sub_exactly_n(
        "Module TraitCallForwarderFor.",
        "(* Module TraitCallForwarderFor.",
        content,
        4,
    )
    content = sub_exactly_n(
        "End TraitCallForwarderFor.",
        "End TraitCallForwarderFor. *)",
        content,
        4,
    )
    content = sub_exactly_once(
        """End ChainExtension.

Module IsResultType.""",
        """End ChainExtension.

(* Module IsResultType.""",
        content,
    )
    content = sub_exactly_once(
        """End IsResultType.

Module Output.""",
        """End IsResultType. *)

Module Output.""",
        content,
    )
    with open(file_name, "w") as f:
        f.write(content)


def update_ink_engine():
    file_name = "ink_engine.v"
    with open(file_name, "r") as f:
        content = f.read()
    pattern = "Require Import CoqOfRust.CoqOfRust."
    content = sub_exactly_once(
        pattern,
        pattern
        + """

Require CoqOfRust.ink.parity_scale_codec.""",
        content,
    )
    # the part below removes a duplicated module that caused a name conflict
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
    with open(file_name, "w") as f:
        f.write(content)


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
Require CoqOfRust.ink.ink.""",
        content,
    )

    # for field in ("total_supply", "balances", "allowances"):
    #     content = sub_exactly_n(
    #         f"{field} : ink_storage_traits.storage.AutoStorableHint.Type_",
    #         f"{field} `{{ink_storage_traits.storage.AutoStorableHint.Trait}} : ink_storage_traits.storage.AutoStorableHint.Type_",
    #         content,
    #         2,
    #     )

    content = sub_exactly_once(
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

    content = sub_exactly_once(
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

    content = sub_exactly_once(
        """    Definition Env : Set := ink_env.types.DefaultEnvironment.""",
        """    Definition Env : Set := ink_env.types.DefaultEnvironment.

    Global Instance Impl_Environment_for_Env : ink_env.types.Environment.Trait Env. Admitted.
    Global Hint Resolve Impl_Environment_for_Env : core.""",
        content,
    )

    content = sub_exactly_once(
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

    with open(file_name, "w") as f:
        f.write(content)


update_ink()
update_ink_e2e_macro()
update_ink_engine()
update_ink_env()
update_ink_macro()
update_ink_primitives()
update_storage_traits()
update_storage()
update_erc20()
