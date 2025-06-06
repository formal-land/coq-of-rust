Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import alloy_primitives.links.aliases.
Require Import core.convert.links.mod.
Require Import revm.revm_specification.links.hardfork.
(*
pub enum CreateScheme {
    Create,
    Create2 {
        salt: U256,
    },
}
*)

Module CreateScheme.
  Inductive t : Set :=
  | Create
  | Create2 : aliases.U256.t -> t.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_context_interface::cfg::CreateScheme";
    φ x :=
      match x with
      | Create => Value.StructTuple "revm_context_interface::cfg::CreateScheme::Create" [] [] []
      | Create2 x =>
        Value.StructRecord "revm_context_interface::cfg::CreateScheme::Create2" [] [] [
          ("salt", φ x)
        ]
      end;
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_context_interface::cfg::CreateScheme").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.

  Lemma of_value_with_Create :
    Value.StructTuple "revm_context_interface::cfg::CreateScheme::Create" [] [] [] = φ Create.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_Create : of_value.

  Lemma of_value_with_Create2 (x : aliases.U256.t) x' :
    x' = φ x ->
    Value.StructRecord "revm_context_interface::cfg::CreateScheme::Create2" [] [] [
      ("salt", x')
    ] = φ (Create2 x).
  Proof. now intros; subst. Qed.
  Smpl Add eapply of_value_with_Create2 : of_value.

  Definition of_value_Create :
    OfValue.t (Value.StructTuple "revm_context_interface::cfg::CreateScheme::Create" [] [] []).
  Proof. eapply OfValue.Make; apply of_value_with_Create. Defined.
  Smpl Add apply of_value_Create : of_value.

  Definition of_value_Create2 (x : aliases.U256.t) x' :
    x' = φ x ->
    OfValue.t (Value.StructRecord "revm_context_interface::cfg::CreateScheme::Create2" [] [] [
      ("salt", x')
    ]).
  Proof. intros; eapply OfValue.Make with (A := t); apply of_value_with_Create2; eassumption. Defined.
  Smpl Add eapply of_value_Create2 : of_value.
End CreateScheme.

(* 
#[auto_impl(&, &mut, Box, Arc)]
pub trait Cfg {
    type Spec: Into<SpecId> + Clone;

    fn chain_id(&self) -> u64;
    fn spec(&self) -> Self::Spec;
    fn blob_max_count(&self, spec_id: SpecId) -> u8;
    fn max_code_size(&self) -> usize;
    fn is_eip3607_disabled(&self) -> bool;
    fn is_balance_check_disabled(&self) -> bool;
    fn is_block_gas_limit_disabled(&self) -> bool;
    fn is_nonce_check_disabled(&self) -> bool;
    fn is_base_fee_check_disabled(&self) -> bool;
}
*)
Module Cfg.
  (* type Spec: Into<SpecId> + Clone; *)
  Module Types.
    Record t : Type := {
      Spec : Set;
    }.

    Class AreLinks (types : t) : Set := {
      H_Spec : Link types.(Spec);
    }.

    Global Instance IsLinkSpec (types : t) (H : AreLinks types) : Link types.(Spec) :=
      H.(H_Spec _).
  End Types.

  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("revm_context_interface::cfg::Cfg", [], [], Φ Self).

  Definition Run_chain_id (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "chain_id" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self ] U64.t
    ).

  Definition Run_spec (Self : Set) `{Link Self} (types : Types.t) `{Types.AreLinks types} : Set :=
    TraitMethod.C (trait Self) "spec" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self ] types.(Types.Spec)
    ).

  Definition Run_blob_max_count (Self : Set) `{Link Self} (types : Types.t) `{Types.AreLinks types} : Set :=
    TraitMethod.C (trait Self) "blob_max_count" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self] U8.t
    ).

  Definition Run_max_code_size (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "max_code_size" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self] Usize.t
    ).

  Definition Run_is_eip3607_disabled (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "is_eip3607_disabled" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self] bool
    ).

  Definition Run_is_balance_check_disabled (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "is_balance_check_disabled" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self] bool
    ).

  Definition Run_is_block_gas_limit_disabled (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "is_block_gas_limit_disabled" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self] bool
    ).

  Definition Run_is_nonce_check_disabled (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "is_nonce_check_disabled" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self] bool
    ).

  Definition Run_is_base_fee_check_disabled (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "is_base_fee_check_disabled" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self] bool
    ).

  Class Run (Self : Set) `{Link Self} (types : Types.t)  `{Types.AreLinks types} : Set :=
  {
    Spec_IsAssociated :
      IsTraitAssociatedType
        "revm_context_interface::cfg::Cfg" [] [] (Φ Self)
        "Spec" (Φ types.(Types.Spec));
    run_Into_for_Spec : Into.Run types.(Types.Spec) SpecId.t;
    chain_id : Run_chain_id Self;
    spec : Run_spec Self types;
    blob_max_count : Run_blob_max_count Self types;
    max_code_size : Run_max_code_size Self;
    is_eip3607_disabled : Run_is_eip3607_disabled Self;
    is_balance_check_disabled : Run_is_balance_check_disabled Self;
    is_block_gas_limit_disabled : Run_is_block_gas_limit_disabled Self;
    is_nonce_check_disabled : Run_is_nonce_check_disabled Self;
    is_base_fee_check_disabled : Run_is_base_fee_check_disabled Self;
  }.
End Cfg.

(*
pub trait CfgGetter {
    type Cfg: Cfg;

    fn cfg(&self) -> &Self::Cfg;
}
*)
Module CfgGetter.
  Module Types.
    Record t : Type := {
      Cfg : Set;
      Spec : Set;
    }.

    Class AreLinks (types : t) : Set := {
      H_Cfg : Link types.(Cfg);
      H_Spec : Link types.(Spec);
    }.

    Global Instance IsLinkCfg (types : t) (H : AreLinks types) : Link types.(Cfg) :=
      H.(H_Cfg _).

    Global Instance IsLinkSpec (types : t) (H : AreLinks types) : Link types.(Spec) :=
      H.(H_Spec _).

    Definition to_Cfg_types (types : t) : Cfg.Types.t :=
      {|
        Cfg.Types.Spec := types.(Spec);
      |}.

    Global Instance AreLinks_to_Cfg_types (types : t) (H : AreLinks types) :
      Cfg.Types.AreLinks (to_Cfg_types types) :=
      {|
        Cfg.Types.H_Spec := _;
      |}.
  End Types.

  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("revm_context_interface::cfg::CfgGetter", [], [], Φ Self).

  Definition Run_cfg (Self : Set) `{Link Self} (types : Types.t) `{Types.AreLinks types} : Set :=
    TraitMethod.C (trait Self) "cfg" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self] (Ref.t Pointer.Kind.Ref types.(Types.Cfg))
    ).

  Record Run (Self : Set) `{Link Self} (types : Types.t) `{Types.AreLinks types} : Set :=
  {
    Cfg_IsAssociated :
      IsTraitAssociatedType
        "revm_context_interface::cfg::CfgGetter" [] [] (Φ Self)
        "Cfg" (Φ types.(Types.Cfg));
    run_Cfg_for_Cfg : Cfg.Run types.(Types.Cfg) (Types.to_Cfg_types types);
    cfg : Run_cfg Self types;
  }.
End CfgGetter.
