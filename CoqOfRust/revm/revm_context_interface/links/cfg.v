Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import CoqOfRust.revm.links.dependencies.

(*
  /// Create scheme.
  #[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
  #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
  pub enum CreateScheme {
      /// Legacy create scheme of `CREATE`.
      Create,
      /// Create scheme of `CREATE2`.
      Create2 {
          /// Salt.
          salt: U256,
      },
  }
*)

Module CreateScheme.
  Inductive t : Set :=
  | Create
  | Create2 : U256.t -> t.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_primitives::env::CreateScheme";
    φ x :=
      match x with
      | Create => Value.StructTuple "revm_primitives::env::CreateScheme::Create" []
      | Create2 x => Value.StructTuple "revm_primitives::env::CreateScheme::Create2" [φ x]
      end;
  }.
End CreateScheme.

Locate Pointer.Kind.Ref.

(* 
#[auto_impl(&, &mut, Box, Arc)]
pub trait Cfg {
    type Spec: Into<SpecId> + Clone;

    fn chain_id(&self) -> u64;

    // Specification id that is set.
    fn spec(&self) -> Self::Spec;

    /// Returns the blob target and max count for the given spec id.
    ///
    /// EIP-7840: Add blob schedule to execution client configuration files
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
  (* TODO: refer to `InterpreterTypes`'s definition to translate types *)
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

  (* fn set_instruction_result(&mut self, result: InstructionResult);
    Definition Run_set_instruction_result (Self : Set) `{Link Self} : Set :=
    {set_instruction_result @
      IsTraitMethod.t "revm_interpreter::interpreter_types::LoopControl" [] [] (Φ Self) "set_instruction_result" set_instruction_result *
      forall (self : Ref.t Pointer.Kind.MutRef Self) (result : InstructionResult.t),
        {{ set_instruction_result [] [] [ φ self; φ result ] 🔽 unit }}
    }.
  *)
  Definition Run_chain_id (Self : Set) `{Link Self} : Set :=
    {chain_id @
      IsTraitMethod.t "revm_context_interface::cfg::Cfg" [] [] (Φ Self) "chain_id" chain_id *
      forall (self : Ref.t Pointer.Kind.Ref Self),
        {{ chain_id [] [] [ φ self ] 🔽 U64.t }}
    }.

  Record Run (Self : Set) `{Link Self} (types : Types.t) 
    `{Types.AreLinks types} : Set := 
  {
    Spec_IsAssociated :
      IsTraitAssociatedType
        "revm_context_interface::cfg::Cfg" [] [] (Φ Self)
        "Spec" (Φ types.(Types.Spec));
    (* run_StackTrait_for_Stack : StackTrait.Run types.(Types.Stack); *) (* TODO: Do we need to implement `Into` for Spec? *)
    chain_id : Run_chain_id Self;
  }.
End Cfg.