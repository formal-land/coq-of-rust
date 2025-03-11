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
(* 
  Definition Run_set_instruction_result (Self : Set) `{Link Self} : Set :=
    {set_instruction_result @
      IsTraitMethod.t "revm_interpreter::interpreter_types::LoopControl" [] [] (Φ Self) "set_instruction_result" set_instruction_result *
      forall (self : Ref.t Pointer.Kind.MutRef Self) (result : InstructionResult.t),
        {{ set_instruction_result [] [] [ φ self; φ result ] 🔽 unit }}
    }.

  Record Run (Self : Set) `{Link Self} : Set := {
    set_instruction_result : Run_set_instruction_result Self;
  }.
*)

  Record Run (Self : Set) `{Link Self} : Set := {
  }.

  (* 
  (Primitive.GetTraitMethod "revm_interpreter::interpreter_types::LoopControl"
       (InterpreterTypes.Types.IsLinkControl WIRE_types H2).(Φ _) [] [] "gas" [] [])
  *)

  (* 
  (Primitive.GetTraitMethod "revm_context_interface::cfg::Cfg"
       (Ty.associated_in_trait "revm_context_interface::cfg::CfgGetter" [] []
          H1.(Φ _) "Cfg") [] [] "chain_id" [] [])
  *)


End Cfg.