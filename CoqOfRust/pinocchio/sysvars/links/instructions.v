Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.

Require Import pinocchio.links.account_info.
Require Import pinocchio.links.instruction.  
Require Import pinocchio.links.program_error.
Require Import pinocchio.links.pubkey.

Require Import pinocchio.sysvars.instructions.

Require Import core.ops.links.deref.
Require Import core.convert.links.mod.
Require Import core.links.result.

Module instruction.

  (*
    pub struct Instructions<T: Deref<Target=[u8]>> { data: T }
    We monomorphize to a concrete carrier that just stores the byte slice.
  *)
  Module Instructions.
    Record t (T : Set) : Set := { data : T}.

    Global Instance IsLink (T : Set) `{Link T} : Link (t T) := {
      Φ := Ty.path "pinocchio::sysvars::instruction::Instructions";
      φ x :=
        Value.StructRecord "pinocchio::sysvars::instruction::Instructions" [] [] [
          ("data", φ x.(data T))
        ];
    }.
  End Instructions.

  (*
    #[repr(C)]
    pub struct IntrospectedInstruction<'a> { raw: *const u8, marker: PhantomData<&'a [u8]> }
    We keep the phantom as unit to avoid depending on PhantomData.
  *)
  Module IntrospectedInstruction.
    Record t : Set := {
      raw : Ref.t Pointer.Kind.Raw U8.t;
      marker : unit
    }.

    Global Instance IsLink : Link t := {
      Φ := Ty.path "pinocchio::sysvars::instruction::IntrospectedInstruction";
      φ x :=
        Value.StructRecord "pinocchio::sysvars::instruction::IntrospectedInstruction" [] [] [
          ("raw", φ x.(raw));
          ("marker", Value.Tuple [])
        ];
    }.
  End IntrospectedInstruction.

  (*
    #[repr(C)]
    pub struct IntrospectedAccountMeta { flags: u8, key: Pubkey }
  *)
  Module IntrospectedAccountMeta.
    Record t : Set := {
      flags : U8.t;
      key : Pubkey.t
    }.

    Global Instance IsLink : Link t := {
      Φ := Ty.path "pinocchio::sysvars::instruction::IntrospectedAccountMeta";
      φ x :=
        Value.StructRecord "pinocchio::sysvars::instruction::IntrospectedAccountMeta" [] [] [
          ("flags", φ x.(flags));
          ("key", φ x.(key))
        ];
    }.
  End IntrospectedAccountMeta.

  Instance run_IS_SIGNER :
    Run.Trait
    pinocchio.sysvars.instructions.sysvars.instructions.value_IS_SIGNER
      [] [] []
      (Ref.t Pointer.Kind.Raw U8.t).
  Proof.
    constructor. run_symbolic.
  Defined.

  Instance run_IS_WRITABLE :
    Run.Trait
    pinocchio.sysvars.instructions.sysvars.instructions.value_IS_WRITABLE
      [] [] []
      (Ref.t Pointer.Kind.Raw U8.t).
  Proof.
    constructor. run_symbolic.
  Defined.

  (*
    pub const INSTRUCTIONS_ID: Pubkey = [...]
  *)
  Instance run_INSTRUCTIONS_ID :
    Run.Trait
    pinocchio.sysvars.instructions.sysvars.instructions.value_INSTRUCTIONS_ID
      [] [] []
      (Ref.t Pointer.Kind.Raw Pubkey.t).
  Proof.
    constructor. admit.
  Admitted.
  (*
    impl<T> Instructions<T> { unsafe fn new_unchecked(data: T) -> Self { ... } ... }
    We expose methods on our monomorphized Instructions.t
  *)
  Module Impl_Instructions.
    Definition Self (T : Set) : Set := Instructions.t T.
    
  Instance run_new_unchecked
    {T : Set} `{Link T}
    (run_Deref_for_T : Deref.Run T (list (Integer.t IntegerKind.U8)))
    (data : T) :
  Run.Trait
  (sysvars.instructions.Impl_pinocchio_sysvars_instructions_Instructions_T.new_unchecked ((Φ T)))
    [] 
    [] 
    [φ data]
    (Instructions.t T).
Proof.
  constructor.
  run_symbolic.
  - admit.
  - admit.
Admitted.
End Impl_Instructions.
  (*  
    Instance run_load_current_index
      (self : Ref.t Pointer.Kind.Ref Self) :
      Run.Trait
      pinocchio.sysvars.instructions.sysvars.instructions.Impl_pinocchio_sysvars_instructions_Instructions_T.load_current_index
        [] [] [ φ self ]
        U16.t.
    Proof.
      constructor. run_symbolic. admit.
    Admitted.
    

    Instance run_deserialize_instruction_unchecked
      (self : Ref.t Pointer.Kind.Ref Self)
      (index : Usize.t) :
      Run.Trait
      pinocchio.sysvars.instructions.sysvars.instructions.Impl_pinocchio_sysvars_instructions_Instructions_T.deserialize_instruction_unchecked
        [] [] [ φ self; φ index ]
        IntrospectedInstruction.t.
    Proof.
      constructor. run_symbolic. admit.
    Admitted.

    Instance run_load_instruction_at
      (self : Ref.t Pointer.Kind.Ref Self)
      (index : Usize.t) :
      Run.Trait
        instruction.instruction.Impl_pinocchio_sysvars_instruction_Instructions.load_instruction_at
        [] [] [ φ self; φ index ]
        (Result.t IntrospectedInstruction.t ProgramError.t).
    Proof.
      constructor. run_symbolic. admit.
    Admitted.

    Instance run_get_instruction_relative
      (self : Ref.t Pointer.Kind.Ref Self)
      (index_rel : I64.t) :
      Run.Trait
        instruction.instruction.Impl_pinocchio_sysvars_instruction_Instructions.get_instruction_relative
        [] [] [ φ self; φ index_rel ]
        (Result.t IntrospectedInstruction.t ProgramError.t).
    Proof.
      constructor. run_symbolic. admit.
    Admitted.
  End Impl_Instructions.
  *)
  (*
    impl<'a> TryFrom<&'a AccountInfo> for Instructions<Ref<'a,[u8]>>

  Module Impl_TryFrom_ref_AccountInfo_for_Instructions.
    Definition Self : Set := Instructions.t.

    Definition run_try_from :
      TryFrom.Run_try_from (Ref.t Pointer.Kind.Ref AccountInfo.t)
                           (Result.t Self ProgramError.t).
    Proof.
      eexists.
      { eapply IsTraitMethod.Defined.
        { apply instruction.instruction.Impl_core_convert_TryFrom_ref__pinocchio_account_info_AccountInfo_for_pinocchio_sysvars_instruction_Instructions.Implements. }
        { reflexivity. } }
      { constructor. admit. }
    Admitted.

    Instance run :
      TryFrom.Run (Ref.t Pointer.Kind.Ref AccountInfo.t) (Result.t Self ProgramError.t) :=
      { TryFrom.try_from := run_try_from }.
  End Impl_TryFrom_ref_AccountInfo_for_Instructions.

  
    impl IntrospectedInstruction { methods ... }
  
  Module Impl_IntrospectedInstruction.
    Definition Self : Set := IntrospectedInstruction.t.
    
    Instance run_get_account_meta_at_unchecked
      (self : Ref.t Pointer.Kind.Ref Self)
      (index : Usize.t) :
      Run.Trait
      pinocchio.sysvars.instructions.sysvars.instructions.Impl_core_cmp_Eq_for_pinocchio_sysvars_instructions_IntrospectedInstruction
      .get_account_meta_at_unchecked
        [] [] [ φ self; φ index ]
        (Ref.t Pointer.Kind.Ref IntrospectedAccountMeta.t).
    Proof.
      constructor. run_symbolic. admit.
    Admitted.

    Instance run_get_account_meta_at
      (self : Ref.t Pointer.Kind.Ref Self)
      (index : Usize.t) :
      Run.Trait
        instruction.instruction.Impl_pinocchio_sysvars_instruction_IntrospectedInstruction.get_account_meta_at
        [] [] [ φ self; φ index ]
        (Result.t (Ref.t Pointer.Kind.Ref IntrospectedAccountMeta.t) ProgramError.t).
    Proof.
      constructor. run_symbolic. admit.
    Admitted.

    Instance run_get_program_id
      (self : Ref.t Pointer.Kind.Ref Self) :
      Run.Trait
        instruction.instruction.Impl_pinocchio_sysvars_instruction_IntrospectedInstruction.get_program_id
        [] [] [ φ self ]
        (Ref.t Pointer.Kind.Ref Pubkey.t).
    Proof.
      constructor. run_symbolic. admit.
    Admitted.

    Instance run_get_instruction_data
      (self : Ref.t Pointer.Kind.Ref Self) :
      Run.Trait
        instruction.instruction.Impl_pinocchio_sysvars_instruction_IntrospectedInstruction.get_instruction_data
        [] [] [ φ self ]
        (list (Integer.t IntegerKind.U8)).
    Proof.
      constructor. run_symbolic. admit.
    Admitted.
  End Impl_IntrospectedInstruction.

  (*
    impl IntrospectedAccountMeta { is_writable, is_signer, to_account_meta }
  *)
  Module Impl_IntrospectedAccountMeta.
    Definition Self : Set := IntrospectedAccountMeta.t.

    Instance run_is_writable
      (self : Ref.t Pointer.Kind.Ref Self) :
      Run.Trait
        instruction.instruction.Impl_pinocchio_sysvars_instruction_IntrospectedAccountMeta.is_writable
        [] [] [ φ self ]
        bool.
    Proof.
      constructor. run_symbolic. admit.
    Admitted.

    Instance run_is_signer
      (self : Ref.t Pointer.Kind.Ref Self) :
      Run.Trait
        instruction.instruction.Impl_pinocchio_sysvars_instruction_IntrospectedAccountMeta.is_signer
        [] [] [ φ self ]
        bool.
    Proof.
      constructor. run_symbolic. admit.
    Admitted.

    Instance run_to_account_meta
      (self : Ref.t Pointer.Kind.Ref Self) :
      Run.Trait
        instruction.instruction.Impl_pinocchio_sysvars_instruction_IntrospectedAccountMeta.to_account_meta
        [] [] [ φ self ]
        AccountMeta.t.
    Proof.
      constructor. run_symbolic. admit.
    Admitted.
  End Impl_IntrospectedAccountMeta.
*)
End instruction.