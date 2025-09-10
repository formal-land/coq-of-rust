Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.ops.links.deref.
Require Import core.links.array.
Require Import core.links.marker.
Require Import core.convert.links.mod.
Require Import pinocchio.instruction.
Require Import pinocchio.links.pubkey.
Require Import pinocchio.links.account_info.

(*
pub struct AccountMeta<'a> {
    /// Public key of the account.
    pub pubkey: &'a Pubkey,

    /// Indicates whether the account is writable or not.
    pub is_writable: bool,

    /// Indicates whether the account signed the instruction or not.
    pub is_signer: bool,
}
*)
Module AccountMeta.
  Record t : Set := {
    pubkey : Ref.t Pointer.Kind.Ref Pubkey.t;
    is_writable : bool;
    is_signer : bool;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "pinocchio::instruction::AccountMeta";
    φ x :=
      Value.StructRecord "pinocchio::instruction::AccountMeta" [] [] [
        ("pubkey"     , φ x.(pubkey));
        ("is_writable", φ x.(is_writable));
        ("is_signer"  , φ x.(is_signer))
      ];
  }.

  Definition of_ty : OfTy.t (Ty.path "pinocchio::instruction::AccountMeta").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.
End AccountMeta.

(*
pub struct Instruction<'a, 'b, 'c, 'd>
where
    'a: 'b,
{
    /// Public key of the program.
    pub program_id: &'c Pubkey,

    /// Data expected by the program instruction.
    pub data: &'d [u8],

    /// Metadata describing accounts that should be passed to the program.
    pub accounts: &'b [AccountMeta<'a>],
}
*)
Module Instruction.
  Record t : Set := {
    program_id : Ref.t Pointer.Kind.Ref Pubkey.t;
    data: Ref.t Pointer.Kind.Ref (list U8.t);
    accounts: Ref.t Pointer.Kind.Ref (list AccountMeta.t);
  }.

  Global Instance IsLink : Link t :=
  { Φ := Ty.path "pinocchio::instruction::Instruction";
    φ x :=
      Value.StructRecord "pinocchio::instruction::Instruction" [] [] [
        ("program_id", φ x.(program_id));
        ("data"      , φ x.(data));
        ("accounts"  , φ x.(accounts))
      ];
  }.

  Definition of_ty : OfTy.t (Ty.path "pinocchio::instruction::Instruction").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.
End Instruction.

Module ProcessedSiblingInstruction.
  Record t : Set := {
    data_len     : U64.t;
    accounts_len : U64.t;
  }.

  Global Instance IsLink : Link t :=
  { Φ := Ty.path "pinocchio::instruction::ProcessedSiblingInstruction";
    φ x :=
      Value.StructRecord "pinocchio::instruction::ProcessedSiblingInstruction" [] [] [
        ("data_len"    , φ x.(data_len));
        ("accounts_len", φ x.(accounts_len))
      ];
  }.

  Definition of_ty : OfTy.t (Ty.path "pinocchio::instruction::ProcessedSiblingInstruction").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.
End ProcessedSiblingInstruction.

Module cpi.
  Module Account.
    Record t : Set := {
      key         : Ref.t Pointer.Kind.Raw Pubkey.t;
      lamports    : Ref.t Pointer.Kind.Raw U64.t;
      data_len    : U64.t;
      data        : Ref.t Pointer.Kind.Raw U8.t;
      owner       : Ref.t Pointer.Kind.Raw Pubkey.t;
      rent_epoch  : U64.t;
      is_signer   : bool;
      is_writable : bool;
      executable  : bool;
      _account_info : PhantomData.t (Ref.t Pointer.Kind.Ref AccountInfo.t);
    }.

    Global Instance IsLink : Link t :=
    { Φ := Ty.path "pinocchio::instruction::Account";
      φ x :=
        Value.StructRecord "pinocchio::instruction::Account" [] [] [
          ("key"         , φ x.(key));
          ("lamports"    , φ x.(lamports));
          ("data_len"    , φ x.(data_len));
          ("data"        , φ x.(data));
          ("owner"       , φ x.(owner));
          ("rent_epoch"  , φ x.(rent_epoch));
          ("is_signer"   , φ x.(is_signer));
          ("is_writable" , φ x.(is_writable));
          ("executable"  , φ x.(executable));
          ("_account_info", φ x.(_account_info))
        ];
    }.
  End Account.
End cpi.

Instance run_offset
  (T U : Set) `{Link T} `{Link U} 
  (ptr : Ref.t Pointer.Kind.ConstPointer T) 
  (offset : Usize.t) :
  Run.Trait
    pinocchio.instruction.instruction.offset
    []
    [Φ T; Φ U]
    [ φ (ptr : Ref.t Pointer.Kind.ConstPointer T)
    ; φ (offset : Usize.t)
    ]
    (Ref.t Pointer.Kind.ConstPointer U).
Proof.
  constructor.
  admit.
Admitted.

Module Impl_AccountMeta.
  Definition Self : Set := AccountMeta.t.

  Instance run_new
    (pubkey : Ref.t Pointer.Kind.Ref Pubkey.t)
    (is_writable : bool)
    (is_signer : bool) :
    Run.Trait
    pinocchio.instruction.instruction.Impl_pinocchio_instruction_AccountMeta.new
    [] []
      [ φ pubkey; φ is_writable; φ is_signer ]
      Self.
  Proof.
    constructor.
    run_symbolic.
    admit.
  Admitted.

  Instance run_readonly
    (pubkey : Ref.t Pointer.Kind.Ref Pubkey.t) :
    Run.Trait
    pinocchio.instruction.instruction.Impl_pinocchio_instruction_AccountMeta.readonly
      [] []
      [ φ pubkey ]
      Self.
  Proof.
    constructor.
    run_symbolic.
    admit.
  Admitted.

  Instance run_writable
    (pubkey : Ref.t Pointer.Kind.Ref Pubkey.t) :
    Run.Trait
    pinocchio.instruction.instruction.Impl_pinocchio_instruction_AccountMeta.writable
      [] []
      [ φ pubkey ]
      Self.
  Proof.
    constructor.
    run_symbolic.
    admit.
  Admitted.

  Instance run_readonly_signer
    (pubkey : Ref.t Pointer.Kind.Ref Pubkey.t) :
    Run.Trait
    pinocchio.instruction.instruction.Impl_pinocchio_instruction_AccountMeta.readonly_signer
      [] []
      [ φ pubkey ]
      Self.
  Proof.
    constructor.
    admit.
  Admitted.

  Instance run_writable_signer
    (pubkey : Ref.t Pointer.Kind.Ref Pubkey.t) :
    Run.Trait
    pinocchio.instruction.instruction.Impl_pinocchio_instruction_AccountMeta.writable_signer
      [] []
      [ φ pubkey ]
      Self.
  Proof.
    constructor.
    run_symbolic.
    admit.
  Admitted.
End Impl_AccountMeta.

Module Impl_From_ref_AccountInfo_for_Account.
  Definition run_from : From.Run_from cpi.Account.t (Ref.t Pointer.Kind.Ref AccountInfo.t).
  Proof.
    eexists.
    { eapply IsTraitMethod.Defined.
      { apply pinocchio.instruction.instruction.Impl_core_convert_From_ref__pinocchio_account_info_AccountInfo_for_pinocchio_instruction_Account.Implements. }
      { reflexivity. }
    }
    { constructor. 
      admit.
    }
  Admitted.

  Instance run : From.Run cpi.Account.t (Ref.t Pointer.Kind.Ref AccountInfo.t) :=
    { From.from := run_from }.
End Impl_From_ref_AccountInfo_for_Account.

Global Instance PointeeSized_Run_list (A : Set) `{Link A} :
  PointeeSized.Run (list A) :=
{ dummy_empty_class := tt }.

Module Seed.
  Record t : Set := {
    seed   : Ref.t Pointer.Kind.Raw U8.t;
    len    : U64.t;
    _bytes : PhantomData.t (Ref.t Pointer.Kind.Ref (list U8.t));
  }.

  Global Instance IsLink : Link t :=
  { Φ := Ty.path "pinocchio::instruction::Seed";
    φ x :=
      Value.StructRecord "pinocchio::instruction::Seed" [] [] [
        ("seed"  , φ x.(seed));
        ("len"   , φ x.(len));
        ("_bytes", φ x.(_bytes))
      ];
  }.

  Definition of_ty : OfTy.t (Ty.path "pinocchio::instruction::Seed").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.
End Seed.

Module Impl_From_ref_slice_u8_for_Seed.
  Definition run_from
    : From.Run_from Seed.t (Ref.t Pointer.Kind.Ref (list (Integer.t IntegerKind.U8))).
  Proof.
    eexists.
    { eapply IsTraitMethod.Defined.
      { apply pinocchio.instruction.instruction.Impl_core_convert_From_ref__slice_u8_for_pinocchio_instruction_Seed.Implements. }
      { reflexivity. } }
    { constructor.
      admit. }
  Admitted.

  Instance run
    : From.Run Seed.t (Ref.t Pointer.Kind.Ref (list (Integer.t IntegerKind.U8))) :=
    { From.from := run_from }.
End Impl_From_ref_slice_u8_for_Seed.

Module Impl_From_ref_array_u8_SIZE_for_Seed.
  Definition run_from
    : forall (SIZE : Usize.t),
      From.Run_from Seed.t (Ref.t Pointer.Kind.Ref (array.t (Integer.t IntegerKind.U8) SIZE)).
  Proof.
    intros SIZE.
    eexists.
    { eapply IsTraitMethod.Defined.
      { apply pinocchio.instruction.instruction.Impl_core_convert_From_ref__array_SIZE_u8_for_pinocchio_instruction_Seed.Implements. }
      { reflexivity. } }
    { constructor.
      admit. }
  Admitted.

  Instance run (SIZE : Usize.t)
    : From.Run Seed.t (Ref.t Pointer.Kind.Ref (array.t (Integer.t IntegerKind.U8) SIZE)) :=
    { From.from := run_from SIZE }.
End Impl_From_ref_array_u8_SIZE_for_Seed.

Module Impl_Deref_for_Seed.
  Definition run_deref
    : Deref.Run_deref Seed.t (list (Integer.t IntegerKind.U8)).
  Proof.
    eexists.
    { eapply IsTraitMethod.Defined.
      { apply pinocchio.instruction.instruction.Impl_core_ops_deref_Deref_for_pinocchio_instruction_Seed.Implements. }
      { reflexivity. } }
    { constructor.
      admit. }
  Admitted.

  Instance run
    : Deref.Run Seed.t (list (Integer.t IntegerKind.U8)) :=
    { Deref.deref := run_deref }.
End Impl_Deref_for_Seed.

(*
pub struct Signer<'a, 'b> {
    /// Signer seeds.
    pub(crate) seeds: *const Seed<'a>,

    /// Number of seeds.
    pub(crate) len: u64,

    /// The pointer to the seeds is only valid while the `&'b [Seed<'a>]` lives. Instead
    /// of holding a reference to the actual `[Seed<'a>]`, which would increase the size
    /// of the type, we claim to hold a reference without actually holding one using a
    /// `PhantomData<&'b [Seed<'a>]>`.
    _seeds: PhantomData<&'b [Seed<'a>]>,
}
*)
Module Signer.
  Record t : Set := {
    seeds : Ref.t Pointer.Kind.ConstPointer Seed.t;
    len   : Integer.t IntegerKind.U64;
    _seeds : PhantomData.t (Ref.t Pointer.Kind.Ref (list Seed.t));
  }.

  Global Instance IsLink : Link t :=
  { Φ := Ty.path "pinocchio::instruction::Signer";
    φ x :=
      Value.StructRecord "pinocchio::instruction::Signer" [] [] [
        ("seeds", φ x.(seeds));
        ("len"  , φ x.(len));
        ("_seeds", φ x.(_seeds))
      ];
  }.

  Definition of_ty : OfTy.t (Ty.path "pinocchio::instruction::Signer").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.
End Signer.

Module Impl_From_ref_slice_Seed_for_Signer.
  Definition run_from
    : From.Run_from Signer.t (Ref.t Pointer.Kind.Ref (list Seed.t)).
  Proof.
    eexists.
    { eapply IsTraitMethod.Defined.
      { apply pinocchio.instruction.instruction.Impl_core_convert_From_ref__slice_pinocchio_instruction_Seed_for_pinocchio_instruction_Signer.Implements. }
      { reflexivity. } }
    { constructor.
      admit. }
  Admitted.

  Instance run
    : From.Run Signer.t (Ref.t Pointer.Kind.Ref (list Seed.t)) :=
    { From.from := run_from }.
End Impl_From_ref_slice_Seed_for_Signer.

Module Impl_From_ref_array_Seed_SIZE_for_Signer.
  Definition run_from
    : forall (SIZE : Usize.t),
      From.Run_from Signer.t (Ref.t Pointer.Kind.Ref (array.t Seed.t SIZE)).
  Proof.
    intros SIZE.
    eexists.
    { eapply IsTraitMethod.Defined.
      { apply pinocchio.instruction.instruction.Impl_core_convert_From_ref__array_SIZE_pinocchio_instruction_Seed_for_pinocchio_instruction_Signer.Implements. }
      { reflexivity. } }
    { constructor.
      admit. }
  Admitted.
End Impl_From_ref_array_Seed_SIZE_for_Signer.