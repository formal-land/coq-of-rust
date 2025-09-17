Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.mem.links.maybe_uninit.
Require Import core.ops.links.deref.
Require Import pinocchio.cpi.
Require Import pinocchio.links.instruction.
Require Import pinocchio.links.account_info.
Require Import pinocchio.links.lib.
Require Import pinocchio.links.pubkey.

(*
pub const MAX_CPI_ACCOUNTS: usize = 64;
*)
Instance run_MAX_CPI_ACCOUNTS :
  Run.Trait
  cpi.value_MAX_CPI_ACCOUNTS [] [] []
    (Ref.t Pointer.Kind.Raw Usize.t).
Proof.
  constructor.
  run_symbolic.
Defined.

(*
pub fn invoke<const ACCOUNTS: usize>(
    instruction: &Instruction,
    account_infos: &[&AccountInfo; ACCOUNTS],
) -> ProgramResult {
    invoke_signed::<ACCOUNTS>(instruction, account_infos, &[])
}
*)
Instance run_invoke 
  (ACCOUNTS : Usize.t) 
  (instruction : Ref.t Pointer.Kind.Ref Instruction.t)
  (account_infos : 
    Ref.t Pointer.Kind.Ref (array.t (Ref.t Pointer.Kind.Ref AccountInfo.t) ACCOUNTS)) :
  Run.Trait
    cpi.invoke 
    [φ ACCOUNTS] 
    [] 
    [φ instruction; φ account_infos]
    ProgramResult.t.
Proof.
  constructor.
  admit.
Admitted.

(*
pub fn invoke_with_bounds<const MAX_ACCOUNTS: usize>(
    instruction: &Instruction,
    account_infos: &[&AccountInfo],
) -> ProgramResult {
    invoke_signed_with_bounds::<MAX_ACCOUNTS>(instruction, account_infos, &[])
}
*)
Instance run_invoke_with_bounds
  (MAX_ACCOUNTS : Usize.t)
  (instruction : Ref.t Pointer.Kind.Ref Instruction.t)
  (account_infos :
     Ref.t Pointer.Kind.Ref (array.t (Ref.t Pointer.Kind.Ref AccountInfo.t) MAX_ACCOUNTS)) :
  Run.Trait
    cpi.invoke_with_bounds
    [φ MAX_ACCOUNTS]              
    []                            
    [φ instruction; φ account_infos] 
    ProgramResult.t.
Proof.
  constructor.
  admit.
Admitted.

(*
pub fn slice_invoke(instruction: &Instruction, account_infos: &[&AccountInfo]) -> ProgramResult {
    slice_invoke_signed(instruction, account_infos, &[])
}
*)
Instance run_slice_invoke
  (MAX_CPI_ACCOUNTS : Usize.t)
  (instruction : Ref.t Pointer.Kind.Ref Instruction.t)
  (account_infos :
     Ref.t Pointer.Kind.Ref (array.t (Ref.t Pointer.Kind.Ref AccountInfo.t) MAX_CPI_ACCOUNTS)) :
  Run.Trait
    cpi.slice_invoke
    []
    []
    [φ instruction; φ account_infos]
    ProgramResult.t.
Proof.
  constructor.
  admit.
Admitted.

(*
pub fn invoke_signed<const ACCOUNTS: usize>(
    instruction: &Instruction,
    account_infos: &[&AccountInfo; ACCOUNTS],
    signers_seeds: &[Signer],
) -> ProgramResult { ... }
*)
Instance run_invoke_signed
  (ACCOUNTS : Usize.t)
  (SIGNERS : Usize.t)
  (instruction : Ref.t Pointer.Kind.Ref Instruction.t)
  (account_infos :
     Ref.t Pointer.Kind.Ref (array.t (Ref.t Pointer.Kind.Ref AccountInfo.t) ACCOUNTS))
  (signers_seeds :
     Ref.t Pointer.Kind.Ref (list Signer.t)) :
  Run.Trait
    cpi.invoke_signed
    [φ ACCOUNTS]
    []
    [φ instruction; φ account_infos; φ signers_seeds]
    ProgramResult.t.
Proof.
  constructor.
  admit.
Admitted.

(*
pub fn invoke_signed_with_bounds<const MAX_ACCOUNTS: usize>(
    instruction: &Instruction,
    account_infos: &[&AccountInfo],
    signers_seeds: &[Signer],
) -> ProgramResult {
*)
Instance run_invoke_signed_with_bounds
  (MAX_ACCOUNTS : Usize.t)
  (SIGNERS : Usize.t)
  (instruction : Ref.t Pointer.Kind.Ref Instruction.t)
  (account_infos :
     Ref.t Pointer.Kind.Ref (array.t (Ref.t Pointer.Kind.Ref AccountInfo.t) MAX_ACCOUNTS))
  (signers_seeds :
     Ref.t Pointer.Kind.Ref (array.t Signer.t SIGNERS)) :
  Run.Trait
    cpi.invoke_signed_with_bounds
    [φ MAX_ACCOUNTS]
    []
    [φ instruction; φ account_infos; φ signers_seeds]
    ProgramResult.t.
Proof.
  constructor.
  admit.
Admitted.

(*
pub fn slice_invoke_signed(
    instruction: &Instruction,
    account_infos: &[&AccountInfo],
    signers_seeds: &[Signer],
) -> ProgramResult { ... }
*)
Instance run_slice_invoke_signed
  (MAX_CPI_ACCOUNTS : Usize.t)
  (SIGNERS : Usize.t)
  (instruction : Ref.t Pointer.Kind.Ref Instruction.t)
  (account_infos :
     Ref.t Pointer.Kind.Ref (array.t (Ref.t Pointer.Kind.Ref AccountInfo.t) MAX_CPI_ACCOUNTS))
  (signers_seeds :
     Ref.t Pointer.Kind.Ref (array.t Signer.t SIGNERS)) :
  Run.Trait
    cpi.slice_invoke_signed
    []
    []
    [φ instruction; φ account_infos; φ signers_seeds]
    ProgramResult.t.
Proof.
  constructor.
  admit.
Admitted.

(*
unsafe fn inner_invoke_signed_with_bounds<const MAX_ACCOUNTS: usize>(
    instruction: &Instruction,
    account_infos: &[&AccountInfo],
    signers_seeds: &[Signer],
) -> ProgramResult { ... }
*)
Instance run_inner_invoke_signed_with_bounds
  (MAX_ACCOUNTS : Usize.t)
  (SIGNERS : Usize.t)
  (instruction : Ref.t Pointer.Kind.Ref Instruction.t)
  (account_infos :
     Ref.t Pointer.Kind.Ref (array.t (Ref.t Pointer.Kind.Ref AccountInfo.t) MAX_ACCOUNTS))
  (signers_seeds :
     Ref.t Pointer.Kind.Ref (array.t Signer.t SIGNERS)) :
  Run.Trait
    cpi.inner_invoke_signed_with_bounds
    [φ MAX_ACCOUNTS]
    []
    [φ instruction; φ account_infos; φ signers_seeds]
    ProgramResult.t.
Proof.
  constructor.
  admit.
Admitted.

(*
pub unsafe fn invoke_unchecked(instruction: &Instruction, accounts: &[Account]) {
    invoke_signed_unchecked(instruction, accounts, &[])
}
*)
Instance run_invoke_unchecked
  (ACCOUNTS : Usize.t)
  (instruction : Ref.t Pointer.Kind.Ref Instruction.t)
  (accounts :
     Ref.t Pointer.Kind.Ref (array.t Account.t ACCOUNTS)) :
  Run.Trait
    cpi.invoke_unchecked
    []
    []
    [φ instruction; φ accounts]
    unit.
Proof.
  constructor.
  admit.
Admitted.

(*
pub unsafe fn invoke_signed_unchecked(
    instruction: &Instruction,
    accounts: &[Account],
    signers_seeds: &[Signer],
) {
    ...
  }
*)
Instance run_invoke_signed_unchecked
  (ACCOUNTS : Usize.t)
  (SIGNERS : Usize.t)
  (instruction : Ref.t Pointer.Kind.Ref Instruction.t)
  (accounts :
     Ref.t Pointer.Kind.Ref (array.t Account.t ACCOUNTS))
  (signers_seeds :
     Ref.t Pointer.Kind.Ref (array.t Signer.t SIGNERS)) :
  Run.Trait
    cpi.invoke_signed_unchecked
    []
    []
    [φ instruction; φ accounts; φ signers_seeds]
    unit.
Proof.
  constructor.
  admit.
Admitted.

(* pub fn set_return_data(data: &[u8]) {
    #[cfg(target_os = "solana")]
    unsafe {
        crate::syscalls::sol_set_return_data(data.as_ptr(), data.len() as u64)
    };

    #[cfg(not(target_os = "solana"))]
    core::hint::black_box(data);
}
*)
Instance run_set_return_data
  (N : Usize.t)
  (data : Ref.t Pointer.Kind.Ref (array.t U8.t N)) :
  Run.Trait
    cpi.set_return_data
    []
    []
    [φ data]
    unit.
Proof.
  constructor.
  admit.
Admitted.

(*
pub fn get_return_data() -> Option<ReturnData> {
    ...
}
*)
Instance run_MAX_RETURN_DATA :
  Run.Trait
  cpi.value_MAX_RETURN_DATA [] [] []
    (Ref.t Pointer.Kind.Raw Usize.t).
Proof.
  constructor.
  run_symbolic.
Defined.

(*
pub struct ReturnData {
    program_id: Pubkey,

    data: [MaybeUninit<u8>; MAX_RETURN_DATA],

    size: usize,
}
*)

Module ReturnData.

  Parameter (MAX_RETURN_DATA : Usize.t).

  Record t : Set := {
    program_id : Pubkey.t;
    data : array.t U8.t MAX_RETURN_DATA;
    size : Usize.t
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "pinocchio::cpi::ReturnData";
    φ x :=
      Value.StructRecord "pinocchio::cpi::ReturnData" [] [] [
        ("program_id", φ x.(program_id));
        ("data", φ x.(data));
        ("size", φ x.(size))
      ];
  }.
End ReturnData.

Instance run_get_return_data :
  Run.Trait
    cpi.get_return_data
    []
    []
    []
    (option ReturnData.t).
Proof.
  constructor.
  admit.
Admitted.

(*
impl ReturnData {
    /// Returns the program that most recently set the return data.
    pub fn program_id(&self) -> &Pubkey {
        &self.program_id
    }

    /// Return the data set by the program.
    pub fn as_slice(&self) -> &[u8] {
        unsafe { from_raw_parts(self.data.as_ptr() as _, self.size) }
    }
}
*)
Module Impl_ReturnData.
  Definition Self : Set := ReturnData.t.

  Instance run_program_id
    (self : Ref.t Pointer.Kind.Ref Self) :
    Run.Trait
      pinocchio.cpi.cpi.Impl_pinocchio_cpi_ReturnData.program_id
      [] []
      [ φ self ]
      (Ref.t Pointer.Kind.Ref Pubkey.t).
  Proof.
    constructor.
    run_symbolic.
    admit.
  Admitted.

  Instance run_as_slice
    (self : Ref.t Pointer.Kind.Ref Self) :
    Run.Trait
      pinocchio.cpi.cpi.Impl_pinocchio_cpi_ReturnData.as_slice
      [] []
      [ φ self ]
      (list (Integer.t IntegerKind.U8)).
  Proof.
    constructor.
    run_symbolic.
    admit.
  Admitted.
End Impl_ReturnData.

(* 
impl Deref for ReturnData {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}
*)
Module Impl_Deref_for_ReturnData.

  Definition Self : Set := ReturnData.t.
  
  Definition run_deref
    : Deref.Run_deref Self (list (Integer.t IntegerKind.U8)).
  Proof.
    eexists.
    { eapply IsTraitMethod.Defined.
      { apply pinocchio.cpi.cpi.Impl_core_ops_deref_Deref_for_pinocchio_cpi_ReturnData.Implements. }
      { reflexivity. } }
    { constructor.
      admit. }
  Admitted.

  Instance run
    : Deref.Run ReturnData.t (list (Integer.t IntegerKind.U8)) :=
    { Deref.deref := run_deref }.
End Impl_Deref_for_ReturnData.

