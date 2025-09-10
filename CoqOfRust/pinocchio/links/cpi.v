Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.mem.links.maybe_uninit.

Require Import pinocchio.cpi.
Require Import pinocchio.links.instruction.
Require Import pinocchio.links.account_info.
Require Import pinocchio.links.lib.
Require Import pinocchio.links.pubkey.

Instance run_MAX_CPI_ACCOUNTS :
  Run.Trait
  cpi.value_MAX_CPI_ACCOUNTS [] [] []
    (Ref.t Pointer.Kind.Raw Usize.t).
Proof.
  constructor.
  run_symbolic.
Defined.

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

Instance run_MAX_RETURN_DATA :
  Run.Trait
  cpi.value_MAX_RETURN_DATA [] [] []
    (Ref.t Pointer.Kind.Raw Usize.t).
Proof.
  constructor.
  run_symbolic.
Defined.

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

