Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.

Require Import pinocchio.cpi.
Require Import pinocchio.links.instruction.
Require Import pinocchio.links.account_info.
Require Import pinocchio.links.lib.

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
  run_symbolic.
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
