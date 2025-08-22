Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.links.result.
Require Import pinocchio.links.program_error.

Require Import pinocchio.lib.
Import lib.

Instance run_SUCCESS :
  Run.Trait
  value_SUCCESS [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor.
  run_symbolic.
Defined.

Instance run_MAX_TX_ACCOUNTS :
  Run.Trait
    value_MAX_TX_ACCOUNTS [] [] []
    (Ref.t Pointer.Kind.Raw Usize.t).
Proof. 
    constructor. 
    run_symbolic. 
    + admit.
    + admit.
    + admit.
Admitted.

Instance run_BPF_ALIGN_OF_U128 :
  Run.Trait
    value_BPF_ALIGN_OF_U128 [] [] []
    (Ref.t Pointer.Kind.Raw Usize.t).
Proof. constructor. run_symbolic. Defined.

Instance run_NON_DUP_MARKER :
  Run.Trait
    value_NON_DUP_MARKER [] [] []
    (Ref.t Pointer.Kind.Raw U8.t).
Proof. constructor. run_symbolic. 
    + admit.
    + admit.
    + admit.
Admitted.

Module ProgramResult.
    Definition t : Set :=
      Result.t unit program_error.ProgramError.t.
End ProgramResult.