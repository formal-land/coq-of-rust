Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.ops.links.deref.
Require Import pinocchio.log.
Require Import pinocchio.links.account_info.
Require Import pinocchio.links.pubkey.

Instance run_sol_log
  (message : Ref.t Pointer.Kind.Ref (list (Integer.t IntegerKind.U8))) :
  Run.Trait
    log.sol_log
    [] []
    [φ message]
    unit.
Proof.
  constructor.
  admit.
Admitted.

Instance run_sol_log_64
  (arg1 arg2 arg3 arg4 arg5 : U64.t) :
  Run.Trait
    log.sol_log_64
    [] []
    [φ arg1; φ arg2; φ arg3; φ arg4; φ arg5]
    unit.
Proof.
  constructor.
  admit.
Admitted.

Instance run_sol_log_data
  (data : Ref.t Pointer.Kind.Ref (list (list (Integer.t IntegerKind.U8)))) :
  Run.Trait
    log.sol_log_data
    [] []
    [φ data]
    unit.
Proof.
  constructor.
  admit.
Admitted.

Instance run_sol_log_slice
  (slice : Ref.t Pointer.Kind.Ref (list (Integer.t IntegerKind.U8))) :
  Run.Trait
    log.sol_log_slice
    [] []
    [φ slice]
    unit.
Proof.
  constructor.
  admit.
Admitted.

Instance run_sol_log_params
  (accounts : Ref.t Pointer.Kind.Ref (list AccountInfo.t))
  (data : Ref.t Pointer.Kind.Ref (list (Integer.t IntegerKind.U8))) :
  Run.Trait
    log.sol_log_params
    [] []
    [φ accounts; φ data]
    unit.
Proof.
  constructor.
  admit.
Admitted.

Instance run_sol_log_compute_units :
  Run.Trait
    log.sol_log_compute_units
    [] [] []
    unit.
Proof.
  constructor.
  admit.
Admitted.
