Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.

Require Import pinocchio.cpi.

Instance run_MAX_CPI_ACCOUNTS :
  Run.Trait
  cpi.value_MAX_CPI_ACCOUNTS [] [] []
    (Ref.t Pointer.Kind.Raw Usize.t).
Proof.
  constructor.
  run_symbolic.
Defined.

