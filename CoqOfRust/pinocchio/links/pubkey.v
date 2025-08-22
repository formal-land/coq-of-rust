Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.links.array.
Require Import pinocchio.pubkey.
Require Import core.links.option.
Require Import core.links.result.
Require Import pinocchio.links.program_error.

Import pinocchio.pubkey.pubkey.

Module Pubkey.
  Definition t : Set :=
    array.t U8.t {| Integer.value := 32 |}.

    Global Instance Link_Pubkey : Link Pubkey.t.
    Proof.
      unfold Pubkey.t.
      typeclasses eauto.
    Defined.
End Pubkey.

Instance run_log
      (pubkey : Ref.t Pointer.Kind.Ref Pubkey.t) :
    Run.Trait
      log [] [] [φ pubkey]
      unit.
  Proof.
    constructor.
    run_symbolic.
    admit.
  Admitted.

Instance run_find_program_address
  (seeds : Ref.t Pointer.Kind.Ref (list (Ref.t Pointer.Kind.Ref (list (Integer.t IntegerKind.U8)))))
  (pubkey : Ref.t Pointer.Kind.Ref Pubkey.t) :
Run.Trait
  find_program_address [] [] [φ seeds; φ pubkey]
  (Ref.t Pointer.Kind.Ref Pubkey.t * U8.t).
Proof.
    constructor.
    run_symbolic.
    admit.
Admitted.

Instance try_find_program_address
  (seeds : Ref.t Pointer.Kind.Ref (list (Ref.t Pointer.Kind.Ref (list (Integer.t IntegerKind.U8)))))
  (program_id : Ref.t Pointer.Kind.Ref Pubkey.t) :
Run.Trait
  try_find_program_address [] [] [φ seeds; φ program_id]
  (option (Ref.t Pointer.Kind.Ref Pubkey.t * U8.t)).
Proof.
    constructor.
    run_symbolic.
    admit.
Admitted.

Instance create_program_address
  (seeds : Ref.t Pointer.Kind.Ref (list (Ref.t Pointer.Kind.Ref (list (Integer.t IntegerKind.U8)))))
  (program_id : Ref.t Pointer.Kind.Ref Pubkey.t) :
  Run.Trait
    create_program_address [] [] [φ seeds; φ program_id]
    (Result.t (Ref.t Pointer.Kind.Ref Pubkey.t) ProgramError.t).
Proof.
  constructor.
  run_symbolic.
  admit.
Admitted.

Instance checked_create_program_address
  (seeds : Ref.t Pointer.Kind.Ref (list (Ref.t Pointer.Kind.Ref (list (Integer.t IntegerKind.U8)))))
  (program_id : Ref.t Pointer.Kind.Ref Pubkey.t) :
  Run.Trait
    checked_create_program_address [] [] [φ seeds; φ program_id]
    (Result.t (Ref.t Pointer.Kind.Ref Pubkey.t) ProgramError.t).
Proof.
  constructor.
  run_symbolic.
  admit.
Admitted.


