Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.links.array.
Require Import pinocchio.pubkey.
Require Import core.links.option.
Import pinocchio.pubkey.pubkey.

From Hammer Require Import Hammer.

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
Definition foo `{Link Pubkey.t} : bool := true.
Definition foow `{Link (option (Ref.t Pointer.Kind.Ref Pubkey.t * U8.t))} : bool := true.

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



