Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import pinocchio.links.account_info.
Require Import pinocchio.links.pubkey.
Require Import pinocchio.links.lib.
Require Import pinocchio.entrypoint.lazy.
Require Import core.links.result.
Require Import pinocchio.links.program_error.

Module InstructionContext.
  Record t : Set := {
    buffer   : Ref.t Pointer.Kind.Raw U8.t;
    remaining: U64.t
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "pinocchio::entrypoint::lazy::InstructionContext";
    φ x :=
      Value.StructRecord "pinocchio::entrypoint::lazy::InstructionContext" [] [] [
        ("buffer",    φ x.(buffer));
        ("remaining", φ x.(remaining))
      ];
  }.
End InstructionContext.

Module MaybeAccount.
  Inductive t : Set :=
  | Account    (a : AccountInfo.t)
  | Duplicated (i : U8.t).

  Global Instance IsLink : Link t := {
    Φ := Ty.path "pinocchio::entrypoint::lazy::MaybeAccount";
    φ x :=
      match x with
      | Account a =>
          Value.StructTuple
            "pinocchio::entrypoint::lazy::MaybeAccount::Account" [] [] [φ a]
      | Duplicated i =>
          Value.StructTuple
            "pinocchio::entrypoint::lazy::MaybeAccount::Duplicated" [] [] [φ i]
      end;
  }.
End MaybeAccount.

Module Impl_InstructionContext.
  Definition Self : Set := InstructionContext.t.
  
  Instance run_new
    (input : Ref.t Pointer.Kind.Raw U8.t) :
    Run.Trait
      pinocchio.entrypoint.lazy.entrypoint.lazy.Impl_pinocchio_entrypoint_lazy_InstructionContext.new
      [] [] [φ input] Self.
  Proof.
    constructor. admit.
  Admitted.

  Instance run_new_unchecked
    (input : Ref.t Pointer.Kind.Raw U8.t) :
    Run.Trait
    pinocchio.entrypoint.lazy.entrypoint.lazy.Impl_pinocchio_entrypoint_lazy_InstructionContext.new_unchecked
      [] [] [φ input] Self.
  Proof.
    constructor. admit.
  Admitted.

  Instance run_next_account
    (self : Ref.t Pointer.Kind.Ref Self) :
    Run.Trait
    pinocchio.entrypoint.lazy.entrypoint.lazy.Impl_pinocchio_entrypoint_lazy_InstructionContext.next_account
      [] [] [φ self] (Result.t MaybeAccount.t ProgramError.t).
  Proof.
    constructor. admit.
  Admitted.

  Instance run_next_account_unchecked
    (self : Ref.t Pointer.Kind.Ref Self) :
    Run.Trait
    pinocchio.entrypoint.lazy.entrypoint.lazy.Impl_pinocchio_entrypoint_lazy_InstructionContext.next_account_unchecked
      [] [] [φ self] MaybeAccount.t.
  Proof.
    constructor. admit.
  Admitted.

  Instance run_remaining
    (self : Ref.t Pointer.Kind.Ref Self) :
    Run.Trait
    pinocchio.entrypoint.lazy.entrypoint.lazy.Impl_pinocchio_entrypoint_lazy_InstructionContext.remaining
      [] [] [φ self] U64.t.
  Proof.
    constructor. admit.
  Admitted.

  Instance run_instruction_data
    (self : Ref.t Pointer.Kind.Ref Self) :
    Run.Trait
     pinocchio.entrypoint.lazy.entrypoint.lazy.Impl_pinocchio_entrypoint_lazy_InstructionContext.instruction_data
      [] [] [φ self] (Result.t (list (Integer.t IntegerKind.U8)) ProgramError.t).
  Proof.
    constructor. admit.
  Admitted.

  Instance run_instruction_data_unchecked
    (self : Ref.t Pointer.Kind.Ref Self) :
    Run.Trait
    pinocchio.entrypoint.lazy.entrypoint.lazy.Impl_pinocchio_entrypoint_lazy_InstructionContext.instruction_data_unchecked
      [] [] [φ self] (list (Integer.t IntegerKind.U8)).
  Proof.
    constructor. admit.
  Admitted.

  Instance run_program_id
    (self : Ref.t Pointer.Kind.Ref Self) :
    Run.Trait
     pinocchio.entrypoint.lazy.entrypoint.lazy.Impl_pinocchio_entrypoint_lazy_InstructionContext.program_id
      [] [] [φ self] (Result.t (Ref.t Pointer.Kind.Ref Pubkey.t) ProgramError.t).
  Proof.
    constructor. admit.
  Admitted.

  Instance run_program_id_unchecked
    (self : Ref.t Pointer.Kind.Ref Self) :
    Run.Trait
     pinocchio.entrypoint.lazy.entrypoint.lazy.Impl_pinocchio_entrypoint_lazy_InstructionContext.program_id_unchecked
      [] [] [φ self] (Ref.t Pointer.Kind.Ref Pubkey.t).
  Proof.
    constructor. admit.
  Admitted.
End Impl_InstructionContext.

Module Impl_MaybeAccount.
    Definition Self : Set := MaybeAccount.t.
  
    Instance run_assume_account
      (self : Self) :
      Run.Trait
       pinocchio.entrypoint.lazy.entrypoint.lazy.Impl_pinocchio_entrypoint_lazy_MaybeAccount.assume_account
        [] [] [φ self] AccountInfo.t.
    Proof.
      constructor. admit.
    Admitted.
End Impl_MaybeAccount.