Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import pinocchio.links.account_info.
Require Import pinocchio.links.pubkey.
Require Import pinocchio.links.lib.
Require Import pinocchio.sysvars.clock.
Require Import core.links.result.
Require Import pinocchio.links.program_error.

Instance run_CLOCK_ID :
  Run.Trait
    pinocchio.sysvars.clock.sysvars.clock.value_CLOCK_ID [] [] []
    (Ref.t Pointer.Kind.Raw Pubkey.t).
Proof.
  constructor.
  admit.
Admitted.

Instance run_DEFAULT_TICKS_PER_SLOT :
  Run.Trait
    pinocchio.sysvars.clock.sysvars.clock.value_DEFAULT_TICKS_PER_SLOT [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor.
  run_symbolic.
Defined.

Instance run_DEFAULT_TICKS_PER_SECOND :
  Run.Trait
    pinocchio.sysvars.clock.sysvars.clock.value_DEFAULT_TICKS_PER_SECOND [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor.
  run_symbolic.
Defined.

Instance run_DEFAULT_MS_PER_SLOT :
  Run.Trait
    pinocchio.sysvars.clock.sysvars.clock.value_DEFAULT_MS_PER_SLOT [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor.
  run_symbolic.
Defined.

Module Clock.
  Record t : Set := {
    slot : U64.t;
    epoch_start_timestamp : I64.t;
    epoch : U64.t;
    leader_schedule_epoch : U64.t;
    unix_timestamp : I64.t
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "pinocchio::sysvars::clock::Clock";
    φ x :=
      Value.StructRecord "pinocchio::sysvars::clock::Clock" [] [] [
        ("slot", φ x.(slot));
        ("epoch_start_timestamp", φ x.(epoch_start_timestamp));
        ("epoch", φ x.(epoch));
        ("leader_schedule_epoch", φ x.(leader_schedule_epoch));
        ("unix_timestamp", φ x.(unix_timestamp))
      ];
  }.
End Clock.

Module Impl_Clock.
  Definition Self : Set := Clock.t.

  Instance run_LEN :
  Run.Trait
    pinocchio.sysvars.clock.sysvars.clock.Impl_pinocchio_sysvars_clock_Clock.value_LEN [] [] []
    (Ref.t Pointer.Kind.Raw Usize.t).
  Proof.
    constructor.
    run_symbolic.
  Defined.

  Instance run_from_account_info
    (account_info : Ref.t Pointer.Kind.Ref AccountInfo.t) :
    Run.Trait
      pinocchio.sysvars.clock.sysvars.clock.Impl_pinocchio_sysvars_clock_Clock.from_account_info
      [] []
      [φ account_info]
      (Result.t (Ref.t Pointer.Kind.Ref Self) ProgramError.t).
  Proof.
    constructor.
    admit.
  Admitted.

  Instance run_from_account_info_unchecked
    (account_info : Ref.t Pointer.Kind.Ref AccountInfo.t) :
    Run.Trait
      pinocchio.sysvars.clock.sysvars.clock.Impl_pinocchio_sysvars_clock_Clock.from_account_info_unchecked
      [] []
      [φ account_info]
      (Result.t (Ref.t Pointer.Kind.Ref Self) ProgramError.t).
  Proof.
    constructor.
    admit.
  Admitted.

  Instance run_from_bytes
    (bytes : Ref.t Pointer.Kind.Ref (list (Integer.t IntegerKind.U8))) :
    Run.Trait
      pinocchio.sysvars.clock.sysvars.clock.Impl_pinocchio_sysvars_clock_Clock.from_bytes
      [] []
      [φ bytes]
      (Result.t (Ref.t Pointer.Kind.Ref Self) ProgramError.t).
  Proof.
    constructor.
    admit.
  Admitted.

  Instance run_from_bytes_unchecked
    (bytes : Ref.t Pointer.Kind.Ref (list (Integer.t IntegerKind.U8))) :
    Run.Trait
      pinocchio.sysvars.clock.sysvars.clock.Impl_pinocchio_sysvars_clock_Clock.from_bytes_unchecked
      [] []
      [φ bytes]
      (Ref.t Pointer.Kind.Ref Self).
  Proof.
    constructor.
    admit.
  Admitted.
End Impl_Clock.
