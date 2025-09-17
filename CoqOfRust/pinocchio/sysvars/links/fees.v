Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import pinocchio.links.lib.
Require Import pinocchio.links.pubkey.
Require Import pinocchio.sysvars.fees.
Require Import core.links.default.
Require Import core.links.clone.
Require Import core.links.marker.

Instance run_DEFAULT_TARGET_LAMPORTS_PER_SIGNATURE :
  Run.Trait
    pinocchio.sysvars.fees.sysvars.fees.value_DEFAULT_TARGET_LAMPORTS_PER_SIGNATURE [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor. run_symbolic.
Defined.

Instance run_DEFAULT_TARGET_SIGNATURES_PER_SLOT :
  Run.Trait
    pinocchio.sysvars.fees.sysvars.fees.value_DEFAULT_TARGET_SIGNATURES_PER_SLOT [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor. 
  run_symbolic.
  admit.
Admitted.

Instance run_DEFAULT_BURN_PERCENT :
  Run.Trait
    pinocchio.sysvars.fees.sysvars.fees.value_DEFAULT_BURN_PERCENT [] [] []
    (Ref.t Pointer.Kind.Raw U8.t).
Proof.
  constructor. run_symbolic.
Defined.

Module FeeCalculator.
  Record t : Set := {
    lamports_per_signature : U64.t
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "pinocchio::sysvars::fees::FeeCalculator";
    φ x :=
      Value.StructRecord "pinocchio::sysvars::fees::FeeCalculator" [] [] [
        ("lamports_per_signature", φ x.(lamports_per_signature))
      ];
  }.
End FeeCalculator.

Module FeeRateGovernor.
  Record t : Set := {
    lamports_per_signature : U64.t;
    target_lamports_per_signature : U64.t;
    target_signatures_per_slot : U64.t;
    min_lamports_per_signature : U64.t;
    max_lamports_per_signature : U64.t;
    burn_percent : U8.t
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "pinocchio::sysvars::fees::FeeRateGovernor";
    φ x :=
      Value.StructRecord "pinocchio::sysvars::fees::FeeRateGovernor" [] [] [
        ("lamports_per_signature", φ x.(lamports_per_signature));
        ("target_lamports_per_signature", φ x.(target_lamports_per_signature));
        ("target_signatures_per_slot", φ x.(target_signatures_per_slot));
        ("min_lamports_per_signature", φ x.(min_lamports_per_signature));
        ("max_lamports_per_signature", φ x.(max_lamports_per_signature));
        ("burn_percent", φ x.(burn_percent))
      ];
  }.
End FeeRateGovernor.

Module Fees.
  Record t : Set := {
    fee_calculator : FeeCalculator.t;
    fee_rate_governor : FeeRateGovernor.t
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "pinocchio::sysvars::fees::Fees";
    φ x :=
      Value.StructRecord "pinocchio::sysvars::fees::Fees" [] [] [
        ("fee_calculator", φ x.(fee_calculator));
        ("fee_rate_governor", φ x.(fee_rate_governor))
      ];
  }.
End Fees.

Module Impl_FeeCalculator.
  Definition Self : Set := FeeCalculator.t.

  Instance run_new
    (lamports_per_signature : U64.t) :
    Run.Trait
      pinocchio.sysvars.fees.sysvars.fees.Impl_pinocchio_sysvars_fees_FeeCalculator.new
      [] []
      [φ lamports_per_signature]
      Self.
  Proof.
    constructor. admit.
  Admitted.
End Impl_FeeCalculator.

Module Impl_FeeRateGovernor.
  Definition Self : Set := FeeRateGovernor.t.

  Instance run_default :
    Run.Trait
      pinocchio.sysvars.fees.sysvars.fees.Impl_core_default_Default_for_pinocchio_sysvars_fees_FeeRateGovernor.default
      [] []
      []
      Self.
  Proof.
    constructor. admit.
  Admitted.

  Instance run_create_fee_calculator
    (self : Ref.t Pointer.Kind.Ref Self) :
    Run.Trait
      pinocchio.sysvars.fees.sysvars.fees.Impl_pinocchio_sysvars_fees_FeeRateGovernor.create_fee_calculator
      [] []
      [φ self]
      FeeCalculator.t.
  Proof.
    constructor. admit.
  Admitted.

  Instance run_burn
    (self : Ref.t Pointer.Kind.Ref Self)
    (fees : U64.t) :
    Run.Trait
      pinocchio.sysvars.fees.sysvars.fees.Impl_pinocchio_sysvars_fees_FeeRateGovernor.burn
      [] []
      [φ self; φ fees]
      (U64.t * U64.t)%type.
  Proof.
    constructor. admit.
  Admitted.
End Impl_FeeRateGovernor.

Module Impl_Fees.
  Definition Self : Set := Fees.t.

  Instance run_new
    (fee_calculator : FeeCalculator.t)
    (fee_rate_governor : FeeRateGovernor.t) :
    Run.Trait
      pinocchio.sysvars.fees.sysvars.fees.Impl_pinocchio_sysvars_fees_Fees.new
      [] []
      [φ fee_calculator; φ fee_rate_governor]
      Self.
  Proof.
    constructor. admit.
  Admitted.
End Impl_Fees.

Module Impl_Default_for_FeeCalculator.
  Definition Self : Set := FeeCalculator.t.

  Definition run_default : Default.Run_default Self.
  Proof.
    eexists.
    { eapply IsTraitMethod.Defined.
      { apply pinocchio.sysvars.fees.sysvars.fees.Impl_core_default_Default_for_pinocchio_sysvars_fees_FeeCalculator.Implements. }
      { reflexivity. } }
    { constructor. admit. }
  Admitted.

  Instance run : Default.Run Self := { Default.default := run_default }.
End Impl_Default_for_FeeCalculator.

Module Impl_Clone_for_FeeCalculator.
  Definition Self : Set := FeeCalculator.t.

  Definition run_clone : Clone.Run_clone Self.
  Proof.
    eexists.
    { eapply IsTraitMethod.Defined.
      { apply pinocchio.sysvars.fees.sysvars.fees.Impl_core_clone_Clone_for_pinocchio_sysvars_fees_FeeCalculator.Implements. }
      { reflexivity. } }
    { constructor. admit. }
  Admitted.

  Instance run : Clone.Run Self := { Clone.clone := run_clone }.
End Impl_Clone_for_FeeCalculator.

Module Impl_Copy_for_FeeCalculator.
  Definition Self : Set := FeeCalculator.t.
  Instance run : Copy.Run Self.
  Proof. 
    constructor.
    admit.
  Admitted.
End Impl_Copy_for_FeeCalculator.

Module Impl_Clone_for_FeeRateGovernor.
  Definition Self : Set := FeeRateGovernor.t.

  Definition run_clone : Clone.Run_clone Self.
  Proof.
    eexists.
    { eapply IsTraitMethod.Defined.
      { apply pinocchio.sysvars.fees.sysvars.fees.Impl_core_clone_Clone_for_pinocchio_sysvars_fees_FeeRateGovernor.Implements. }
      { reflexivity. } }
    { constructor. admit. }
  Admitted.

  Instance run : Clone.Run Self := { Clone.clone := run_clone }.
End Impl_Clone_for_FeeRateGovernor.

Module Impl_Default_for_Fees.
  Definition Self : Set := Fees.t.

  Definition run_default : Default.Run_default Self.
  Proof.
    eexists.
    { eapply IsTraitMethod.Defined.
      { apply pinocchio.sysvars.fees.sysvars.fees.Impl_core_default_Default_for_pinocchio_sysvars_fees_Fees.Implements. }
      { reflexivity. } }
    { constructor. admit. }
  Admitted.

  Instance run : Default.Run Self := { Default.default := run_default }.
End Impl_Default_for_Fees.