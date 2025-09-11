Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import pinocchio.links.account_info.
Require Import pinocchio.links.pubkey.
Require Import pinocchio.links.lib.
Require Import pinocchio.sysvars.rent.
Require Import core.links.clone.
Require Import core.links.marker.

Print pinocchio.sysvars.rent.sysvars.rent.sysvars.rent.

Instance run_RENT_ID :
  Run.Trait
    pinocchio.sysvars.rent.sysvars.rent.value_RENT_ID [] [] []
    (Ref.t Pointer.Kind.Raw Pubkey.t).
Proof.
  constructor. 
  run_symbolic.
  - admit.
  - admit.
Admitted.

Instance run_DEFAULT_LAMPORTS_PER_BYTE_YEAR :
  Run.Trait
    pinocchio.sysvars.rent.sysvars.rent.value_DEFAULT_LAMPORTS_PER_BYTE_YEAR [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor. run_symbolic.
Defined.
(*
Instance run_DEFAULT_EXEMPTION_THRESHOLD :
  Run.Trait
    pinocchio.sysvars.rent.sysvars.rent.value_DEFAULT_EXEMPTION_THRESHOLD [] [] []
    (Ref.t Pointer.Kind.Raw F64.t).
Proof.
  constructor. run_symbolic.
Defined.
*)
Instance run_DEFAULT_EXEMPTION_THRESHOLD_AS_U64 :
  Run.Trait
    pinocchio.sysvars.rent.sysvars.rent.value_DEFAULT_EXEMPTION_THRESHOLD_AS_U64 [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor. run_symbolic.
Defined.

Instance run_F64_EXEMPTION_THRESHOLD_AS_U64 :
  Run.Trait
    pinocchio.sysvars.rent.sysvars.rent.value_F64_EXEMPTION_THRESHOLD_AS_U64 [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor. run_symbolic.
Defined.

Instance run_DEFAULT_BURN_PERCENT_rent :
  Run.Trait
    pinocchio.sysvars.rent.sysvars.rent.value_DEFAULT_BURN_PERCENT [] [] []
    (Ref.t Pointer.Kind.Raw U8.t).
Proof.
  constructor. run_symbolic.
Defined.

Instance run_ACCOUNT_STORAGE_OVERHEAD :
  Run.Trait
    pinocchio.sysvars.rent.sysvars.rent.value_ACCOUNT_STORAGE_OVERHEAD [] [] []
    (Ref.t Pointer.Kind.Raw U64.t).
Proof.
  constructor. run_symbolic.
Defined.
(*
Module Rent.
  Record t : Set := {
    lamports_per_byte_year : U64.t;
    exemption_threshold : F64.t;
    burn_percent : U8.t
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "pinocchio::sysvars::rent::Rent";
    φ x :=
      Value.StructRecord "pinocchio::sysvars::rent::Rent" [] [] [
        ("lamports_per_byte_year", φ x.(lamports_per_byte_year));
        ("exemption_threshold", φ x.(exemption_threshold));
        ("burn_percent", φ x.(burn_percent))
      ];
  }.
End Rent.
*)
Module RentDue.
  Inductive t : Set :=
  | Exempt
  | Paying (x : U64.t).

  Global Instance IsLink : Link t := {
    Φ := Ty.path "pinocchio::sysvars::rent::RentDue";
    φ v :=
      match v with
      | Exempt =>
          Value.StructTuple
            "pinocchio::sysvars::rent::RentDue::Exempt" [] [] []
      | Paying x =>
          Value.StructTuple
            "pinocchio::sysvars::rent::RentDue::Paying" [] [] [φ x]
      end;
  }.
End RentDue.

(*
Module Impl_Rent.
  Definition Self : Set := Rent.t.

  Instance run_from_account_info
    (account_info : Ref.t Pointer.Kind.Ref AccountInfo.t) :
    Run.Trait
      pinocchio.sysvars.rent.sysvars.rent.Impl_pinocchio_sysvars_rent_Rent.from_account_info
      [] []
      [φ account_info]
      (result (Ref.t Pointer.Kind.Ref Self) ProgramError.t).
  Proof.
    constructor. admit.
  Admitted.

  Instance run_from_account_info_unchecked
    (account_info : Ref.t Pointer.Kind.Ref AccountInfo.t) :
    Run.Trait
      pinocchio.sysvars.rent.sysvars.rent.Impl_pinocchio_sysvars_rent_Rent.from_account_info_unchecked
      [] []
      [φ account_info]
      (result (Ref.t Pointer.Kind.Ref Self) ProgramError.t).
  Proof.
    constructor. admit.
  Admitted.

  Instance run_from_bytes
    (bytes : Ref.t Pointer.Kind.Ref (list (Integer.t IntegerKind.U8))) :
    Run.Trait
      pinocchio.sysvars.rent.sysvars.rent.Impl_pinocchio_sysvars_rent_Rent.from_bytes
      [] []
      [φ bytes]
      (result (Ref.t Pointer.Kind.Ref Self) ProgramError.t).
  Proof.
    constructor. admit.
  Admitted.

  Instance run_from_bytes_unchecked
    (bytes : Ref.t Pointer.Kind.Ref (list (Integer.t IntegerKind.U8))) :
    Run.Trait
      pinocchio.sysvars.rent.sysvars.rent.Impl_pinocchio_sysvars_rent_Rent.from_bytes_unchecked
      [] []
      [φ bytes]
      (Ref.t Pointer.Kind.Ref Self).
  Proof.
    constructor. admit.
  Admitted.

  Instance run_calculate_burn
    (self : Ref.t Pointer.Kind.Ref Self)
    (rent_collected : U64.t) :
    Run.Trait
      pinocchio.sysvars.rent.sysvars.rent.Impl_pinocchio_sysvars_rent_Rent.calculate_burn
      [] []
      [φ self; φ rent_collected]
      (U64.t * U64.t)%type.
  Proof.
    constructor. admit.
  Admitted.

  Instance run_due
    (self : Ref.t Pointer.Kind.Ref Self)
    (balance : U64.t)
    (data_len : Usize.t)
    (years_elapsed : F64.t) :
    Run.Trait
      pinocchio.sysvars.rent.sysvars.rent.Impl_pinocchio_sysvars_rent_Rent.due
      [] []
      [φ self; φ balance; φ data_len; φ years_elapsed]
      RentDue.t.
  Proof.
    constructor. admit.
  Admitted.

  Instance run_due_amount
    (self : Ref.t Pointer.Kind.Ref Self)
    (data_len : Usize.t)
    (years_elapsed : F64.t) :
    Run.Trait
      pinocchio.sysvars.rent.sysvars.rent.Impl_pinocchio_sysvars_rent_Rent.due_amount
      [] []
      [φ self; φ data_len; φ years_elapsed]
      U64.t.
  Proof.
    constructor. admit.
  Admitted.

  Instance run_minimum_balance
    (self : Ref.t Pointer.Kind.Ref Self)
    (data_len : Usize.t) :
    Run.Trait
      pinocchio.sysvars.rent.sysvars.rent.Impl_pinocchio_sysvars_rent_Rent.minimum_balance
      [] []
      [φ self; φ data_len]
      U64.t.
  Proof.
    constructor. admit.
  Admitted.

  Instance run_is_exempt
    (self : Ref.t Pointer.Kind.Ref Self)
    (lamports : U64.t)
    (data_len : Usize.t) :
    Run.Trait
      pinocchio.sysvars.rent.sysvars.rent.Impl_pinocchio_sysvars_rent_Rent.is_exempt
      [] []
      [φ self; φ lamports; φ data_len]
      bool.
  Proof.
    constructor. admit.
  Admitted.

  Instance run_is_default_rent_threshold
    (self : Ref.t Pointer.Kind.Ref Self) :
    Run.Trait
      pinocchio.sysvars.rent.sysvars.rent.Impl_pinocchio_sysvars_rent_Rent.is_default_rent_threshold
      [] []
      [φ self]
      bool.
  Proof.
    constructor. admit.
  Admitted.
End Impl_Rent.
*)

Module Impl_RentDue.
  Definition Self : Set := RentDue.t.

  Instance run_lamports
    (self : Ref.t Pointer.Kind.Ref Self) :
    Run.Trait
      pinocchio.sysvars.rent.sysvars.rent.Impl_pinocchio_sysvars_rent_RentDue.lamports
      [] []
      [φ self]
      U64.t.
  Proof.
    constructor. admit.
  Admitted.

  Instance run_is_exempt
    (self : Ref.t Pointer.Kind.Ref Self) :
    Run.Trait
      pinocchio.sysvars.rent.sysvars.rent.Impl_pinocchio_sysvars_rent_RentDue.is_exempt
      [] []
      [φ self]
      bool.
  Proof.
    constructor. admit.
  Admitted.
End Impl_RentDue.

(*
Module Impl_Default_for_Rent.
  Definition Self : Set := Rent.t.

  Definition run_default : Default.Run_default Self.
  Proof.
    eexists.
    { eapply IsTraitMethod.Defined.
      { apply pinocchio.sysvars.rent.sysvars.rent.Impl_core_default_Default_for_pinocchio_sysvars_rent_Rent.Implements. }
      { reflexivity. } }
    { constructor. admit. }
  Admitted.

  Instance run : Default.Run Self := { Default.default := run_default }.
End Impl_Default_for_Rent.

Module Impl_Clone_for_Rent.
  Definition Self : Set := Rent.t.

  Definition run_clone : Clone.Run_clone Self.
  Proof.
    eexists.
    { eapply IsTraitMethod.Defined.
      { apply pinocchio.sysvars.rent.sysvars.rent.Impl_core_clone_Clone_for_pinocchio_sysvars_rent_Rent.Implements. }
      { reflexivity. } }
    { constructor. admit. }
  Admitted.

  Instance run : Clone.Run Self := { Clone.clone := run_clone }.
End Impl_Clone_for_Rent.
*)

Module Impl_Clone_for_RentDue.
  Definition Self : Set := RentDue.t.

  Definition run_clone : Clone.Run_clone Self.
  Proof.
    eexists.
    { eapply IsTraitMethod.Defined.
      { apply pinocchio.sysvars.rent.sysvars.rent.Impl_core_clone_Clone_for_pinocchio_sysvars_rent_RentDue.Implements. }
      { reflexivity. } }
    { constructor. admit. }
  Admitted.

  Instance run : Clone.Run Self := { Clone.clone := run_clone }.
End Impl_Clone_for_RentDue.

Module Impl_Copy_for_RentDue.
  Definition Self : Set := RentDue.t.
  Instance run : Copy.Run Self.
  Proof. 
    constructor.
    admit. 
  Admitted.
End Impl_Copy_for_RentDue.
