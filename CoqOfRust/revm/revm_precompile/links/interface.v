Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import alloc.links.string.
Require Import revm.revm_precompile.interface.

Module PrecompileError.
  Inductive t : Set :=
  | OutOfGas
  | Blake2WrongLength
  | Blake2WrongFinalIndicatorFlag
  | ModexpExpOverflow
  | ModexpBaseOverflow
  | ModexpModOverflow
  | Bn128FieldPointNotAMember
  | Bn128AffineGFailedToCreate
  | Bn128PairLength
  | BlobInvalidInputLength
  | BlobMismatchedVersion
  | BlobVerifyKzgProofFailed
  | Other
    (_ : alloc.links.string.String.t)
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_precompile::interface::PrecompileError";
    φ x :=
      match x with
      | OutOfGas =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::OutOfGas" []
      | Blake2WrongLength =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::Blake2WrongLength" []
      | Blake2WrongFinalIndicatorFlag =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::Blake2WrongFinalIndicatorFlag" []
      | ModexpExpOverflow =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::ModexpExpOverflow" []
      | ModexpBaseOverflow =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::ModexpBaseOverflow" []
      | ModexpModOverflow =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::ModexpModOverflow" []
      | Bn128FieldPointNotAMember =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::Bn128FieldPointNotAMember" []
      | Bn128AffineGFailedToCreate =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::Bn128AffineGFailedToCreate" []
      | Bn128PairLength =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::Bn128PairLength" []
      | BlobInvalidInputLength =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::BlobInvalidInputLength" []
      | BlobMismatchedVersion =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::BlobMismatchedVersion" []
      | BlobVerifyKzgProofFailed =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::BlobVerifyKzgProofFailed" []
      | Other γ0 =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::Other" [
          φ γ0
        ]
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_precompile::interface::PrecompileError").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_OutOfGas :
    Value.StructTuple "revm_precompile::interface::PrecompileError::OutOfGas" [] =
    φ OutOfGas.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_OutOfGas : of_value.

  Lemma of_value_with_Blake2WrongLength :
    Value.StructTuple "revm_precompile::interface::PrecompileError::Blake2WrongLength" [] =
    φ Blake2WrongLength.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Blake2WrongLength : of_value.

  Lemma of_value_with_Blake2WrongFinalIndicatorFlag :
    Value.StructTuple "revm_precompile::interface::PrecompileError::Blake2WrongFinalIndicatorFlag" [] =
    φ Blake2WrongFinalIndicatorFlag.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Blake2WrongFinalIndicatorFlag : of_value.

  Lemma of_value_with_ModexpExpOverflow :
    Value.StructTuple "revm_precompile::interface::PrecompileError::ModexpExpOverflow" [] =
    φ ModexpExpOverflow.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_ModexpExpOverflow : of_value.

  Lemma of_value_with_ModexpBaseOverflow :
    Value.StructTuple "revm_precompile::interface::PrecompileError::ModexpBaseOverflow" [] =
    φ ModexpBaseOverflow.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_ModexpBaseOverflow : of_value.

  Lemma of_value_with_ModexpModOverflow :
    Value.StructTuple "revm_precompile::interface::PrecompileError::ModexpModOverflow" [] =
    φ ModexpModOverflow.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_ModexpModOverflow : of_value.

  Lemma of_value_with_Bn128FieldPointNotAMember :
    Value.StructTuple "revm_precompile::interface::PrecompileError::Bn128FieldPointNotAMember" [] =
    φ Bn128FieldPointNotAMember.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Bn128FieldPointNotAMember : of_value.

  Lemma of_value_with_Bn128AffineGFailedToCreate :
    Value.StructTuple "revm_precompile::interface::PrecompileError::Bn128AffineGFailedToCreate" [] =
    φ Bn128AffineGFailedToCreate.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Bn128AffineGFailedToCreate : of_value.

  Lemma of_value_with_Bn128PairLength :
    Value.StructTuple "revm_precompile::interface::PrecompileError::Bn128PairLength" [] =
    φ Bn128PairLength.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Bn128PairLength : of_value.

  Lemma of_value_with_BlobInvalidInputLength :
    Value.StructTuple "revm_precompile::interface::PrecompileError::BlobInvalidInputLength" [] =
    φ BlobInvalidInputLength.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_BlobInvalidInputLength : of_value.

  Lemma of_value_with_BlobMismatchedVersion :
    Value.StructTuple "revm_precompile::interface::PrecompileError::BlobMismatchedVersion" [] =
    φ BlobMismatchedVersion.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_BlobMismatchedVersion : of_value.

  Lemma of_value_with_BlobVerifyKzgProofFailed :
    Value.StructTuple "revm_precompile::interface::PrecompileError::BlobVerifyKzgProofFailed" [] =
    φ BlobVerifyKzgProofFailed.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_BlobVerifyKzgProofFailed : of_value.

  Lemma of_value_with_Other
    (γ0 : alloc.links.string.String.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_precompile::interface::PrecompileError::Other" [
      γ0'
    ] =
    φ (Other γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Other : of_value.

  Definition of_value_OutOfGas :
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::OutOfGas" []
    ).
  Proof. econstructor; apply of_value_with_OutOfGas; eassumption. Defined.
  Smpl Add simple apply of_value_OutOfGas : of_value.

  Definition of_value_Blake2WrongLength :
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::Blake2WrongLength" []
    ).
  Proof. econstructor; apply of_value_with_Blake2WrongLength; eassumption. Defined.
  Smpl Add simple apply of_value_Blake2WrongLength : of_value.

  Definition of_value_Blake2WrongFinalIndicatorFlag :
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::Blake2WrongFinalIndicatorFlag" []
    ).
  Proof. econstructor; apply of_value_with_Blake2WrongFinalIndicatorFlag; eassumption. Defined.
  Smpl Add simple apply of_value_Blake2WrongFinalIndicatorFlag : of_value.

  Definition of_value_ModexpExpOverflow :
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::ModexpExpOverflow" []
    ).
  Proof. econstructor; apply of_value_with_ModexpExpOverflow; eassumption. Defined.
  Smpl Add simple apply of_value_ModexpExpOverflow : of_value.

  Definition of_value_ModexpBaseOverflow :
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::ModexpBaseOverflow" []
    ).
  Proof. econstructor; apply of_value_with_ModexpBaseOverflow; eassumption. Defined.
  Smpl Add simple apply of_value_ModexpBaseOverflow : of_value.

  Definition of_value_ModexpModOverflow :
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::ModexpModOverflow" []
    ).
  Proof. econstructor; apply of_value_with_ModexpModOverflow; eassumption. Defined.
  Smpl Add simple apply of_value_ModexpModOverflow : of_value.

  Definition of_value_Bn128FieldPointNotAMember :
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::Bn128FieldPointNotAMember" []
    ).
  Proof. econstructor; apply of_value_with_Bn128FieldPointNotAMember; eassumption. Defined.
  Smpl Add simple apply of_value_Bn128FieldPointNotAMember : of_value.

  Definition of_value_Bn128AffineGFailedToCreate :
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::Bn128AffineGFailedToCreate" []
    ).
  Proof. econstructor; apply of_value_with_Bn128AffineGFailedToCreate; eassumption. Defined.
  Smpl Add simple apply of_value_Bn128AffineGFailedToCreate : of_value.

  Definition of_value_Bn128PairLength :
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::Bn128PairLength" []
    ).
  Proof. econstructor; apply of_value_with_Bn128PairLength; eassumption. Defined.
  Smpl Add simple apply of_value_Bn128PairLength : of_value.

  Definition of_value_BlobInvalidInputLength :
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::BlobInvalidInputLength" []
    ).
  Proof. econstructor; apply of_value_with_BlobInvalidInputLength; eassumption. Defined.
  Smpl Add simple apply of_value_BlobInvalidInputLength : of_value.

  Definition of_value_BlobMismatchedVersion :
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::BlobMismatchedVersion" []
    ).
  Proof. econstructor; apply of_value_with_BlobMismatchedVersion; eassumption. Defined.
  Smpl Add simple apply of_value_BlobMismatchedVersion : of_value.

  Definition of_value_BlobVerifyKzgProofFailed :
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::BlobVerifyKzgProofFailed" []
    ).
  Proof. econstructor; apply of_value_with_BlobVerifyKzgProofFailed; eassumption. Defined.
  Smpl Add simple apply of_value_BlobVerifyKzgProofFailed : of_value.

  Definition of_value_Other
    (γ0 : alloc.links.string.String.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileError::Other" [
        γ0'
      ]
    ).
  Proof. econstructor; apply of_value_with_Other; eassumption. Defined.
  Smpl Add simple apply of_value_Other : of_value.
End PrecompileError.

Module Impl_PrecompileError.
  Definition Self : Set :=
    PrecompileError.t.

  (* pub fn is_oog(&self) -> bool *)
  Definition run_is_oog (self : Ref.t Pointer.Kind.Ref Self) :
    {{
      interface.Impl_revm_precompile_interface_PrecompileError.is_oog [] [] [ φ self ] 🔽
      bool
    }}.
  Proof.
    run_symbolic.
  Defined.
End Impl_PrecompileError.
