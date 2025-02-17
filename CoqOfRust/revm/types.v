(* Generated file. Do not edit. *)
Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require Import revm.links.dependencies.

Module Bytecode.
  Inductive t : Set :=
  | LegacyAnalyzed
    (_ : revm_bytecode.legacy.links.analyzed.LegacyAnalyzedBytecode.t)
  | Eof
    (_ : alloc.links.sync.Arc.t revm_bytecode.links.eof.Eof.t alloc.links.alloc.Global.t)
  | Eip7702
    (_ : revm_bytecode.links.eip7702.Eip7702Bytecode.t)
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_bytecode::bytecode::Bytecode";
    φ x :=
      match x with
      | LegacyAnalyzed γ0 =>
        Value.StructTuple "revm_bytecode::bytecode::Bytecode::LegacyAnalyzed" [
          φ γ0
        ]
      | Eof γ0 =>
        Value.StructTuple "revm_bytecode::bytecode::Bytecode::Eof" [
          φ γ0
        ]
      | Eip7702 γ0 =>
        Value.StructTuple "revm_bytecode::bytecode::Bytecode::Eip7702" [
          φ γ0
        ]
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_bytecode::bytecode::Bytecode").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_LegacyAnalyzed
    (γ0 : revm_bytecode.legacy.links.analyzed.LegacyAnalyzedBytecode.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_bytecode::bytecode::Bytecode::LegacyAnalyzed" [
      γ0
    ] =
    φ (LegacyAnalyzed γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_LegacyAnalyzed : of_value.

  Lemma of_value_with_Eof
    (γ0 : alloc.links.sync.Arc.t revm_bytecode.links.eof.Eof.t alloc.links.alloc.Global.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_bytecode::bytecode::Bytecode::Eof" [
      γ0
    ] =
    φ (Eof γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Eof : of_value.

  Lemma of_value_with_Eip7702
    (γ0 : revm_bytecode.links.eip7702.Eip7702Bytecode.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_bytecode::bytecode::Bytecode::Eip7702" [
      γ0
    ] =
    φ (Eip7702 γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Eip7702 : of_value.

  Definition of_value_LegacyAnalyzed
    (γ0 : revm_bytecode.legacy.links.analyzed.LegacyAnalyzedBytecode.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_bytecode::bytecode::Bytecode::LegacyAnalyzed" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_LegacyAnalyzed; eassumption. Defined.
  Smpl Add simple apply of_value_LegacyAnalyzed : of_value.

  Definition of_value_Eof
    (γ0 : alloc.links.sync.Arc.t revm_bytecode.links.eof.Eof.t alloc.links.alloc.Global.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_bytecode::bytecode::Bytecode::Eof" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Eof; eassumption. Defined.
  Smpl Add simple apply of_value_Eof : of_value.

  Definition of_value_Eip7702
    (γ0 : revm_bytecode.links.eip7702.Eip7702Bytecode.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_bytecode::bytecode::Bytecode::Eip7702" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Eip7702; eassumption. Defined.
  Smpl Add simple apply of_value_Eip7702 : of_value.
End Bytecode.

Module BytecodeDecodeError.
  Inductive t : Set :=
  | Eof
    (_ : revm_bytecode.links.eof.EofDecodeError.t)
  | Eip7702
    (_ : revm_bytecode.links.eip7702.Eip7702DecodeError.t)
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_bytecode::decode_errors::BytecodeDecodeError";
    φ x :=
      match x with
      | Eof γ0 =>
        Value.StructTuple "revm_bytecode::decode_errors::BytecodeDecodeError::Eof" [
          φ γ0
        ]
      | Eip7702 γ0 =>
        Value.StructTuple "revm_bytecode::decode_errors::BytecodeDecodeError::Eip7702" [
          φ γ0
        ]
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_bytecode::decode_errors::BytecodeDecodeError").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_Eof
    (γ0 : revm_bytecode.links.eof.EofDecodeError.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_bytecode::decode_errors::BytecodeDecodeError::Eof" [
      γ0
    ] =
    φ (Eof γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Eof : of_value.

  Lemma of_value_with_Eip7702
    (γ0 : revm_bytecode.links.eip7702.Eip7702DecodeError.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_bytecode::decode_errors::BytecodeDecodeError::Eip7702" [
      γ0
    ] =
    φ (Eip7702 γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Eip7702 : of_value.

  Definition of_value_Eof
    (γ0 : revm_bytecode.links.eof.EofDecodeError.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_bytecode::decode_errors::BytecodeDecodeError::Eof" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Eof; eassumption. Defined.
  Smpl Add simple apply of_value_Eof : of_value.

  Definition of_value_Eip7702
    (γ0 : revm_bytecode.links.eip7702.Eip7702DecodeError.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_bytecode::decode_errors::BytecodeDecodeError::Eip7702" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Eip7702; eassumption. Defined.
  Smpl Add simple apply of_value_Eip7702 : of_value.
End BytecodeDecodeError.

Module Eip7702Bytecode.
  Record t : Set := {
    delegated_address: alloy_primitives.bits.links.address.Address.t;
    version: U8.t;
    raw: alloy_primitives.links.bytes_.Bytes.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_bytecode::eip7702::Eip7702Bytecode";
    φ '(Build_t delegated_address version raw) :=
      Value.StructRecord "revm_bytecode::eip7702::Eip7702Bytecode" [
        ("delegated_address", φ delegated_address);
        ("version", φ version);
        ("raw", φ raw)
      ]
  }.
End Eip7702Bytecode.

Module Eip7702DecodeError.
  Inductive t : Set :=
  | InvalidLength
  | InvalidMagic
  | UnsupportedVersion
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_bytecode::eip7702::Eip7702DecodeError";
    φ x :=
      match x with
      | InvalidLength =>
        Value.StructTuple "revm_bytecode::eip7702::Eip7702DecodeError::InvalidLength" []
      | InvalidMagic =>
        Value.StructTuple "revm_bytecode::eip7702::Eip7702DecodeError::InvalidMagic" []
      | UnsupportedVersion =>
        Value.StructTuple "revm_bytecode::eip7702::Eip7702DecodeError::UnsupportedVersion" []
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_bytecode::eip7702::Eip7702DecodeError").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_InvalidLength :
    Value.StructTuple "revm_bytecode::eip7702::Eip7702DecodeError::InvalidLength" [] =
    φ InvalidLength.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InvalidLength : of_value.

  Lemma of_value_with_InvalidMagic :
    Value.StructTuple "revm_bytecode::eip7702::Eip7702DecodeError::InvalidMagic" [] =
    φ InvalidMagic.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InvalidMagic : of_value.

  Lemma of_value_with_UnsupportedVersion :
    Value.StructTuple "revm_bytecode::eip7702::Eip7702DecodeError::UnsupportedVersion" [] =
    φ UnsupportedVersion.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_UnsupportedVersion : of_value.

  Definition of_value_InvalidLength :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eip7702::Eip7702DecodeError::InvalidLength" []
    ).
  Proof. econstructor; apply of_value_with_InvalidLength; eassumption. Defined.
  Smpl Add simple apply of_value_InvalidLength : of_value.

  Definition of_value_InvalidMagic :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eip7702::Eip7702DecodeError::InvalidMagic" []
    ).
  Proof. econstructor; apply of_value_with_InvalidMagic; eassumption. Defined.
  Smpl Add simple apply of_value_InvalidMagic : of_value.

  Definition of_value_UnsupportedVersion :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eip7702::Eip7702DecodeError::UnsupportedVersion" []
    ).
  Proof. econstructor; apply of_value_with_UnsupportedVersion; eassumption. Defined.
  Smpl Add simple apply of_value_UnsupportedVersion : of_value.
End Eip7702DecodeError.

Module Eof.
  Record t : Set := {
    header: revm_bytecode.eof.links.header.EofHeader.t;
    body: revm_bytecode.eof.links.body.EofBody.t;
    raw: alloy_primitives.links.bytes_.Bytes.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_bytecode::eof::Eof";
    φ '(Build_t header body raw) :=
      Value.StructRecord "revm_bytecode::eof::Eof" [
        ("header", φ header);
        ("body", φ body);
        ("raw", φ raw)
      ]
  }.
End Eof.

Module EofDecodeError.
  Inductive t : Set :=
  | MissingInput
  | MissingBodyWithoutData
  | DanglingData
  | InvalidTypesSection
  | InvalidTypesSectionSize
  | InvalidEOFMagicNumber
  | InvalidEOFVersion
  | InvalidTypesKind
  | InvalidCodeKind
  | InvalidTerminalByte
  | InvalidDataKind
  | InvalidKindAfterCode
  | MismatchCodeAndTypesSize
  | NonSizes
  | ShortInputForSizes
  | ZeroSize
  | TooManyCodeSections
  | ZeroCodeSections
  | TooManyContainerSections
  | InvalidEOFSize
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_bytecode::eof::EofDecodeError";
    φ x :=
      match x with
      | MissingInput =>
        Value.StructTuple "revm_bytecode::eof::EofDecodeError::MissingInput" []
      | MissingBodyWithoutData =>
        Value.StructTuple "revm_bytecode::eof::EofDecodeError::MissingBodyWithoutData" []
      | DanglingData =>
        Value.StructTuple "revm_bytecode::eof::EofDecodeError::DanglingData" []
      | InvalidTypesSection =>
        Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidTypesSection" []
      | InvalidTypesSectionSize =>
        Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidTypesSectionSize" []
      | InvalidEOFMagicNumber =>
        Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidEOFMagicNumber" []
      | InvalidEOFVersion =>
        Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidEOFVersion" []
      | InvalidTypesKind =>
        Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidTypesKind" []
      | InvalidCodeKind =>
        Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidCodeKind" []
      | InvalidTerminalByte =>
        Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidTerminalByte" []
      | InvalidDataKind =>
        Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidDataKind" []
      | InvalidKindAfterCode =>
        Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidKindAfterCode" []
      | MismatchCodeAndTypesSize =>
        Value.StructTuple "revm_bytecode::eof::EofDecodeError::MismatchCodeAndTypesSize" []
      | NonSizes =>
        Value.StructTuple "revm_bytecode::eof::EofDecodeError::NonSizes" []
      | ShortInputForSizes =>
        Value.StructTuple "revm_bytecode::eof::EofDecodeError::ShortInputForSizes" []
      | ZeroSize =>
        Value.StructTuple "revm_bytecode::eof::EofDecodeError::ZeroSize" []
      | TooManyCodeSections =>
        Value.StructTuple "revm_bytecode::eof::EofDecodeError::TooManyCodeSections" []
      | ZeroCodeSections =>
        Value.StructTuple "revm_bytecode::eof::EofDecodeError::ZeroCodeSections" []
      | TooManyContainerSections =>
        Value.StructTuple "revm_bytecode::eof::EofDecodeError::TooManyContainerSections" []
      | InvalidEOFSize =>
        Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidEOFSize" []
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_bytecode::eof::EofDecodeError").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_MissingInput :
    Value.StructTuple "revm_bytecode::eof::EofDecodeError::MissingInput" [] =
    φ MissingInput.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_MissingInput : of_value.

  Lemma of_value_with_MissingBodyWithoutData :
    Value.StructTuple "revm_bytecode::eof::EofDecodeError::MissingBodyWithoutData" [] =
    φ MissingBodyWithoutData.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_MissingBodyWithoutData : of_value.

  Lemma of_value_with_DanglingData :
    Value.StructTuple "revm_bytecode::eof::EofDecodeError::DanglingData" [] =
    φ DanglingData.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_DanglingData : of_value.

  Lemma of_value_with_InvalidTypesSection :
    Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidTypesSection" [] =
    φ InvalidTypesSection.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InvalidTypesSection : of_value.

  Lemma of_value_with_InvalidTypesSectionSize :
    Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidTypesSectionSize" [] =
    φ InvalidTypesSectionSize.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InvalidTypesSectionSize : of_value.

  Lemma of_value_with_InvalidEOFMagicNumber :
    Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidEOFMagicNumber" [] =
    φ InvalidEOFMagicNumber.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InvalidEOFMagicNumber : of_value.

  Lemma of_value_with_InvalidEOFVersion :
    Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidEOFVersion" [] =
    φ InvalidEOFVersion.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InvalidEOFVersion : of_value.

  Lemma of_value_with_InvalidTypesKind :
    Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidTypesKind" [] =
    φ InvalidTypesKind.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InvalidTypesKind : of_value.

  Lemma of_value_with_InvalidCodeKind :
    Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidCodeKind" [] =
    φ InvalidCodeKind.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InvalidCodeKind : of_value.

  Lemma of_value_with_InvalidTerminalByte :
    Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidTerminalByte" [] =
    φ InvalidTerminalByte.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InvalidTerminalByte : of_value.

  Lemma of_value_with_InvalidDataKind :
    Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidDataKind" [] =
    φ InvalidDataKind.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InvalidDataKind : of_value.

  Lemma of_value_with_InvalidKindAfterCode :
    Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidKindAfterCode" [] =
    φ InvalidKindAfterCode.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InvalidKindAfterCode : of_value.

  Lemma of_value_with_MismatchCodeAndTypesSize :
    Value.StructTuple "revm_bytecode::eof::EofDecodeError::MismatchCodeAndTypesSize" [] =
    φ MismatchCodeAndTypesSize.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_MismatchCodeAndTypesSize : of_value.

  Lemma of_value_with_NonSizes :
    Value.StructTuple "revm_bytecode::eof::EofDecodeError::NonSizes" [] =
    φ NonSizes.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_NonSizes : of_value.

  Lemma of_value_with_ShortInputForSizes :
    Value.StructTuple "revm_bytecode::eof::EofDecodeError::ShortInputForSizes" [] =
    φ ShortInputForSizes.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_ShortInputForSizes : of_value.

  Lemma of_value_with_ZeroSize :
    Value.StructTuple "revm_bytecode::eof::EofDecodeError::ZeroSize" [] =
    φ ZeroSize.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_ZeroSize : of_value.

  Lemma of_value_with_TooManyCodeSections :
    Value.StructTuple "revm_bytecode::eof::EofDecodeError::TooManyCodeSections" [] =
    φ TooManyCodeSections.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_TooManyCodeSections : of_value.

  Lemma of_value_with_ZeroCodeSections :
    Value.StructTuple "revm_bytecode::eof::EofDecodeError::ZeroCodeSections" [] =
    φ ZeroCodeSections.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_ZeroCodeSections : of_value.

  Lemma of_value_with_TooManyContainerSections :
    Value.StructTuple "revm_bytecode::eof::EofDecodeError::TooManyContainerSections" [] =
    φ TooManyContainerSections.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_TooManyContainerSections : of_value.

  Lemma of_value_with_InvalidEOFSize :
    Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidEOFSize" [] =
    φ InvalidEOFSize.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InvalidEOFSize : of_value.

  Definition of_value_MissingInput :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::EofDecodeError::MissingInput" []
    ).
  Proof. econstructor; apply of_value_with_MissingInput; eassumption. Defined.
  Smpl Add simple apply of_value_MissingInput : of_value.

  Definition of_value_MissingBodyWithoutData :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::EofDecodeError::MissingBodyWithoutData" []
    ).
  Proof. econstructor; apply of_value_with_MissingBodyWithoutData; eassumption. Defined.
  Smpl Add simple apply of_value_MissingBodyWithoutData : of_value.

  Definition of_value_DanglingData :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::EofDecodeError::DanglingData" []
    ).
  Proof. econstructor; apply of_value_with_DanglingData; eassumption. Defined.
  Smpl Add simple apply of_value_DanglingData : of_value.

  Definition of_value_InvalidTypesSection :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidTypesSection" []
    ).
  Proof. econstructor; apply of_value_with_InvalidTypesSection; eassumption. Defined.
  Smpl Add simple apply of_value_InvalidTypesSection : of_value.

  Definition of_value_InvalidTypesSectionSize :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidTypesSectionSize" []
    ).
  Proof. econstructor; apply of_value_with_InvalidTypesSectionSize; eassumption. Defined.
  Smpl Add simple apply of_value_InvalidTypesSectionSize : of_value.

  Definition of_value_InvalidEOFMagicNumber :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidEOFMagicNumber" []
    ).
  Proof. econstructor; apply of_value_with_InvalidEOFMagicNumber; eassumption. Defined.
  Smpl Add simple apply of_value_InvalidEOFMagicNumber : of_value.

  Definition of_value_InvalidEOFVersion :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidEOFVersion" []
    ).
  Proof. econstructor; apply of_value_with_InvalidEOFVersion; eassumption. Defined.
  Smpl Add simple apply of_value_InvalidEOFVersion : of_value.

  Definition of_value_InvalidTypesKind :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidTypesKind" []
    ).
  Proof. econstructor; apply of_value_with_InvalidTypesKind; eassumption. Defined.
  Smpl Add simple apply of_value_InvalidTypesKind : of_value.

  Definition of_value_InvalidCodeKind :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidCodeKind" []
    ).
  Proof. econstructor; apply of_value_with_InvalidCodeKind; eassumption. Defined.
  Smpl Add simple apply of_value_InvalidCodeKind : of_value.

  Definition of_value_InvalidTerminalByte :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidTerminalByte" []
    ).
  Proof. econstructor; apply of_value_with_InvalidTerminalByte; eassumption. Defined.
  Smpl Add simple apply of_value_InvalidTerminalByte : of_value.

  Definition of_value_InvalidDataKind :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidDataKind" []
    ).
  Proof. econstructor; apply of_value_with_InvalidDataKind; eassumption. Defined.
  Smpl Add simple apply of_value_InvalidDataKind : of_value.

  Definition of_value_InvalidKindAfterCode :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidKindAfterCode" []
    ).
  Proof. econstructor; apply of_value_with_InvalidKindAfterCode; eassumption. Defined.
  Smpl Add simple apply of_value_InvalidKindAfterCode : of_value.

  Definition of_value_MismatchCodeAndTypesSize :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::EofDecodeError::MismatchCodeAndTypesSize" []
    ).
  Proof. econstructor; apply of_value_with_MismatchCodeAndTypesSize; eassumption. Defined.
  Smpl Add simple apply of_value_MismatchCodeAndTypesSize : of_value.

  Definition of_value_NonSizes :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::EofDecodeError::NonSizes" []
    ).
  Proof. econstructor; apply of_value_with_NonSizes; eassumption. Defined.
  Smpl Add simple apply of_value_NonSizes : of_value.

  Definition of_value_ShortInputForSizes :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::EofDecodeError::ShortInputForSizes" []
    ).
  Proof. econstructor; apply of_value_with_ShortInputForSizes; eassumption. Defined.
  Smpl Add simple apply of_value_ShortInputForSizes : of_value.

  Definition of_value_ZeroSize :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::EofDecodeError::ZeroSize" []
    ).
  Proof. econstructor; apply of_value_with_ZeroSize; eassumption. Defined.
  Smpl Add simple apply of_value_ZeroSize : of_value.

  Definition of_value_TooManyCodeSections :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::EofDecodeError::TooManyCodeSections" []
    ).
  Proof. econstructor; apply of_value_with_TooManyCodeSections; eassumption. Defined.
  Smpl Add simple apply of_value_TooManyCodeSections : of_value.

  Definition of_value_ZeroCodeSections :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::EofDecodeError::ZeroCodeSections" []
    ).
  Proof. econstructor; apply of_value_with_ZeroCodeSections; eassumption. Defined.
  Smpl Add simple apply of_value_ZeroCodeSections : of_value.

  Definition of_value_TooManyContainerSections :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::EofDecodeError::TooManyContainerSections" []
    ).
  Proof. econstructor; apply of_value_with_TooManyContainerSections; eassumption. Defined.
  Smpl Add simple apply of_value_TooManyContainerSections : of_value.

  Definition of_value_InvalidEOFSize :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidEOFSize" []
    ).
  Proof. econstructor; apply of_value_with_InvalidEOFSize; eassumption. Defined.
  Smpl Add simple apply of_value_InvalidEOFSize : of_value.
End EofDecodeError.

Module EofBody.
  Record t : Set := {
    types_section: alloc.links.vec.Vec.t revm_bytecode.eof.links.types_section.TypesSection.t alloc.links.alloc.Global.t;
    code_section: alloc.links.vec.Vec.t Usize.t alloc.links.alloc.Global.t;
    code: alloy_primitives.links.bytes_.Bytes.t;
    container_section: alloc.links.vec.Vec.t alloy_primitives.links.bytes_.Bytes.t alloc.links.alloc.Global.t;
    data_section: alloy_primitives.links.bytes_.Bytes.t;
    is_data_filled: bool;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_bytecode::eof::body::EofBody";
    φ '(Build_t types_section code_section code container_section data_section is_data_filled) :=
      Value.StructRecord "revm_bytecode::eof::body::EofBody" [
        ("types_section", φ types_section);
        ("code_section", φ code_section);
        ("code", φ code);
        ("container_section", φ container_section);
        ("data_section", φ data_section);
        ("is_data_filled", φ is_data_filled)
      ]
  }.
End EofBody.

Module EofHeader.
  Record t : Set := {
    types_size: U16.t;
    code_sizes: alloc.links.vec.Vec.t U16.t alloc.links.alloc.Global.t;
    container_sizes: alloc.links.vec.Vec.t U16.t alloc.links.alloc.Global.t;
    data_size: U16.t;
    sum_code_sizes: Usize.t;
    sum_container_sizes: Usize.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_bytecode::eof::header::EofHeader";
    φ '(Build_t types_size code_sizes container_sizes data_size sum_code_sizes sum_container_sizes) :=
      Value.StructRecord "revm_bytecode::eof::header::EofHeader" [
        ("types_size", φ types_size);
        ("code_sizes", φ code_sizes);
        ("container_sizes", φ container_sizes);
        ("data_size", φ data_size);
        ("sum_code_sizes", φ sum_code_sizes);
        ("sum_container_sizes", φ sum_container_sizes)
      ]
  }.
End EofHeader.

Module TypesSection.
  Record t : Set := {
    inputs: U8.t;
    outputs: U8.t;
    max_stack_size: U16.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_bytecode::eof::types_section::TypesSection";
    φ '(Build_t inputs outputs max_stack_size) :=
      Value.StructRecord "revm_bytecode::eof::types_section::TypesSection" [
        ("inputs", φ inputs);
        ("outputs", φ outputs);
        ("max_stack_size", φ max_stack_size)
      ]
  }.
End TypesSection.

Module EofError.
  Inductive t : Set :=
  | Decode
    (_ : revm_bytecode.links.eof.EofDecodeError.t)
  | Validation
    (_ : revm_bytecode.eof.links.verification.EofValidationError.t)
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_bytecode::eof::verification::EofError";
    φ x :=
      match x with
      | Decode γ0 =>
        Value.StructTuple "revm_bytecode::eof::verification::EofError::Decode" [
          φ γ0
        ]
      | Validation γ0 =>
        Value.StructTuple "revm_bytecode::eof::verification::EofError::Validation" [
          φ γ0
        ]
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_bytecode::eof::verification::EofError").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_Decode
    (γ0 : revm_bytecode.links.eof.EofDecodeError.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_bytecode::eof::verification::EofError::Decode" [
      γ0
    ] =
    φ (Decode γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Decode : of_value.

  Lemma of_value_with_Validation
    (γ0 : revm_bytecode.eof.links.verification.EofValidationError.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_bytecode::eof::verification::EofError::Validation" [
      γ0
    ] =
    φ (Validation γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Validation : of_value.

  Definition of_value_Decode
    (γ0 : revm_bytecode.links.eof.EofDecodeError.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::verification::EofError::Decode" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Decode; eassumption. Defined.
  Smpl Add simple apply of_value_Decode : of_value.

  Definition of_value_Validation
    (γ0 : revm_bytecode.eof.links.verification.EofValidationError.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::verification::EofError::Validation" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Validation; eassumption. Defined.
  Smpl Add simple apply of_value_Validation : of_value.
End EofError.

Module EofValidationError.
  Inductive t : Set :=
  | FalsePositive
  | UnknownOpcode
  | OpcodeDisabled
  | InstructionNotForwardAccessed
  | MissingImmediateBytes
  | MissingRJUMPVImmediateBytes
  | JumpToImmediateBytes
  | BackwardJumpToImmediateBytes
  | RJUMPVZeroMaxIndex
  | JumpZeroOffset
  | EOFCREATEInvalidIndex
  | CodeSectionOutOfBounds
  | CALLFNonReturningFunction
  | StackOverflow
  | JUMPFEnoughOutputs
  | JUMPFStackHigherThanOutputs
  | DataLoadOutOfBounds
  | RETFBiggestStackNumMoreThenOutputs
  | StackUnderflow
  | TypesStackUnderflow
  | JumpUnderflow
  | JumpOverflow
  | BackwardJumpBiggestNumMismatch
  | BackwardJumpSmallestNumMismatch
  | LastInstructionNotTerminating
  | CodeSectionNotAccessed
  | InvalidTypesSection
  | InvalidFirstTypesSection
  | MaxStackMismatch
  | NoCodeSections
  | SubContainerCalledInTwoModes
  | SubContainerNotAccessed
  | DataNotFilled
  | NonReturningSectionIsReturning
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_bytecode::eof::verification::EofValidationError";
    φ x :=
      match x with
      | FalsePositive =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::FalsePositive" []
      | UnknownOpcode =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::UnknownOpcode" []
      | OpcodeDisabled =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::OpcodeDisabled" []
      | InstructionNotForwardAccessed =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::InstructionNotForwardAccessed" []
      | MissingImmediateBytes =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::MissingImmediateBytes" []
      | MissingRJUMPVImmediateBytes =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::MissingRJUMPVImmediateBytes" []
      | JumpToImmediateBytes =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::JumpToImmediateBytes" []
      | BackwardJumpToImmediateBytes =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::BackwardJumpToImmediateBytes" []
      | RJUMPVZeroMaxIndex =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::RJUMPVZeroMaxIndex" []
      | JumpZeroOffset =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::JumpZeroOffset" []
      | EOFCREATEInvalidIndex =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::EOFCREATEInvalidIndex" []
      | CodeSectionOutOfBounds =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::CodeSectionOutOfBounds" []
      | CALLFNonReturningFunction =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::CALLFNonReturningFunction" []
      | StackOverflow =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::StackOverflow" []
      | JUMPFEnoughOutputs =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::JUMPFEnoughOutputs" []
      | JUMPFStackHigherThanOutputs =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::JUMPFStackHigherThanOutputs" []
      | DataLoadOutOfBounds =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::DataLoadOutOfBounds" []
      | RETFBiggestStackNumMoreThenOutputs =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::RETFBiggestStackNumMoreThenOutputs" []
      | StackUnderflow =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::StackUnderflow" []
      | TypesStackUnderflow =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::TypesStackUnderflow" []
      | JumpUnderflow =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::JumpUnderflow" []
      | JumpOverflow =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::JumpOverflow" []
      | BackwardJumpBiggestNumMismatch =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::BackwardJumpBiggestNumMismatch" []
      | BackwardJumpSmallestNumMismatch =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::BackwardJumpSmallestNumMismatch" []
      | LastInstructionNotTerminating =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::LastInstructionNotTerminating" []
      | CodeSectionNotAccessed =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::CodeSectionNotAccessed" []
      | InvalidTypesSection =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::InvalidTypesSection" []
      | InvalidFirstTypesSection =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::InvalidFirstTypesSection" []
      | MaxStackMismatch =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::MaxStackMismatch" []
      | NoCodeSections =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::NoCodeSections" []
      | SubContainerCalledInTwoModes =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::SubContainerCalledInTwoModes" []
      | SubContainerNotAccessed =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::SubContainerNotAccessed" []
      | DataNotFilled =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::DataNotFilled" []
      | NonReturningSectionIsReturning =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::NonReturningSectionIsReturning" []
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_bytecode::eof::verification::EofValidationError").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_FalsePositive :
    Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::FalsePositive" [] =
    φ FalsePositive.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_FalsePositive : of_value.

  Lemma of_value_with_UnknownOpcode :
    Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::UnknownOpcode" [] =
    φ UnknownOpcode.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_UnknownOpcode : of_value.

  Lemma of_value_with_OpcodeDisabled :
    Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::OpcodeDisabled" [] =
    φ OpcodeDisabled.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_OpcodeDisabled : of_value.

  Lemma of_value_with_InstructionNotForwardAccessed :
    Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::InstructionNotForwardAccessed" [] =
    φ InstructionNotForwardAccessed.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InstructionNotForwardAccessed : of_value.

  Lemma of_value_with_MissingImmediateBytes :
    Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::MissingImmediateBytes" [] =
    φ MissingImmediateBytes.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_MissingImmediateBytes : of_value.

  Lemma of_value_with_MissingRJUMPVImmediateBytes :
    Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::MissingRJUMPVImmediateBytes" [] =
    φ MissingRJUMPVImmediateBytes.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_MissingRJUMPVImmediateBytes : of_value.

  Lemma of_value_with_JumpToImmediateBytes :
    Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::JumpToImmediateBytes" [] =
    φ JumpToImmediateBytes.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_JumpToImmediateBytes : of_value.

  Lemma of_value_with_BackwardJumpToImmediateBytes :
    Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::BackwardJumpToImmediateBytes" [] =
    φ BackwardJumpToImmediateBytes.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_BackwardJumpToImmediateBytes : of_value.

  Lemma of_value_with_RJUMPVZeroMaxIndex :
    Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::RJUMPVZeroMaxIndex" [] =
    φ RJUMPVZeroMaxIndex.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_RJUMPVZeroMaxIndex : of_value.

  Lemma of_value_with_JumpZeroOffset :
    Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::JumpZeroOffset" [] =
    φ JumpZeroOffset.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_JumpZeroOffset : of_value.

  Lemma of_value_with_EOFCREATEInvalidIndex :
    Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::EOFCREATEInvalidIndex" [] =
    φ EOFCREATEInvalidIndex.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_EOFCREATEInvalidIndex : of_value.

  Lemma of_value_with_CodeSectionOutOfBounds :
    Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::CodeSectionOutOfBounds" [] =
    φ CodeSectionOutOfBounds.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CodeSectionOutOfBounds : of_value.

  Lemma of_value_with_CALLFNonReturningFunction :
    Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::CALLFNonReturningFunction" [] =
    φ CALLFNonReturningFunction.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CALLFNonReturningFunction : of_value.

  Lemma of_value_with_StackOverflow :
    Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::StackOverflow" [] =
    φ StackOverflow.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_StackOverflow : of_value.

  Lemma of_value_with_JUMPFEnoughOutputs :
    Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::JUMPFEnoughOutputs" [] =
    φ JUMPFEnoughOutputs.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_JUMPFEnoughOutputs : of_value.

  Lemma of_value_with_JUMPFStackHigherThanOutputs :
    Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::JUMPFStackHigherThanOutputs" [] =
    φ JUMPFStackHigherThanOutputs.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_JUMPFStackHigherThanOutputs : of_value.

  Lemma of_value_with_DataLoadOutOfBounds :
    Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::DataLoadOutOfBounds" [] =
    φ DataLoadOutOfBounds.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_DataLoadOutOfBounds : of_value.

  Lemma of_value_with_RETFBiggestStackNumMoreThenOutputs :
    Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::RETFBiggestStackNumMoreThenOutputs" [] =
    φ RETFBiggestStackNumMoreThenOutputs.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_RETFBiggestStackNumMoreThenOutputs : of_value.

  Lemma of_value_with_StackUnderflow :
    Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::StackUnderflow" [] =
    φ StackUnderflow.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_StackUnderflow : of_value.

  Lemma of_value_with_TypesStackUnderflow :
    Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::TypesStackUnderflow" [] =
    φ TypesStackUnderflow.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_TypesStackUnderflow : of_value.

  Lemma of_value_with_JumpUnderflow :
    Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::JumpUnderflow" [] =
    φ JumpUnderflow.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_JumpUnderflow : of_value.

  Lemma of_value_with_JumpOverflow :
    Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::JumpOverflow" [] =
    φ JumpOverflow.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_JumpOverflow : of_value.

  Lemma of_value_with_BackwardJumpBiggestNumMismatch :
    Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::BackwardJumpBiggestNumMismatch" [] =
    φ BackwardJumpBiggestNumMismatch.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_BackwardJumpBiggestNumMismatch : of_value.

  Lemma of_value_with_BackwardJumpSmallestNumMismatch :
    Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::BackwardJumpSmallestNumMismatch" [] =
    φ BackwardJumpSmallestNumMismatch.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_BackwardJumpSmallestNumMismatch : of_value.

  Lemma of_value_with_LastInstructionNotTerminating :
    Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::LastInstructionNotTerminating" [] =
    φ LastInstructionNotTerminating.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_LastInstructionNotTerminating : of_value.

  Lemma of_value_with_CodeSectionNotAccessed :
    Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::CodeSectionNotAccessed" [] =
    φ CodeSectionNotAccessed.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CodeSectionNotAccessed : of_value.

  Lemma of_value_with_InvalidTypesSection :
    Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::InvalidTypesSection" [] =
    φ InvalidTypesSection.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InvalidTypesSection : of_value.

  Lemma of_value_with_InvalidFirstTypesSection :
    Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::InvalidFirstTypesSection" [] =
    φ InvalidFirstTypesSection.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InvalidFirstTypesSection : of_value.

  Lemma of_value_with_MaxStackMismatch :
    Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::MaxStackMismatch" [] =
    φ MaxStackMismatch.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_MaxStackMismatch : of_value.

  Lemma of_value_with_NoCodeSections :
    Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::NoCodeSections" [] =
    φ NoCodeSections.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_NoCodeSections : of_value.

  Lemma of_value_with_SubContainerCalledInTwoModes :
    Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::SubContainerCalledInTwoModes" [] =
    φ SubContainerCalledInTwoModes.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_SubContainerCalledInTwoModes : of_value.

  Lemma of_value_with_SubContainerNotAccessed :
    Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::SubContainerNotAccessed" [] =
    φ SubContainerNotAccessed.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_SubContainerNotAccessed : of_value.

  Lemma of_value_with_DataNotFilled :
    Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::DataNotFilled" [] =
    φ DataNotFilled.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_DataNotFilled : of_value.

  Lemma of_value_with_NonReturningSectionIsReturning :
    Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::NonReturningSectionIsReturning" [] =
    φ NonReturningSectionIsReturning.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_NonReturningSectionIsReturning : of_value.

  Definition of_value_FalsePositive :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::FalsePositive" []
    ).
  Proof. econstructor; apply of_value_with_FalsePositive; eassumption. Defined.
  Smpl Add simple apply of_value_FalsePositive : of_value.

  Definition of_value_UnknownOpcode :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::UnknownOpcode" []
    ).
  Proof. econstructor; apply of_value_with_UnknownOpcode; eassumption. Defined.
  Smpl Add simple apply of_value_UnknownOpcode : of_value.

  Definition of_value_OpcodeDisabled :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::OpcodeDisabled" []
    ).
  Proof. econstructor; apply of_value_with_OpcodeDisabled; eassumption. Defined.
  Smpl Add simple apply of_value_OpcodeDisabled : of_value.

  Definition of_value_InstructionNotForwardAccessed :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::InstructionNotForwardAccessed" []
    ).
  Proof. econstructor; apply of_value_with_InstructionNotForwardAccessed; eassumption. Defined.
  Smpl Add simple apply of_value_InstructionNotForwardAccessed : of_value.

  Definition of_value_MissingImmediateBytes :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::MissingImmediateBytes" []
    ).
  Proof. econstructor; apply of_value_with_MissingImmediateBytes; eassumption. Defined.
  Smpl Add simple apply of_value_MissingImmediateBytes : of_value.

  Definition of_value_MissingRJUMPVImmediateBytes :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::MissingRJUMPVImmediateBytes" []
    ).
  Proof. econstructor; apply of_value_with_MissingRJUMPVImmediateBytes; eassumption. Defined.
  Smpl Add simple apply of_value_MissingRJUMPVImmediateBytes : of_value.

  Definition of_value_JumpToImmediateBytes :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::JumpToImmediateBytes" []
    ).
  Proof. econstructor; apply of_value_with_JumpToImmediateBytes; eassumption. Defined.
  Smpl Add simple apply of_value_JumpToImmediateBytes : of_value.

  Definition of_value_BackwardJumpToImmediateBytes :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::BackwardJumpToImmediateBytes" []
    ).
  Proof. econstructor; apply of_value_with_BackwardJumpToImmediateBytes; eassumption. Defined.
  Smpl Add simple apply of_value_BackwardJumpToImmediateBytes : of_value.

  Definition of_value_RJUMPVZeroMaxIndex :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::RJUMPVZeroMaxIndex" []
    ).
  Proof. econstructor; apply of_value_with_RJUMPVZeroMaxIndex; eassumption. Defined.
  Smpl Add simple apply of_value_RJUMPVZeroMaxIndex : of_value.

  Definition of_value_JumpZeroOffset :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::JumpZeroOffset" []
    ).
  Proof. econstructor; apply of_value_with_JumpZeroOffset; eassumption. Defined.
  Smpl Add simple apply of_value_JumpZeroOffset : of_value.

  Definition of_value_EOFCREATEInvalidIndex :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::EOFCREATEInvalidIndex" []
    ).
  Proof. econstructor; apply of_value_with_EOFCREATEInvalidIndex; eassumption. Defined.
  Smpl Add simple apply of_value_EOFCREATEInvalidIndex : of_value.

  Definition of_value_CodeSectionOutOfBounds :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::CodeSectionOutOfBounds" []
    ).
  Proof. econstructor; apply of_value_with_CodeSectionOutOfBounds; eassumption. Defined.
  Smpl Add simple apply of_value_CodeSectionOutOfBounds : of_value.

  Definition of_value_CALLFNonReturningFunction :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::CALLFNonReturningFunction" []
    ).
  Proof. econstructor; apply of_value_with_CALLFNonReturningFunction; eassumption. Defined.
  Smpl Add simple apply of_value_CALLFNonReturningFunction : of_value.

  Definition of_value_StackOverflow :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::StackOverflow" []
    ).
  Proof. econstructor; apply of_value_with_StackOverflow; eassumption. Defined.
  Smpl Add simple apply of_value_StackOverflow : of_value.

  Definition of_value_JUMPFEnoughOutputs :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::JUMPFEnoughOutputs" []
    ).
  Proof. econstructor; apply of_value_with_JUMPFEnoughOutputs; eassumption. Defined.
  Smpl Add simple apply of_value_JUMPFEnoughOutputs : of_value.

  Definition of_value_JUMPFStackHigherThanOutputs :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::JUMPFStackHigherThanOutputs" []
    ).
  Proof. econstructor; apply of_value_with_JUMPFStackHigherThanOutputs; eassumption. Defined.
  Smpl Add simple apply of_value_JUMPFStackHigherThanOutputs : of_value.

  Definition of_value_DataLoadOutOfBounds :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::DataLoadOutOfBounds" []
    ).
  Proof. econstructor; apply of_value_with_DataLoadOutOfBounds; eassumption. Defined.
  Smpl Add simple apply of_value_DataLoadOutOfBounds : of_value.

  Definition of_value_RETFBiggestStackNumMoreThenOutputs :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::RETFBiggestStackNumMoreThenOutputs" []
    ).
  Proof. econstructor; apply of_value_with_RETFBiggestStackNumMoreThenOutputs; eassumption. Defined.
  Smpl Add simple apply of_value_RETFBiggestStackNumMoreThenOutputs : of_value.

  Definition of_value_StackUnderflow :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::StackUnderflow" []
    ).
  Proof. econstructor; apply of_value_with_StackUnderflow; eassumption. Defined.
  Smpl Add simple apply of_value_StackUnderflow : of_value.

  Definition of_value_TypesStackUnderflow :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::TypesStackUnderflow" []
    ).
  Proof. econstructor; apply of_value_with_TypesStackUnderflow; eassumption. Defined.
  Smpl Add simple apply of_value_TypesStackUnderflow : of_value.

  Definition of_value_JumpUnderflow :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::JumpUnderflow" []
    ).
  Proof. econstructor; apply of_value_with_JumpUnderflow; eassumption. Defined.
  Smpl Add simple apply of_value_JumpUnderflow : of_value.

  Definition of_value_JumpOverflow :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::JumpOverflow" []
    ).
  Proof. econstructor; apply of_value_with_JumpOverflow; eassumption. Defined.
  Smpl Add simple apply of_value_JumpOverflow : of_value.

  Definition of_value_BackwardJumpBiggestNumMismatch :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::BackwardJumpBiggestNumMismatch" []
    ).
  Proof. econstructor; apply of_value_with_BackwardJumpBiggestNumMismatch; eassumption. Defined.
  Smpl Add simple apply of_value_BackwardJumpBiggestNumMismatch : of_value.

  Definition of_value_BackwardJumpSmallestNumMismatch :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::BackwardJumpSmallestNumMismatch" []
    ).
  Proof. econstructor; apply of_value_with_BackwardJumpSmallestNumMismatch; eassumption. Defined.
  Smpl Add simple apply of_value_BackwardJumpSmallestNumMismatch : of_value.

  Definition of_value_LastInstructionNotTerminating :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::LastInstructionNotTerminating" []
    ).
  Proof. econstructor; apply of_value_with_LastInstructionNotTerminating; eassumption. Defined.
  Smpl Add simple apply of_value_LastInstructionNotTerminating : of_value.

  Definition of_value_CodeSectionNotAccessed :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::CodeSectionNotAccessed" []
    ).
  Proof. econstructor; apply of_value_with_CodeSectionNotAccessed; eassumption. Defined.
  Smpl Add simple apply of_value_CodeSectionNotAccessed : of_value.

  Definition of_value_InvalidTypesSection :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::InvalidTypesSection" []
    ).
  Proof. econstructor; apply of_value_with_InvalidTypesSection; eassumption. Defined.
  Smpl Add simple apply of_value_InvalidTypesSection : of_value.

  Definition of_value_InvalidFirstTypesSection :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::InvalidFirstTypesSection" []
    ).
  Proof. econstructor; apply of_value_with_InvalidFirstTypesSection; eassumption. Defined.
  Smpl Add simple apply of_value_InvalidFirstTypesSection : of_value.

  Definition of_value_MaxStackMismatch :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::MaxStackMismatch" []
    ).
  Proof. econstructor; apply of_value_with_MaxStackMismatch; eassumption. Defined.
  Smpl Add simple apply of_value_MaxStackMismatch : of_value.

  Definition of_value_NoCodeSections :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::NoCodeSections" []
    ).
  Proof. econstructor; apply of_value_with_NoCodeSections; eassumption. Defined.
  Smpl Add simple apply of_value_NoCodeSections : of_value.

  Definition of_value_SubContainerCalledInTwoModes :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::SubContainerCalledInTwoModes" []
    ).
  Proof. econstructor; apply of_value_with_SubContainerCalledInTwoModes; eassumption. Defined.
  Smpl Add simple apply of_value_SubContainerCalledInTwoModes : of_value.

  Definition of_value_SubContainerNotAccessed :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::SubContainerNotAccessed" []
    ).
  Proof. econstructor; apply of_value_with_SubContainerNotAccessed; eassumption. Defined.
  Smpl Add simple apply of_value_SubContainerNotAccessed : of_value.

  Definition of_value_DataNotFilled :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::DataNotFilled" []
    ).
  Proof. econstructor; apply of_value_with_DataNotFilled; eassumption. Defined.
  Smpl Add simple apply of_value_DataNotFilled : of_value.

  Definition of_value_NonReturningSectionIsReturning :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::NonReturningSectionIsReturning" []
    ).
  Proof. econstructor; apply of_value_with_NonReturningSectionIsReturning; eassumption. Defined.
  Smpl Add simple apply of_value_NonReturningSectionIsReturning : of_value.
End EofValidationError.

Module AccessTracker.
  Record t : Set := {
    this_container_code_type: core.links.option.Option.t revm_bytecode.eof.links.verification.CodeType.t;
    codes: alloc.links.vec.Vec.t bool alloc.links.alloc.Global.t;
    processing_stack: alloc.links.vec.Vec.t Usize.t alloc.links.alloc.Global.t;
    subcontainers: alloc.links.vec.Vec.t (core.links.option.Option.t revm_bytecode.eof.links.verification.CodeType.t) alloc.links.alloc.Global.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_bytecode::eof::verification::AccessTracker";
    φ '(Build_t this_container_code_type codes processing_stack subcontainers) :=
      Value.StructRecord "revm_bytecode::eof::verification::AccessTracker" [
        ("this_container_code_type", φ this_container_code_type);
        ("codes", φ codes);
        ("processing_stack", φ processing_stack);
        ("subcontainers", φ subcontainers)
      ]
  }.
End AccessTracker.

Module CodeType.
  Inductive t : Set :=
  | ReturnContract
  | ReturnOrStop
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_bytecode::eof::verification::CodeType";
    φ x :=
      match x with
      | ReturnContract =>
        Value.StructTuple "revm_bytecode::eof::verification::CodeType::ReturnContract" []
      | ReturnOrStop =>
        Value.StructTuple "revm_bytecode::eof::verification::CodeType::ReturnOrStop" []
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_bytecode::eof::verification::CodeType").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_ReturnContract :
    Value.StructTuple "revm_bytecode::eof::verification::CodeType::ReturnContract" [] =
    φ ReturnContract.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_ReturnContract : of_value.

  Lemma of_value_with_ReturnOrStop :
    Value.StructTuple "revm_bytecode::eof::verification::CodeType::ReturnOrStop" [] =
    φ ReturnOrStop.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_ReturnOrStop : of_value.

  Definition of_value_ReturnContract :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::verification::CodeType::ReturnContract" []
    ).
  Proof. econstructor; apply of_value_with_ReturnContract; eassumption. Defined.
  Smpl Add simple apply of_value_ReturnContract : of_value.

  Definition of_value_ReturnOrStop :
    OfValue.t (
      Value.StructTuple "revm_bytecode::eof::verification::CodeType::ReturnOrStop" []
    ).
  Proof. econstructor; apply of_value_with_ReturnOrStop; eassumption. Defined.
  Smpl Add simple apply of_value_ReturnOrStop : of_value.
End CodeType.

Module InstructionInfo.
  Record t : Set := {
    is_immediate: bool;
    is_jumpdest: bool;
    smallest: I32.t;
    biggest: I32.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_bytecode::eof::verification::validate_eof_code::InstructionInfo";
    φ '(Build_t is_immediate is_jumpdest smallest biggest) :=
      Value.StructRecord "revm_bytecode::eof::verification::validate_eof_code::InstructionInfo" [
        ("is_immediate", φ is_immediate);
        ("is_jumpdest", φ is_jumpdest);
        ("smallest", φ smallest);
        ("biggest", φ biggest)
      ]
  }.
End InstructionInfo.

Module LegacyAnalyzedBytecode.
  Record t : Set := {
    bytecode: alloy_primitives.links.bytes_.Bytes.t;
    original_len: Usize.t;
    jump_table: revm_bytecode.legacy.links.jump_map.JumpTable.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_bytecode::legacy::analyzed::LegacyAnalyzedBytecode";
    φ '(Build_t bytecode original_len jump_table) :=
      Value.StructRecord "revm_bytecode::legacy::analyzed::LegacyAnalyzedBytecode" [
        ("bytecode", φ bytecode);
        ("original_len", φ original_len);
        ("jump_table", φ jump_table)
      ]
  }.
End LegacyAnalyzedBytecode.

Module AnalysisKind.
  Inductive t : Set :=
  | Raw
  | Analyse
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_context_interface::cfg::AnalysisKind";
    φ x :=
      match x with
      | Raw =>
        Value.StructTuple "revm_context_interface::cfg::AnalysisKind::Raw" []
      | Analyse =>
        Value.StructTuple "revm_context_interface::cfg::AnalysisKind::Analyse" []
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_context_interface::cfg::AnalysisKind").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_Raw :
    Value.StructTuple "revm_context_interface::cfg::AnalysisKind::Raw" [] =
    φ Raw.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Raw : of_value.

  Lemma of_value_with_Analyse :
    Value.StructTuple "revm_context_interface::cfg::AnalysisKind::Analyse" [] =
    φ Analyse.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Analyse : of_value.

  Definition of_value_Raw :
    OfValue.t (
      Value.StructTuple "revm_context_interface::cfg::AnalysisKind::Raw" []
    ).
  Proof. econstructor; apply of_value_with_Raw; eassumption. Defined.
  Smpl Add simple apply of_value_Raw : of_value.

  Definition of_value_Analyse :
    OfValue.t (
      Value.StructTuple "revm_context_interface::cfg::AnalysisKind::Analyse" []
    ).
  Proof. econstructor; apply of_value_with_Analyse; eassumption. Defined.
  Smpl Add simple apply of_value_Analyse : of_value.
End AnalysisKind.

Module CreateScheme.
  Inductive t : Set :=
  | Create
  | Create2
    (salt : ruint.Uint.t 256 4)
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_context_interface::cfg::CreateScheme";
    φ x :=
      match x with
      | Create =>
        Value.StructTuple "revm_context_interface::cfg::CreateScheme::Create" []
      | Create2 salt =>
        Value.StructRecord "revm_context_interface::cfg::CreateScheme::Create2" [
          ("salt", φ salt)
        ]
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_context_interface::cfg::CreateScheme").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_Create :
    Value.StructTuple "revm_context_interface::cfg::CreateScheme::Create" [] =
    φ Create.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Create : of_value.

  Lemma of_value_with_Create2
    (salt : ruint.Uint.t 256 4) (salt' : Value.t) :
    salt' = φ salt ->
    Value.StructRecord "revm_context_interface::cfg::CreateScheme::Create2" [
      ("salt", salt')
    ] =
    φ (Create2 salt).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Create2 : of_value.

  Definition of_value_Create :
    OfValue.t (
      Value.StructTuple "revm_context_interface::cfg::CreateScheme::Create" []
    ).
  Proof. econstructor; apply of_value_with_Create; eassumption. Defined.
  Smpl Add simple apply of_value_Create : of_value.

  Definition of_value_Create2
    (salt : ruint.Uint.t 256 4) (salt' : Value.t) :
    salt' = φ salt ->
    OfValue.t (
      Value.StructRecord "revm_context_interface::cfg::CreateScheme::Create2" [
        ("salt", salt')
      ]
    ).
  Proof. econstructor; apply of_value_with_Create2; eassumption. Defined.
  Smpl Add simple apply of_value_Create2 : of_value.
End CreateScheme.

Module SStoreResult.
  Record t : Set := {
    original_value: ruint.Uint.t 256 4;
    present_value: ruint.Uint.t 256 4;
    new_value: ruint.Uint.t 256 4;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_context_interface::host::SStoreResult";
    φ '(Build_t original_value present_value new_value) :=
      Value.StructRecord "revm_context_interface::host::SStoreResult" [
        ("original_value", φ original_value);
        ("present_value", φ present_value);
        ("new_value", φ new_value)
      ]
  }.
End SStoreResult.

Module SelfDestructResult.
  Record t : Set := {
    had_value: bool;
    target_exists: bool;
    previously_destroyed: bool;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_context_interface::host::SelfDestructResult";
    φ '(Build_t had_value target_exists previously_destroyed) :=
      Value.StructRecord "revm_context_interface::host::SelfDestructResult" [
        ("had_value", φ had_value);
        ("target_exists", φ target_exists);
        ("previously_destroyed", φ previously_destroyed)
      ]
  }.
End SelfDestructResult.

Module TransferError.
  Inductive t : Set :=
  | OutOfFunds
  | OverflowPayment
  | CreateCollision
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_context_interface::journaled_state::TransferError";
    φ x :=
      match x with
      | OutOfFunds =>
        Value.StructTuple "revm_context_interface::journaled_state::TransferError::OutOfFunds" []
      | OverflowPayment =>
        Value.StructTuple "revm_context_interface::journaled_state::TransferError::OverflowPayment" []
      | CreateCollision =>
        Value.StructTuple "revm_context_interface::journaled_state::TransferError::CreateCollision" []
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_context_interface::journaled_state::TransferError").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_OutOfFunds :
    Value.StructTuple "revm_context_interface::journaled_state::TransferError::OutOfFunds" [] =
    φ OutOfFunds.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_OutOfFunds : of_value.

  Lemma of_value_with_OverflowPayment :
    Value.StructTuple "revm_context_interface::journaled_state::TransferError::OverflowPayment" [] =
    φ OverflowPayment.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_OverflowPayment : of_value.

  Lemma of_value_with_CreateCollision :
    Value.StructTuple "revm_context_interface::journaled_state::TransferError::CreateCollision" [] =
    φ CreateCollision.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CreateCollision : of_value.

  Definition of_value_OutOfFunds :
    OfValue.t (
      Value.StructTuple "revm_context_interface::journaled_state::TransferError::OutOfFunds" []
    ).
  Proof. econstructor; apply of_value_with_OutOfFunds; eassumption. Defined.
  Smpl Add simple apply of_value_OutOfFunds : of_value.

  Definition of_value_OverflowPayment :
    OfValue.t (
      Value.StructTuple "revm_context_interface::journaled_state::TransferError::OverflowPayment" []
    ).
  Proof. econstructor; apply of_value_with_OverflowPayment; eassumption. Defined.
  Smpl Add simple apply of_value_OverflowPayment : of_value.

  Definition of_value_CreateCollision :
    OfValue.t (
      Value.StructTuple "revm_context_interface::journaled_state::TransferError::CreateCollision" []
    ).
  Proof. econstructor; apply of_value_with_CreateCollision; eassumption. Defined.
  Smpl Add simple apply of_value_CreateCollision : of_value.
End TransferError.

Module JournalCheckpoint.
  Record t : Set := {
    log_i: Usize.t;
    journal_i: Usize.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_context_interface::journaled_state::JournalCheckpoint";
    φ '(Build_t log_i journal_i) :=
      Value.StructRecord "revm_context_interface::journaled_state::JournalCheckpoint" [
        ("log_i", φ log_i);
        ("journal_i", φ journal_i)
      ]
  }.
End JournalCheckpoint.

Module StateLoad.
  Record t {T: Set} : Set := {
    data: T;
    is_cold: bool;
  }.
  Arguments Build_t {_}.
  Arguments t : clear implicits.

  Global Instance IsLink {T: Set} `{Link T} : Link (t T) := {
    Φ := Ty.path "revm_context_interface::journaled_state::StateLoad";
    φ '(Build_t data is_cold) :=
      Value.StructRecord "revm_context_interface::journaled_state::StateLoad" [
        ("data", φ data);
        ("is_cold", φ is_cold)
      ]
  }.
End StateLoad.

Module AccountLoad.
  Record t : Set := {
    load: revm_context_interface.links.journaled_state.Eip7702CodeLoad.t ();
    is_empty: bool;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_context_interface::journaled_state::AccountLoad";
    φ '(Build_t load is_empty) :=
      Value.StructRecord "revm_context_interface::journaled_state::AccountLoad" [
        ("load", φ load);
        ("is_empty", φ is_empty)
      ]
  }.
End AccountLoad.

Module Eip7702CodeLoad.
  Record t {T: Set} : Set := {
    state_load: revm_context_interface.links.journaled_state.StateLoad.t T;
    is_delegate_account_cold: core.links.option.Option.t bool;
  }.
  Arguments Build_t {_}.
  Arguments t : clear implicits.

  Global Instance IsLink {T: Set} `{Link T} : Link (t T) := {
    Φ := Ty.path "revm_context_interface::journaled_state::Eip7702CodeLoad";
    φ '(Build_t state_load is_delegate_account_cold) :=
      Value.StructRecord "revm_context_interface::journaled_state::Eip7702CodeLoad" [
        ("state_load", φ state_load);
        ("is_delegate_account_cold", φ is_delegate_account_cold)
      ]
  }.
End Eip7702CodeLoad.

Module ResultAndState.
  Record t {HaltReasonT: Set} : Set := {
    result: revm_context_interface.links.result.ExecutionResult.t HaltReasonT;
    state: hashbrown.links.map.HashMap.t alloy_primitives.bits.links.address.Address.t revm_state.Account.t foldhash.seed.links.fast.RandomState.t hashbrown.raw.alloc.links.inner.Global.t;
  }.
  Arguments Build_t {_}.
  Arguments t : clear implicits.

  Global Instance IsLink {HaltReasonT: Set} `{Link HaltReasonT} : Link (t HaltReasonT) := {
    Φ := Ty.path "revm_context_interface::result::ResultAndState";
    φ '(Build_t result state) :=
      Value.StructRecord "revm_context_interface::result::ResultAndState" [
        ("result", φ result);
        ("state", φ state)
      ]
  }.
End ResultAndState.

Module ExecutionResult.
  Inductive t (HaltReasonT: Set) : Set :=
  | Success
    (reason : revm_context_interface.links.result.SuccessReason.t)
    (gas_used : U64.t)
    (gas_refunded : U64.t)
    (logs : alloc.links.vec.Vec.t (alloy_primitives.links.log.Log.t alloy_primitives.links.log.LogData.t) alloc.links.alloc.Global.t)
    (output : revm_context_interface.links.result.Output.t)
  | Revert
    (gas_used : U64.t)
    (output : alloy_primitives.links.bytes_.Bytes.t)
  | Halt
    (reason : HaltReasonT)
    (gas_used : U64.t)
  .
  Arguments Success Revert Halt {_}.

  Global Instance IsLink (HaltReasonT: Set) : Link t HaltReasonT := {
    Φ := Ty.path "revm_context_interface::result::ExecutionResult";
    φ x :=
      match x with
      | Success reason gas_used gas_refunded logs output =>
        Value.StructRecord "revm_context_interface::result::ExecutionResult::Success" [
          ("reason", φ reason);
          ("gas_used", φ gas_used);
          ("gas_refunded", φ gas_refunded);
          ("logs", φ logs);
          ("output", φ output)
        ]
      | Revert gas_used output =>
        Value.StructRecord "revm_context_interface::result::ExecutionResult::Revert" [
          ("gas_used", φ gas_used);
          ("output", φ output)
        ]
      | Halt reason gas_used =>
        Value.StructRecord "revm_context_interface::result::ExecutionResult::Halt" [
          ("reason", φ reason);
          ("gas_used", φ gas_used)
        ]
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_context_interface::result::ExecutionResult").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_Success
    (reason : revm_context_interface.links.result.SuccessReason.t) (reason' : Value.t)
    (gas_used : U64.t) (gas_used' : Value.t)
    (gas_refunded : U64.t) (gas_refunded' : Value.t)
    (logs : alloc.links.vec.Vec.t (alloy_primitives.links.log.Log.t alloy_primitives.links.log.LogData.t) alloc.links.alloc.Global.t) (logs' : Value.t)
    (output : revm_context_interface.links.result.Output.t) (output' : Value.t) :
    reason' = φ reason ->
    gas_used' = φ gas_used ->
    gas_refunded' = φ gas_refunded ->
    logs' = φ logs ->
    output' = φ output ->
    Value.StructRecord "revm_context_interface::result::ExecutionResult::Success" [
      ("reason", reason');
      ("gas_used", gas_used');
      ("gas_refunded", gas_refunded');
      ("logs", logs');
      ("output", output')
    ] =
    φ (Success reason gas_used gas_refunded logs output).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Success : of_value.

  Lemma of_value_with_Revert
    (gas_used : U64.t) (gas_used' : Value.t)
    (output : alloy_primitives.links.bytes_.Bytes.t) (output' : Value.t) :
    gas_used' = φ gas_used ->
    output' = φ output ->
    Value.StructRecord "revm_context_interface::result::ExecutionResult::Revert" [
      ("gas_used", gas_used');
      ("output", output')
    ] =
    φ (Revert gas_used output).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Revert : of_value.

  Lemma of_value_with_Halt
    (reason : HaltReasonT) (reason' : Value.t)
    (gas_used : U64.t) (gas_used' : Value.t) :
    reason' = φ reason ->
    gas_used' = φ gas_used ->
    Value.StructRecord "revm_context_interface::result::ExecutionResult::Halt" [
      ("reason", reason');
      ("gas_used", gas_used')
    ] =
    φ (Halt reason gas_used).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Halt : of_value.

  Definition of_value_Success
    (reason : revm_context_interface.links.result.SuccessReason.t) (reason' : Value.t)
    (gas_used : U64.t) (gas_used' : Value.t)
    (gas_refunded : U64.t) (gas_refunded' : Value.t)
    (logs : alloc.links.vec.Vec.t (alloy_primitives.links.log.Log.t alloy_primitives.links.log.LogData.t) alloc.links.alloc.Global.t) (logs' : Value.t)
    (output : revm_context_interface.links.result.Output.t) (output' : Value.t) :
    reason' = φ reason ->
    gas_used' = φ gas_used ->
    gas_refunded' = φ gas_refunded ->
    logs' = φ logs ->
    output' = φ output ->
    OfValue.t (
      Value.StructRecord "revm_context_interface::result::ExecutionResult::Success" [
        ("reason", reason');
        ("gas_used", gas_used');
        ("gas_refunded", gas_refunded');
        ("logs", logs');
        ("output", output')
      ]
    ).
  Proof. econstructor; apply of_value_with_Success; eassumption. Defined.
  Smpl Add simple apply of_value_Success : of_value.

  Definition of_value_Revert
    (gas_used : U64.t) (gas_used' : Value.t)
    (output : alloy_primitives.links.bytes_.Bytes.t) (output' : Value.t) :
    gas_used' = φ gas_used ->
    output' = φ output ->
    OfValue.t (
      Value.StructRecord "revm_context_interface::result::ExecutionResult::Revert" [
        ("gas_used", gas_used');
        ("output", output')
      ]
    ).
  Proof. econstructor; apply of_value_with_Revert; eassumption. Defined.
  Smpl Add simple apply of_value_Revert : of_value.

  Definition of_value_Halt
    (reason : HaltReasonT) (reason' : Value.t)
    (gas_used : U64.t) (gas_used' : Value.t) :
    reason' = φ reason ->
    gas_used' = φ gas_used ->
    OfValue.t (
      Value.StructRecord "revm_context_interface::result::ExecutionResult::Halt" [
        ("reason", reason');
        ("gas_used", gas_used')
      ]
    ).
  Proof. econstructor; apply of_value_with_Halt; eassumption. Defined.
  Smpl Add simple apply of_value_Halt : of_value.
End ExecutionResult.

Module Output.
  Inductive t : Set :=
  | Call
    (_ : alloy_primitives.links.bytes_.Bytes.t)
  | Create
    (_ : alloy_primitives.links.bytes_.Bytes.t)
    (_ : core.links.option.Option.t alloy_primitives.bits.links.address.Address.t)
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_context_interface::result::Output";
    φ x :=
      match x with
      | Call γ0 =>
        Value.StructTuple "revm_context_interface::result::Output::Call" [
          φ γ0
        ]
      | Create γ0 γ1 =>
        Value.StructTuple "revm_context_interface::result::Output::Create" [
          φ γ0;
          φ γ1
        ]
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_context_interface::result::Output").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_Call
    (γ0 : alloy_primitives.links.bytes_.Bytes.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_context_interface::result::Output::Call" [
      γ0
    ] =
    φ (Call γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Call : of_value.

  Lemma of_value_with_Create
    (γ0 : alloy_primitives.links.bytes_.Bytes.t) (γ0' : Value.t)
    (γ1 : core.links.option.Option.t alloy_primitives.bits.links.address.Address.t) (γ1' : Value.t) :
    γ0' = φ γ0 ->
    γ1' = φ γ1 ->
    Value.StructTuple "revm_context_interface::result::Output::Create" [
      γ0;
      γ1
    ] =
    φ (Create γ0 γ1).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Create : of_value.

  Definition of_value_Call
    (γ0 : alloy_primitives.links.bytes_.Bytes.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::Output::Call" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Call; eassumption. Defined.
  Smpl Add simple apply of_value_Call : of_value.

  Definition of_value_Create
    (γ0 : alloy_primitives.links.bytes_.Bytes.t) (γ0' : Value.t)
    (γ1 : core.links.option.Option.t alloy_primitives.bits.links.address.Address.t) (γ1' : Value.t) :
    γ0' = φ γ0 ->
    γ1' = φ γ1 ->
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::Output::Create" [
        γ0;
        γ1
      ]
    ).
  Proof. econstructor; apply of_value_with_Create; eassumption. Defined.
  Smpl Add simple apply of_value_Create : of_value.
End Output.

Module EVMError.
  Inductive t (DBError TransactionError: Set) : Set :=
  | Transaction
    (_ : TransactionError)
  | Header
    (_ : revm_context_interface.links.result.InvalidHeader.t)
  | Database
    (_ : DBError)
  | Custom
    (_ : alloc.links.string.String.t)
  | Precompile
    (_ : alloc.links.string.String.t)
  .
  Arguments Transaction Header Database Custom Precompile {_ _}.

  Global Instance IsLink (DBError TransactionError: Set) : Link t DBError TransactionError := {
    Φ := Ty.path "revm_context_interface::result::EVMError";
    φ x :=
      match x with
      | Transaction γ0 =>
        Value.StructTuple "revm_context_interface::result::EVMError::Transaction" [
          φ γ0
        ]
      | Header γ0 =>
        Value.StructTuple "revm_context_interface::result::EVMError::Header" [
          φ γ0
        ]
      | Database γ0 =>
        Value.StructTuple "revm_context_interface::result::EVMError::Database" [
          φ γ0
        ]
      | Custom γ0 =>
        Value.StructTuple "revm_context_interface::result::EVMError::Custom" [
          φ γ0
        ]
      | Precompile γ0 =>
        Value.StructTuple "revm_context_interface::result::EVMError::Precompile" [
          φ γ0
        ]
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_context_interface::result::EVMError").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_Transaction
    (γ0 : TransactionError) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_context_interface::result::EVMError::Transaction" [
      γ0
    ] =
    φ (Transaction γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Transaction : of_value.

  Lemma of_value_with_Header
    (γ0 : revm_context_interface.links.result.InvalidHeader.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_context_interface::result::EVMError::Header" [
      γ0
    ] =
    φ (Header γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Header : of_value.

  Lemma of_value_with_Database
    (γ0 : DBError) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_context_interface::result::EVMError::Database" [
      γ0
    ] =
    φ (Database γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Database : of_value.

  Lemma of_value_with_Custom
    (γ0 : alloc.links.string.String.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_context_interface::result::EVMError::Custom" [
      γ0
    ] =
    φ (Custom γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Custom : of_value.

  Lemma of_value_with_Precompile
    (γ0 : alloc.links.string.String.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_context_interface::result::EVMError::Precompile" [
      γ0
    ] =
    φ (Precompile γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Precompile : of_value.

  Definition of_value_Transaction
    (γ0 : TransactionError) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::EVMError::Transaction" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Transaction; eassumption. Defined.
  Smpl Add simple apply of_value_Transaction : of_value.

  Definition of_value_Header
    (γ0 : revm_context_interface.links.result.InvalidHeader.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::EVMError::Header" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Header; eassumption. Defined.
  Smpl Add simple apply of_value_Header : of_value.

  Definition of_value_Database
    (γ0 : DBError) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::EVMError::Database" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Database; eassumption. Defined.
  Smpl Add simple apply of_value_Database : of_value.

  Definition of_value_Custom
    (γ0 : alloc.links.string.String.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::EVMError::Custom" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Custom; eassumption. Defined.
  Smpl Add simple apply of_value_Custom : of_value.

  Definition of_value_Precompile
    (γ0 : alloc.links.string.String.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::EVMError::Precompile" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Precompile; eassumption. Defined.
  Smpl Add simple apply of_value_Precompile : of_value.
End EVMError.

Module InvalidTransaction.
  Inductive t : Set :=
  | PriorityFeeGreaterThanMaxFee
  | GasPriceLessThanBasefee
  | CallerGasLimitMoreThanBlock
  | CallGasCostMoreThanGasLimit
  | RejectCallerWithCode
  | LackOfFundForMaxFee
    (fee : alloc.links.boxed.Box.t (ruint.Uint.t 256 4) alloc.links.alloc.Global.t)
    (balance : alloc.links.boxed.Box.t (ruint.Uint.t 256 4) alloc.links.alloc.Global.t)
  | OverflowPaymentInTransaction
  | NonceOverflowInTransaction
  | NonceTooHigh
    (tx : U64.t)
    (state : U64.t)
  | NonceTooLow
    (tx : U64.t)
    (state : U64.t)
  | CreateInitCodeSizeLimit
  | InvalidChainId
  | AccessListNotSupported
  | MaxFeePerBlobGasNotSupported
  | BlobVersionedHashesNotSupported
  | BlobGasPriceGreaterThanMax
  | EmptyBlobs
  | BlobCreateTransaction
  | TooManyBlobs
    (max : Usize.t)
    (have : Usize.t)
  | BlobVersionNotSupported
  | EofCrateShouldHaveToAddress
  | AuthorizationListNotSupported
  | AuthorizationListInvalidFields
  | EmptyAuthorizationList
  | InvalidAuthorizationList
    (_ : revm_specification.eip7702.links.authorization_list.InvalidAuthorization.t)
  | Eip2930NotSupported
  | Eip1559NotSupported
  | Eip4844NotSupported
  | Eip7702NotSupported
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_context_interface::result::InvalidTransaction";
    φ x :=
      match x with
      | PriorityFeeGreaterThanMaxFee =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::PriorityFeeGreaterThanMaxFee" []
      | GasPriceLessThanBasefee =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::GasPriceLessThanBasefee" []
      | CallerGasLimitMoreThanBlock =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::CallerGasLimitMoreThanBlock" []
      | CallGasCostMoreThanGasLimit =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::CallGasCostMoreThanGasLimit" []
      | RejectCallerWithCode =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::RejectCallerWithCode" []
      | LackOfFundForMaxFee fee balance =>
        Value.StructRecord "revm_context_interface::result::InvalidTransaction::LackOfFundForMaxFee" [
          ("fee", φ fee);
          ("balance", φ balance)
        ]
      | OverflowPaymentInTransaction =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::OverflowPaymentInTransaction" []
      | NonceOverflowInTransaction =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::NonceOverflowInTransaction" []
      | NonceTooHigh tx state =>
        Value.StructRecord "revm_context_interface::result::InvalidTransaction::NonceTooHigh" [
          ("tx", φ tx);
          ("state", φ state)
        ]
      | NonceTooLow tx state =>
        Value.StructRecord "revm_context_interface::result::InvalidTransaction::NonceTooLow" [
          ("tx", φ tx);
          ("state", φ state)
        ]
      | CreateInitCodeSizeLimit =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::CreateInitCodeSizeLimit" []
      | InvalidChainId =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::InvalidChainId" []
      | AccessListNotSupported =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::AccessListNotSupported" []
      | MaxFeePerBlobGasNotSupported =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::MaxFeePerBlobGasNotSupported" []
      | BlobVersionedHashesNotSupported =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::BlobVersionedHashesNotSupported" []
      | BlobGasPriceGreaterThanMax =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::BlobGasPriceGreaterThanMax" []
      | EmptyBlobs =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::EmptyBlobs" []
      | BlobCreateTransaction =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::BlobCreateTransaction" []
      | TooManyBlobs max have =>
        Value.StructRecord "revm_context_interface::result::InvalidTransaction::TooManyBlobs" [
          ("max", φ max);
          ("have", φ have)
        ]
      | BlobVersionNotSupported =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::BlobVersionNotSupported" []
      | EofCrateShouldHaveToAddress =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::EofCrateShouldHaveToAddress" []
      | AuthorizationListNotSupported =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::AuthorizationListNotSupported" []
      | AuthorizationListInvalidFields =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::AuthorizationListInvalidFields" []
      | EmptyAuthorizationList =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::EmptyAuthorizationList" []
      | InvalidAuthorizationList γ0 =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::InvalidAuthorizationList" [
          φ γ0
        ]
      | Eip2930NotSupported =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::Eip2930NotSupported" []
      | Eip1559NotSupported =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::Eip1559NotSupported" []
      | Eip4844NotSupported =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::Eip4844NotSupported" []
      | Eip7702NotSupported =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::Eip7702NotSupported" []
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_context_interface::result::InvalidTransaction").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_PriorityFeeGreaterThanMaxFee :
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::PriorityFeeGreaterThanMaxFee" [] =
    φ PriorityFeeGreaterThanMaxFee.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_PriorityFeeGreaterThanMaxFee : of_value.

  Lemma of_value_with_GasPriceLessThanBasefee :
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::GasPriceLessThanBasefee" [] =
    φ GasPriceLessThanBasefee.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_GasPriceLessThanBasefee : of_value.

  Lemma of_value_with_CallerGasLimitMoreThanBlock :
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::CallerGasLimitMoreThanBlock" [] =
    φ CallerGasLimitMoreThanBlock.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CallerGasLimitMoreThanBlock : of_value.

  Lemma of_value_with_CallGasCostMoreThanGasLimit :
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::CallGasCostMoreThanGasLimit" [] =
    φ CallGasCostMoreThanGasLimit.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CallGasCostMoreThanGasLimit : of_value.

  Lemma of_value_with_RejectCallerWithCode :
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::RejectCallerWithCode" [] =
    φ RejectCallerWithCode.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_RejectCallerWithCode : of_value.

  Lemma of_value_with_LackOfFundForMaxFee
    (fee : alloc.links.boxed.Box.t (ruint.Uint.t 256 4) alloc.links.alloc.Global.t) (fee' : Value.t)
    (balance : alloc.links.boxed.Box.t (ruint.Uint.t 256 4) alloc.links.alloc.Global.t) (balance' : Value.t) :
    fee' = φ fee ->
    balance' = φ balance ->
    Value.StructRecord "revm_context_interface::result::InvalidTransaction::LackOfFundForMaxFee" [
      ("fee", fee');
      ("balance", balance')
    ] =
    φ (LackOfFundForMaxFee fee balance).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_LackOfFundForMaxFee : of_value.

  Lemma of_value_with_OverflowPaymentInTransaction :
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::OverflowPaymentInTransaction" [] =
    φ OverflowPaymentInTransaction.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_OverflowPaymentInTransaction : of_value.

  Lemma of_value_with_NonceOverflowInTransaction :
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::NonceOverflowInTransaction" [] =
    φ NonceOverflowInTransaction.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_NonceOverflowInTransaction : of_value.

  Lemma of_value_with_NonceTooHigh
    (tx : U64.t) (tx' : Value.t)
    (state : U64.t) (state' : Value.t) :
    tx' = φ tx ->
    state' = φ state ->
    Value.StructRecord "revm_context_interface::result::InvalidTransaction::NonceTooHigh" [
      ("tx", tx');
      ("state", state')
    ] =
    φ (NonceTooHigh tx state).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_NonceTooHigh : of_value.

  Lemma of_value_with_NonceTooLow
    (tx : U64.t) (tx' : Value.t)
    (state : U64.t) (state' : Value.t) :
    tx' = φ tx ->
    state' = φ state ->
    Value.StructRecord "revm_context_interface::result::InvalidTransaction::NonceTooLow" [
      ("tx", tx');
      ("state", state')
    ] =
    φ (NonceTooLow tx state).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_NonceTooLow : of_value.

  Lemma of_value_with_CreateInitCodeSizeLimit :
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::CreateInitCodeSizeLimit" [] =
    φ CreateInitCodeSizeLimit.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CreateInitCodeSizeLimit : of_value.

  Lemma of_value_with_InvalidChainId :
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::InvalidChainId" [] =
    φ InvalidChainId.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InvalidChainId : of_value.

  Lemma of_value_with_AccessListNotSupported :
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::AccessListNotSupported" [] =
    φ AccessListNotSupported.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_AccessListNotSupported : of_value.

  Lemma of_value_with_MaxFeePerBlobGasNotSupported :
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::MaxFeePerBlobGasNotSupported" [] =
    φ MaxFeePerBlobGasNotSupported.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_MaxFeePerBlobGasNotSupported : of_value.

  Lemma of_value_with_BlobVersionedHashesNotSupported :
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::BlobVersionedHashesNotSupported" [] =
    φ BlobVersionedHashesNotSupported.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_BlobVersionedHashesNotSupported : of_value.

  Lemma of_value_with_BlobGasPriceGreaterThanMax :
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::BlobGasPriceGreaterThanMax" [] =
    φ BlobGasPriceGreaterThanMax.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_BlobGasPriceGreaterThanMax : of_value.

  Lemma of_value_with_EmptyBlobs :
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::EmptyBlobs" [] =
    φ EmptyBlobs.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_EmptyBlobs : of_value.

  Lemma of_value_with_BlobCreateTransaction :
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::BlobCreateTransaction" [] =
    φ BlobCreateTransaction.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_BlobCreateTransaction : of_value.

  Lemma of_value_with_TooManyBlobs
    (max : Usize.t) (max' : Value.t)
    (have : Usize.t) (have' : Value.t) :
    max' = φ max ->
    have' = φ have ->
    Value.StructRecord "revm_context_interface::result::InvalidTransaction::TooManyBlobs" [
      ("max", max');
      ("have", have')
    ] =
    φ (TooManyBlobs max have).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_TooManyBlobs : of_value.

  Lemma of_value_with_BlobVersionNotSupported :
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::BlobVersionNotSupported" [] =
    φ BlobVersionNotSupported.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_BlobVersionNotSupported : of_value.

  Lemma of_value_with_EofCrateShouldHaveToAddress :
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::EofCrateShouldHaveToAddress" [] =
    φ EofCrateShouldHaveToAddress.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_EofCrateShouldHaveToAddress : of_value.

  Lemma of_value_with_AuthorizationListNotSupported :
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::AuthorizationListNotSupported" [] =
    φ AuthorizationListNotSupported.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_AuthorizationListNotSupported : of_value.

  Lemma of_value_with_AuthorizationListInvalidFields :
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::AuthorizationListInvalidFields" [] =
    φ AuthorizationListInvalidFields.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_AuthorizationListInvalidFields : of_value.

  Lemma of_value_with_EmptyAuthorizationList :
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::EmptyAuthorizationList" [] =
    φ EmptyAuthorizationList.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_EmptyAuthorizationList : of_value.

  Lemma of_value_with_InvalidAuthorizationList
    (γ0 : revm_specification.eip7702.links.authorization_list.InvalidAuthorization.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::InvalidAuthorizationList" [
      γ0
    ] =
    φ (InvalidAuthorizationList γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InvalidAuthorizationList : of_value.

  Lemma of_value_with_Eip2930NotSupported :
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::Eip2930NotSupported" [] =
    φ Eip2930NotSupported.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Eip2930NotSupported : of_value.

  Lemma of_value_with_Eip1559NotSupported :
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::Eip1559NotSupported" [] =
    φ Eip1559NotSupported.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Eip1559NotSupported : of_value.

  Lemma of_value_with_Eip4844NotSupported :
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::Eip4844NotSupported" [] =
    φ Eip4844NotSupported.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Eip4844NotSupported : of_value.

  Lemma of_value_with_Eip7702NotSupported :
    Value.StructTuple "revm_context_interface::result::InvalidTransaction::Eip7702NotSupported" [] =
    φ Eip7702NotSupported.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Eip7702NotSupported : of_value.

  Definition of_value_PriorityFeeGreaterThanMaxFee :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::PriorityFeeGreaterThanMaxFee" []
    ).
  Proof. econstructor; apply of_value_with_PriorityFeeGreaterThanMaxFee; eassumption. Defined.
  Smpl Add simple apply of_value_PriorityFeeGreaterThanMaxFee : of_value.

  Definition of_value_GasPriceLessThanBasefee :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::GasPriceLessThanBasefee" []
    ).
  Proof. econstructor; apply of_value_with_GasPriceLessThanBasefee; eassumption. Defined.
  Smpl Add simple apply of_value_GasPriceLessThanBasefee : of_value.

  Definition of_value_CallerGasLimitMoreThanBlock :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::CallerGasLimitMoreThanBlock" []
    ).
  Proof. econstructor; apply of_value_with_CallerGasLimitMoreThanBlock; eassumption. Defined.
  Smpl Add simple apply of_value_CallerGasLimitMoreThanBlock : of_value.

  Definition of_value_CallGasCostMoreThanGasLimit :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::CallGasCostMoreThanGasLimit" []
    ).
  Proof. econstructor; apply of_value_with_CallGasCostMoreThanGasLimit; eassumption. Defined.
  Smpl Add simple apply of_value_CallGasCostMoreThanGasLimit : of_value.

  Definition of_value_RejectCallerWithCode :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::RejectCallerWithCode" []
    ).
  Proof. econstructor; apply of_value_with_RejectCallerWithCode; eassumption. Defined.
  Smpl Add simple apply of_value_RejectCallerWithCode : of_value.

  Definition of_value_LackOfFundForMaxFee
    (fee : alloc.links.boxed.Box.t (ruint.Uint.t 256 4) alloc.links.alloc.Global.t) (fee' : Value.t)
    (balance : alloc.links.boxed.Box.t (ruint.Uint.t 256 4) alloc.links.alloc.Global.t) (balance' : Value.t) :
    fee' = φ fee ->
    balance' = φ balance ->
    OfValue.t (
      Value.StructRecord "revm_context_interface::result::InvalidTransaction::LackOfFundForMaxFee" [
        ("fee", fee');
        ("balance", balance')
      ]
    ).
  Proof. econstructor; apply of_value_with_LackOfFundForMaxFee; eassumption. Defined.
  Smpl Add simple apply of_value_LackOfFundForMaxFee : of_value.

  Definition of_value_OverflowPaymentInTransaction :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::OverflowPaymentInTransaction" []
    ).
  Proof. econstructor; apply of_value_with_OverflowPaymentInTransaction; eassumption. Defined.
  Smpl Add simple apply of_value_OverflowPaymentInTransaction : of_value.

  Definition of_value_NonceOverflowInTransaction :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::NonceOverflowInTransaction" []
    ).
  Proof. econstructor; apply of_value_with_NonceOverflowInTransaction; eassumption. Defined.
  Smpl Add simple apply of_value_NonceOverflowInTransaction : of_value.

  Definition of_value_NonceTooHigh
    (tx : U64.t) (tx' : Value.t)
    (state : U64.t) (state' : Value.t) :
    tx' = φ tx ->
    state' = φ state ->
    OfValue.t (
      Value.StructRecord "revm_context_interface::result::InvalidTransaction::NonceTooHigh" [
        ("tx", tx');
        ("state", state')
      ]
    ).
  Proof. econstructor; apply of_value_with_NonceTooHigh; eassumption. Defined.
  Smpl Add simple apply of_value_NonceTooHigh : of_value.

  Definition of_value_NonceTooLow
    (tx : U64.t) (tx' : Value.t)
    (state : U64.t) (state' : Value.t) :
    tx' = φ tx ->
    state' = φ state ->
    OfValue.t (
      Value.StructRecord "revm_context_interface::result::InvalidTransaction::NonceTooLow" [
        ("tx", tx');
        ("state", state')
      ]
    ).
  Proof. econstructor; apply of_value_with_NonceTooLow; eassumption. Defined.
  Smpl Add simple apply of_value_NonceTooLow : of_value.

  Definition of_value_CreateInitCodeSizeLimit :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::CreateInitCodeSizeLimit" []
    ).
  Proof. econstructor; apply of_value_with_CreateInitCodeSizeLimit; eassumption. Defined.
  Smpl Add simple apply of_value_CreateInitCodeSizeLimit : of_value.

  Definition of_value_InvalidChainId :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::InvalidChainId" []
    ).
  Proof. econstructor; apply of_value_with_InvalidChainId; eassumption. Defined.
  Smpl Add simple apply of_value_InvalidChainId : of_value.

  Definition of_value_AccessListNotSupported :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::AccessListNotSupported" []
    ).
  Proof. econstructor; apply of_value_with_AccessListNotSupported; eassumption. Defined.
  Smpl Add simple apply of_value_AccessListNotSupported : of_value.

  Definition of_value_MaxFeePerBlobGasNotSupported :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::MaxFeePerBlobGasNotSupported" []
    ).
  Proof. econstructor; apply of_value_with_MaxFeePerBlobGasNotSupported; eassumption. Defined.
  Smpl Add simple apply of_value_MaxFeePerBlobGasNotSupported : of_value.

  Definition of_value_BlobVersionedHashesNotSupported :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::BlobVersionedHashesNotSupported" []
    ).
  Proof. econstructor; apply of_value_with_BlobVersionedHashesNotSupported; eassumption. Defined.
  Smpl Add simple apply of_value_BlobVersionedHashesNotSupported : of_value.

  Definition of_value_BlobGasPriceGreaterThanMax :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::BlobGasPriceGreaterThanMax" []
    ).
  Proof. econstructor; apply of_value_with_BlobGasPriceGreaterThanMax; eassumption. Defined.
  Smpl Add simple apply of_value_BlobGasPriceGreaterThanMax : of_value.

  Definition of_value_EmptyBlobs :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::EmptyBlobs" []
    ).
  Proof. econstructor; apply of_value_with_EmptyBlobs; eassumption. Defined.
  Smpl Add simple apply of_value_EmptyBlobs : of_value.

  Definition of_value_BlobCreateTransaction :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::BlobCreateTransaction" []
    ).
  Proof. econstructor; apply of_value_with_BlobCreateTransaction; eassumption. Defined.
  Smpl Add simple apply of_value_BlobCreateTransaction : of_value.

  Definition of_value_TooManyBlobs
    (max : Usize.t) (max' : Value.t)
    (have : Usize.t) (have' : Value.t) :
    max' = φ max ->
    have' = φ have ->
    OfValue.t (
      Value.StructRecord "revm_context_interface::result::InvalidTransaction::TooManyBlobs" [
        ("max", max');
        ("have", have')
      ]
    ).
  Proof. econstructor; apply of_value_with_TooManyBlobs; eassumption. Defined.
  Smpl Add simple apply of_value_TooManyBlobs : of_value.

  Definition of_value_BlobVersionNotSupported :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::BlobVersionNotSupported" []
    ).
  Proof. econstructor; apply of_value_with_BlobVersionNotSupported; eassumption. Defined.
  Smpl Add simple apply of_value_BlobVersionNotSupported : of_value.

  Definition of_value_EofCrateShouldHaveToAddress :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::EofCrateShouldHaveToAddress" []
    ).
  Proof. econstructor; apply of_value_with_EofCrateShouldHaveToAddress; eassumption. Defined.
  Smpl Add simple apply of_value_EofCrateShouldHaveToAddress : of_value.

  Definition of_value_AuthorizationListNotSupported :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::AuthorizationListNotSupported" []
    ).
  Proof. econstructor; apply of_value_with_AuthorizationListNotSupported; eassumption. Defined.
  Smpl Add simple apply of_value_AuthorizationListNotSupported : of_value.

  Definition of_value_AuthorizationListInvalidFields :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::AuthorizationListInvalidFields" []
    ).
  Proof. econstructor; apply of_value_with_AuthorizationListInvalidFields; eassumption. Defined.
  Smpl Add simple apply of_value_AuthorizationListInvalidFields : of_value.

  Definition of_value_EmptyAuthorizationList :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::EmptyAuthorizationList" []
    ).
  Proof. econstructor; apply of_value_with_EmptyAuthorizationList; eassumption. Defined.
  Smpl Add simple apply of_value_EmptyAuthorizationList : of_value.

  Definition of_value_InvalidAuthorizationList
    (γ0 : revm_specification.eip7702.links.authorization_list.InvalidAuthorization.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::InvalidAuthorizationList" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_InvalidAuthorizationList; eassumption. Defined.
  Smpl Add simple apply of_value_InvalidAuthorizationList : of_value.

  Definition of_value_Eip2930NotSupported :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::Eip2930NotSupported" []
    ).
  Proof. econstructor; apply of_value_with_Eip2930NotSupported; eassumption. Defined.
  Smpl Add simple apply of_value_Eip2930NotSupported : of_value.

  Definition of_value_Eip1559NotSupported :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::Eip1559NotSupported" []
    ).
  Proof. econstructor; apply of_value_with_Eip1559NotSupported; eassumption. Defined.
  Smpl Add simple apply of_value_Eip1559NotSupported : of_value.

  Definition of_value_Eip4844NotSupported :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::Eip4844NotSupported" []
    ).
  Proof. econstructor; apply of_value_with_Eip4844NotSupported; eassumption. Defined.
  Smpl Add simple apply of_value_Eip4844NotSupported : of_value.

  Definition of_value_Eip7702NotSupported :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidTransaction::Eip7702NotSupported" []
    ).
  Proof. econstructor; apply of_value_with_Eip7702NotSupported; eassumption. Defined.
  Smpl Add simple apply of_value_Eip7702NotSupported : of_value.
End InvalidTransaction.

Module InvalidHeader.
  Inductive t : Set :=
  | PrevrandaoNotSet
  | ExcessBlobGasNotSet
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_context_interface::result::InvalidHeader";
    φ x :=
      match x with
      | PrevrandaoNotSet =>
        Value.StructTuple "revm_context_interface::result::InvalidHeader::PrevrandaoNotSet" []
      | ExcessBlobGasNotSet =>
        Value.StructTuple "revm_context_interface::result::InvalidHeader::ExcessBlobGasNotSet" []
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_context_interface::result::InvalidHeader").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_PrevrandaoNotSet :
    Value.StructTuple "revm_context_interface::result::InvalidHeader::PrevrandaoNotSet" [] =
    φ PrevrandaoNotSet.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_PrevrandaoNotSet : of_value.

  Lemma of_value_with_ExcessBlobGasNotSet :
    Value.StructTuple "revm_context_interface::result::InvalidHeader::ExcessBlobGasNotSet" [] =
    φ ExcessBlobGasNotSet.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_ExcessBlobGasNotSet : of_value.

  Definition of_value_PrevrandaoNotSet :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidHeader::PrevrandaoNotSet" []
    ).
  Proof. econstructor; apply of_value_with_PrevrandaoNotSet; eassumption. Defined.
  Smpl Add simple apply of_value_PrevrandaoNotSet : of_value.

  Definition of_value_ExcessBlobGasNotSet :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::InvalidHeader::ExcessBlobGasNotSet" []
    ).
  Proof. econstructor; apply of_value_with_ExcessBlobGasNotSet; eassumption. Defined.
  Smpl Add simple apply of_value_ExcessBlobGasNotSet : of_value.
End InvalidHeader.

Module SuccessReason.
  Inductive t : Set :=
  | Stop
  | Return
  | SelfDestruct
  | EofReturnContract
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_context_interface::result::SuccessReason";
    φ x :=
      match x with
      | Stop =>
        Value.StructTuple "revm_context_interface::result::SuccessReason::Stop" []
      | Return =>
        Value.StructTuple "revm_context_interface::result::SuccessReason::Return" []
      | SelfDestruct =>
        Value.StructTuple "revm_context_interface::result::SuccessReason::SelfDestruct" []
      | EofReturnContract =>
        Value.StructTuple "revm_context_interface::result::SuccessReason::EofReturnContract" []
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_context_interface::result::SuccessReason").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_Stop :
    Value.StructTuple "revm_context_interface::result::SuccessReason::Stop" [] =
    φ Stop.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Stop : of_value.

  Lemma of_value_with_Return :
    Value.StructTuple "revm_context_interface::result::SuccessReason::Return" [] =
    φ Return.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Return : of_value.

  Lemma of_value_with_SelfDestruct :
    Value.StructTuple "revm_context_interface::result::SuccessReason::SelfDestruct" [] =
    φ SelfDestruct.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_SelfDestruct : of_value.

  Lemma of_value_with_EofReturnContract :
    Value.StructTuple "revm_context_interface::result::SuccessReason::EofReturnContract" [] =
    φ EofReturnContract.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_EofReturnContract : of_value.

  Definition of_value_Stop :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::SuccessReason::Stop" []
    ).
  Proof. econstructor; apply of_value_with_Stop; eassumption. Defined.
  Smpl Add simple apply of_value_Stop : of_value.

  Definition of_value_Return :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::SuccessReason::Return" []
    ).
  Proof. econstructor; apply of_value_with_Return; eassumption. Defined.
  Smpl Add simple apply of_value_Return : of_value.

  Definition of_value_SelfDestruct :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::SuccessReason::SelfDestruct" []
    ).
  Proof. econstructor; apply of_value_with_SelfDestruct; eassumption. Defined.
  Smpl Add simple apply of_value_SelfDestruct : of_value.

  Definition of_value_EofReturnContract :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::SuccessReason::EofReturnContract" []
    ).
  Proof. econstructor; apply of_value_with_EofReturnContract; eassumption. Defined.
  Smpl Add simple apply of_value_EofReturnContract : of_value.
End SuccessReason.

Module HaltReason.
  Inductive t : Set :=
  | OutOfGas
    (_ : revm_context_interface.links.result.OutOfGasError.t)
  | OpcodeNotFound
  | InvalidFEOpcode
  | InvalidJump
  | NotActivated
  | StackUnderflow
  | StackOverflow
  | OutOfOffset
  | CreateCollision
  | PrecompileError
  | NonceOverflow
  | CreateContractSizeLimit
  | CreateContractStartingWithEF
  | CreateInitCodeSizeLimit
  | OverflowPayment
  | StateChangeDuringStaticCall
  | CallNotAllowedInsideStatic
  | OutOfFunds
  | CallTooDeep
  | EofAuxDataOverflow
  | EofAuxDataTooSmall
  | SubRoutineStackOverflow
  | InvalidEXTCALLTarget
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_context_interface::result::HaltReason";
    φ x :=
      match x with
      | OutOfGas γ0 =>
        Value.StructTuple "revm_context_interface::result::HaltReason::OutOfGas" [
          φ γ0
        ]
      | OpcodeNotFound =>
        Value.StructTuple "revm_context_interface::result::HaltReason::OpcodeNotFound" []
      | InvalidFEOpcode =>
        Value.StructTuple "revm_context_interface::result::HaltReason::InvalidFEOpcode" []
      | InvalidJump =>
        Value.StructTuple "revm_context_interface::result::HaltReason::InvalidJump" []
      | NotActivated =>
        Value.StructTuple "revm_context_interface::result::HaltReason::NotActivated" []
      | StackUnderflow =>
        Value.StructTuple "revm_context_interface::result::HaltReason::StackUnderflow" []
      | StackOverflow =>
        Value.StructTuple "revm_context_interface::result::HaltReason::StackOverflow" []
      | OutOfOffset =>
        Value.StructTuple "revm_context_interface::result::HaltReason::OutOfOffset" []
      | CreateCollision =>
        Value.StructTuple "revm_context_interface::result::HaltReason::CreateCollision" []
      | PrecompileError =>
        Value.StructTuple "revm_context_interface::result::HaltReason::PrecompileError" []
      | NonceOverflow =>
        Value.StructTuple "revm_context_interface::result::HaltReason::NonceOverflow" []
      | CreateContractSizeLimit =>
        Value.StructTuple "revm_context_interface::result::HaltReason::CreateContractSizeLimit" []
      | CreateContractStartingWithEF =>
        Value.StructTuple "revm_context_interface::result::HaltReason::CreateContractStartingWithEF" []
      | CreateInitCodeSizeLimit =>
        Value.StructTuple "revm_context_interface::result::HaltReason::CreateInitCodeSizeLimit" []
      | OverflowPayment =>
        Value.StructTuple "revm_context_interface::result::HaltReason::OverflowPayment" []
      | StateChangeDuringStaticCall =>
        Value.StructTuple "revm_context_interface::result::HaltReason::StateChangeDuringStaticCall" []
      | CallNotAllowedInsideStatic =>
        Value.StructTuple "revm_context_interface::result::HaltReason::CallNotAllowedInsideStatic" []
      | OutOfFunds =>
        Value.StructTuple "revm_context_interface::result::HaltReason::OutOfFunds" []
      | CallTooDeep =>
        Value.StructTuple "revm_context_interface::result::HaltReason::CallTooDeep" []
      | EofAuxDataOverflow =>
        Value.StructTuple "revm_context_interface::result::HaltReason::EofAuxDataOverflow" []
      | EofAuxDataTooSmall =>
        Value.StructTuple "revm_context_interface::result::HaltReason::EofAuxDataTooSmall" []
      | SubRoutineStackOverflow =>
        Value.StructTuple "revm_context_interface::result::HaltReason::SubRoutineStackOverflow" []
      | InvalidEXTCALLTarget =>
        Value.StructTuple "revm_context_interface::result::HaltReason::InvalidEXTCALLTarget" []
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_context_interface::result::HaltReason").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_OutOfGas
    (γ0 : revm_context_interface.links.result.OutOfGasError.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_context_interface::result::HaltReason::OutOfGas" [
      γ0
    ] =
    φ (OutOfGas γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_OutOfGas : of_value.

  Lemma of_value_with_OpcodeNotFound :
    Value.StructTuple "revm_context_interface::result::HaltReason::OpcodeNotFound" [] =
    φ OpcodeNotFound.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_OpcodeNotFound : of_value.

  Lemma of_value_with_InvalidFEOpcode :
    Value.StructTuple "revm_context_interface::result::HaltReason::InvalidFEOpcode" [] =
    φ InvalidFEOpcode.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InvalidFEOpcode : of_value.

  Lemma of_value_with_InvalidJump :
    Value.StructTuple "revm_context_interface::result::HaltReason::InvalidJump" [] =
    φ InvalidJump.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InvalidJump : of_value.

  Lemma of_value_with_NotActivated :
    Value.StructTuple "revm_context_interface::result::HaltReason::NotActivated" [] =
    φ NotActivated.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_NotActivated : of_value.

  Lemma of_value_with_StackUnderflow :
    Value.StructTuple "revm_context_interface::result::HaltReason::StackUnderflow" [] =
    φ StackUnderflow.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_StackUnderflow : of_value.

  Lemma of_value_with_StackOverflow :
    Value.StructTuple "revm_context_interface::result::HaltReason::StackOverflow" [] =
    φ StackOverflow.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_StackOverflow : of_value.

  Lemma of_value_with_OutOfOffset :
    Value.StructTuple "revm_context_interface::result::HaltReason::OutOfOffset" [] =
    φ OutOfOffset.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_OutOfOffset : of_value.

  Lemma of_value_with_CreateCollision :
    Value.StructTuple "revm_context_interface::result::HaltReason::CreateCollision" [] =
    φ CreateCollision.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CreateCollision : of_value.

  Lemma of_value_with_PrecompileError :
    Value.StructTuple "revm_context_interface::result::HaltReason::PrecompileError" [] =
    φ PrecompileError.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_PrecompileError : of_value.

  Lemma of_value_with_NonceOverflow :
    Value.StructTuple "revm_context_interface::result::HaltReason::NonceOverflow" [] =
    φ NonceOverflow.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_NonceOverflow : of_value.

  Lemma of_value_with_CreateContractSizeLimit :
    Value.StructTuple "revm_context_interface::result::HaltReason::CreateContractSizeLimit" [] =
    φ CreateContractSizeLimit.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CreateContractSizeLimit : of_value.

  Lemma of_value_with_CreateContractStartingWithEF :
    Value.StructTuple "revm_context_interface::result::HaltReason::CreateContractStartingWithEF" [] =
    φ CreateContractStartingWithEF.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CreateContractStartingWithEF : of_value.

  Lemma of_value_with_CreateInitCodeSizeLimit :
    Value.StructTuple "revm_context_interface::result::HaltReason::CreateInitCodeSizeLimit" [] =
    φ CreateInitCodeSizeLimit.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CreateInitCodeSizeLimit : of_value.

  Lemma of_value_with_OverflowPayment :
    Value.StructTuple "revm_context_interface::result::HaltReason::OverflowPayment" [] =
    φ OverflowPayment.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_OverflowPayment : of_value.

  Lemma of_value_with_StateChangeDuringStaticCall :
    Value.StructTuple "revm_context_interface::result::HaltReason::StateChangeDuringStaticCall" [] =
    φ StateChangeDuringStaticCall.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_StateChangeDuringStaticCall : of_value.

  Lemma of_value_with_CallNotAllowedInsideStatic :
    Value.StructTuple "revm_context_interface::result::HaltReason::CallNotAllowedInsideStatic" [] =
    φ CallNotAllowedInsideStatic.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CallNotAllowedInsideStatic : of_value.

  Lemma of_value_with_OutOfFunds :
    Value.StructTuple "revm_context_interface::result::HaltReason::OutOfFunds" [] =
    φ OutOfFunds.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_OutOfFunds : of_value.

  Lemma of_value_with_CallTooDeep :
    Value.StructTuple "revm_context_interface::result::HaltReason::CallTooDeep" [] =
    φ CallTooDeep.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CallTooDeep : of_value.

  Lemma of_value_with_EofAuxDataOverflow :
    Value.StructTuple "revm_context_interface::result::HaltReason::EofAuxDataOverflow" [] =
    φ EofAuxDataOverflow.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_EofAuxDataOverflow : of_value.

  Lemma of_value_with_EofAuxDataTooSmall :
    Value.StructTuple "revm_context_interface::result::HaltReason::EofAuxDataTooSmall" [] =
    φ EofAuxDataTooSmall.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_EofAuxDataTooSmall : of_value.

  Lemma of_value_with_SubRoutineStackOverflow :
    Value.StructTuple "revm_context_interface::result::HaltReason::SubRoutineStackOverflow" [] =
    φ SubRoutineStackOverflow.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_SubRoutineStackOverflow : of_value.

  Lemma of_value_with_InvalidEXTCALLTarget :
    Value.StructTuple "revm_context_interface::result::HaltReason::InvalidEXTCALLTarget" [] =
    φ InvalidEXTCALLTarget.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InvalidEXTCALLTarget : of_value.

  Definition of_value_OutOfGas
    (γ0 : revm_context_interface.links.result.OutOfGasError.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::HaltReason::OutOfGas" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_OutOfGas; eassumption. Defined.
  Smpl Add simple apply of_value_OutOfGas : of_value.

  Definition of_value_OpcodeNotFound :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::HaltReason::OpcodeNotFound" []
    ).
  Proof. econstructor; apply of_value_with_OpcodeNotFound; eassumption. Defined.
  Smpl Add simple apply of_value_OpcodeNotFound : of_value.

  Definition of_value_InvalidFEOpcode :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::HaltReason::InvalidFEOpcode" []
    ).
  Proof. econstructor; apply of_value_with_InvalidFEOpcode; eassumption. Defined.
  Smpl Add simple apply of_value_InvalidFEOpcode : of_value.

  Definition of_value_InvalidJump :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::HaltReason::InvalidJump" []
    ).
  Proof. econstructor; apply of_value_with_InvalidJump; eassumption. Defined.
  Smpl Add simple apply of_value_InvalidJump : of_value.

  Definition of_value_NotActivated :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::HaltReason::NotActivated" []
    ).
  Proof. econstructor; apply of_value_with_NotActivated; eassumption. Defined.
  Smpl Add simple apply of_value_NotActivated : of_value.

  Definition of_value_StackUnderflow :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::HaltReason::StackUnderflow" []
    ).
  Proof. econstructor; apply of_value_with_StackUnderflow; eassumption. Defined.
  Smpl Add simple apply of_value_StackUnderflow : of_value.

  Definition of_value_StackOverflow :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::HaltReason::StackOverflow" []
    ).
  Proof. econstructor; apply of_value_with_StackOverflow; eassumption. Defined.
  Smpl Add simple apply of_value_StackOverflow : of_value.

  Definition of_value_OutOfOffset :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::HaltReason::OutOfOffset" []
    ).
  Proof. econstructor; apply of_value_with_OutOfOffset; eassumption. Defined.
  Smpl Add simple apply of_value_OutOfOffset : of_value.

  Definition of_value_CreateCollision :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::HaltReason::CreateCollision" []
    ).
  Proof. econstructor; apply of_value_with_CreateCollision; eassumption. Defined.
  Smpl Add simple apply of_value_CreateCollision : of_value.

  Definition of_value_PrecompileError :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::HaltReason::PrecompileError" []
    ).
  Proof. econstructor; apply of_value_with_PrecompileError; eassumption. Defined.
  Smpl Add simple apply of_value_PrecompileError : of_value.

  Definition of_value_NonceOverflow :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::HaltReason::NonceOverflow" []
    ).
  Proof. econstructor; apply of_value_with_NonceOverflow; eassumption. Defined.
  Smpl Add simple apply of_value_NonceOverflow : of_value.

  Definition of_value_CreateContractSizeLimit :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::HaltReason::CreateContractSizeLimit" []
    ).
  Proof. econstructor; apply of_value_with_CreateContractSizeLimit; eassumption. Defined.
  Smpl Add simple apply of_value_CreateContractSizeLimit : of_value.

  Definition of_value_CreateContractStartingWithEF :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::HaltReason::CreateContractStartingWithEF" []
    ).
  Proof. econstructor; apply of_value_with_CreateContractStartingWithEF; eassumption. Defined.
  Smpl Add simple apply of_value_CreateContractStartingWithEF : of_value.

  Definition of_value_CreateInitCodeSizeLimit :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::HaltReason::CreateInitCodeSizeLimit" []
    ).
  Proof. econstructor; apply of_value_with_CreateInitCodeSizeLimit; eassumption. Defined.
  Smpl Add simple apply of_value_CreateInitCodeSizeLimit : of_value.

  Definition of_value_OverflowPayment :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::HaltReason::OverflowPayment" []
    ).
  Proof. econstructor; apply of_value_with_OverflowPayment; eassumption. Defined.
  Smpl Add simple apply of_value_OverflowPayment : of_value.

  Definition of_value_StateChangeDuringStaticCall :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::HaltReason::StateChangeDuringStaticCall" []
    ).
  Proof. econstructor; apply of_value_with_StateChangeDuringStaticCall; eassumption. Defined.
  Smpl Add simple apply of_value_StateChangeDuringStaticCall : of_value.

  Definition of_value_CallNotAllowedInsideStatic :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::HaltReason::CallNotAllowedInsideStatic" []
    ).
  Proof. econstructor; apply of_value_with_CallNotAllowedInsideStatic; eassumption. Defined.
  Smpl Add simple apply of_value_CallNotAllowedInsideStatic : of_value.

  Definition of_value_OutOfFunds :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::HaltReason::OutOfFunds" []
    ).
  Proof. econstructor; apply of_value_with_OutOfFunds; eassumption. Defined.
  Smpl Add simple apply of_value_OutOfFunds : of_value.

  Definition of_value_CallTooDeep :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::HaltReason::CallTooDeep" []
    ).
  Proof. econstructor; apply of_value_with_CallTooDeep; eassumption. Defined.
  Smpl Add simple apply of_value_CallTooDeep : of_value.

  Definition of_value_EofAuxDataOverflow :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::HaltReason::EofAuxDataOverflow" []
    ).
  Proof. econstructor; apply of_value_with_EofAuxDataOverflow; eassumption. Defined.
  Smpl Add simple apply of_value_EofAuxDataOverflow : of_value.

  Definition of_value_EofAuxDataTooSmall :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::HaltReason::EofAuxDataTooSmall" []
    ).
  Proof. econstructor; apply of_value_with_EofAuxDataTooSmall; eassumption. Defined.
  Smpl Add simple apply of_value_EofAuxDataTooSmall : of_value.

  Definition of_value_SubRoutineStackOverflow :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::HaltReason::SubRoutineStackOverflow" []
    ).
  Proof. econstructor; apply of_value_with_SubRoutineStackOverflow; eassumption. Defined.
  Smpl Add simple apply of_value_SubRoutineStackOverflow : of_value.

  Definition of_value_InvalidEXTCALLTarget :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::HaltReason::InvalidEXTCALLTarget" []
    ).
  Proof. econstructor; apply of_value_with_InvalidEXTCALLTarget; eassumption. Defined.
  Smpl Add simple apply of_value_InvalidEXTCALLTarget : of_value.
End HaltReason.

Module OutOfGasError.
  Inductive t : Set :=
  | Basic
  | MemoryLimit
  | Memory
  | Precompile
  | InvalidOperand
  | ReentrancySentry
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_context_interface::result::OutOfGasError";
    φ x :=
      match x with
      | Basic =>
        Value.StructTuple "revm_context_interface::result::OutOfGasError::Basic" []
      | MemoryLimit =>
        Value.StructTuple "revm_context_interface::result::OutOfGasError::MemoryLimit" []
      | Memory =>
        Value.StructTuple "revm_context_interface::result::OutOfGasError::Memory" []
      | Precompile =>
        Value.StructTuple "revm_context_interface::result::OutOfGasError::Precompile" []
      | InvalidOperand =>
        Value.StructTuple "revm_context_interface::result::OutOfGasError::InvalidOperand" []
      | ReentrancySentry =>
        Value.StructTuple "revm_context_interface::result::OutOfGasError::ReentrancySentry" []
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_context_interface::result::OutOfGasError").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_Basic :
    Value.StructTuple "revm_context_interface::result::OutOfGasError::Basic" [] =
    φ Basic.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Basic : of_value.

  Lemma of_value_with_MemoryLimit :
    Value.StructTuple "revm_context_interface::result::OutOfGasError::MemoryLimit" [] =
    φ MemoryLimit.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_MemoryLimit : of_value.

  Lemma of_value_with_Memory :
    Value.StructTuple "revm_context_interface::result::OutOfGasError::Memory" [] =
    φ Memory.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Memory : of_value.

  Lemma of_value_with_Precompile :
    Value.StructTuple "revm_context_interface::result::OutOfGasError::Precompile" [] =
    φ Precompile.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Precompile : of_value.

  Lemma of_value_with_InvalidOperand :
    Value.StructTuple "revm_context_interface::result::OutOfGasError::InvalidOperand" [] =
    φ InvalidOperand.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InvalidOperand : of_value.

  Lemma of_value_with_ReentrancySentry :
    Value.StructTuple "revm_context_interface::result::OutOfGasError::ReentrancySentry" [] =
    φ ReentrancySentry.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_ReentrancySentry : of_value.

  Definition of_value_Basic :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::OutOfGasError::Basic" []
    ).
  Proof. econstructor; apply of_value_with_Basic; eassumption. Defined.
  Smpl Add simple apply of_value_Basic : of_value.

  Definition of_value_MemoryLimit :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::OutOfGasError::MemoryLimit" []
    ).
  Proof. econstructor; apply of_value_with_MemoryLimit; eassumption. Defined.
  Smpl Add simple apply of_value_MemoryLimit : of_value.

  Definition of_value_Memory :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::OutOfGasError::Memory" []
    ).
  Proof. econstructor; apply of_value_with_Memory; eassumption. Defined.
  Smpl Add simple apply of_value_Memory : of_value.

  Definition of_value_Precompile :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::OutOfGasError::Precompile" []
    ).
  Proof. econstructor; apply of_value_with_Precompile; eassumption. Defined.
  Smpl Add simple apply of_value_Precompile : of_value.

  Definition of_value_InvalidOperand :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::OutOfGasError::InvalidOperand" []
    ).
  Proof. econstructor; apply of_value_with_InvalidOperand; eassumption. Defined.
  Smpl Add simple apply of_value_InvalidOperand : of_value.

  Definition of_value_ReentrancySentry :
    OfValue.t (
      Value.StructTuple "revm_context_interface::result::OutOfGasError::ReentrancySentry" []
    ).
  Proof. econstructor; apply of_value_with_ReentrancySentry; eassumption. Defined.
  Smpl Add simple apply of_value_ReentrancySentry : of_value.
End OutOfGasError.

Module BlobExcessGasAndPrice.
  Record t : Set := {
    excess_blob_gas: U64.t;
    blob_gasprice: U128.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_context_interface::block::blob::BlobExcessGasAndPrice";
    φ '(Build_t excess_blob_gas blob_gasprice) :=
      Value.StructRecord "revm_context_interface::block::blob::BlobExcessGasAndPrice" [
        ("excess_blob_gas", φ excess_blob_gas);
        ("blob_gasprice", φ blob_gasprice)
      ]
  }.
End BlobExcessGasAndPrice.

Module DummyHost.
  Record t {BLOCK TX CFG: Set} : Set := {
    tx: TX;
    block: BLOCK;
    cfg: CFG;
    storage: hashbrown.links.map.HashMap.t (ruint.Uint.t 256 4) (ruint.Uint.t 256 4) foldhash.seed.links.fast.RandomState.t hashbrown.raw.alloc.links.inner.Global.t;
    transient_storage: hashbrown.links.map.HashMap.t (ruint.Uint.t 256 4) (ruint.Uint.t 256 4) foldhash.seed.links.fast.RandomState.t hashbrown.raw.alloc.links.inner.Global.t;
    log: alloc.links.vec.Vec.t (alloy_primitives.links.log.Log.t alloy_primitives.links.log.LogData.t) alloc.links.alloc.Global.t;
  }.
  Arguments Build_t {_ _ _}.
  Arguments t : clear implicits.

  Global Instance IsLink {BLOCK TX CFG: Set} `{Link BLOCK} `{Link TX} `{Link CFG} : Link (t BLOCK TX CFG) := {
    Φ := Ty.path "revm_context_interface::host::dummy::DummyHost";
    φ '(Build_t tx block cfg storage transient_storage log) :=
      Value.StructRecord "revm_context_interface::host::dummy::DummyHost" [
        ("tx", φ tx);
        ("block", φ block);
        ("cfg", φ cfg);
        ("storage", φ storage);
        ("transient_storage", φ transient_storage);
        ("log", φ log)
      ]
  }.
End DummyHost.

Module TransactionType.
  Inductive t : Set :=
  | Legacy
  | Eip2930
  | Eip1559
  | Eip4844
  | Eip7702
  | Custom
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_context_interface::transaction::transaction_type::TransactionType";
    φ x :=
      match x with
      | Legacy =>
        Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Legacy" []
      | Eip2930 =>
        Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip2930" []
      | Eip1559 =>
        Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip1559" []
      | Eip4844 =>
        Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip4844" []
      | Eip7702 =>
        Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip7702" []
      | Custom =>
        Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Custom" []
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_context_interface::transaction::transaction_type::TransactionType").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_Legacy :
    Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Legacy" [] =
    φ Legacy.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Legacy : of_value.

  Lemma of_value_with_Eip2930 :
    Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip2930" [] =
    φ Eip2930.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Eip2930 : of_value.

  Lemma of_value_with_Eip1559 :
    Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip1559" [] =
    φ Eip1559.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Eip1559 : of_value.

  Lemma of_value_with_Eip4844 :
    Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip4844" [] =
    φ Eip4844.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Eip4844 : of_value.

  Lemma of_value_with_Eip7702 :
    Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip7702" [] =
    φ Eip7702.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Eip7702 : of_value.

  Lemma of_value_with_Custom :
    Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Custom" [] =
    φ Custom.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Custom : of_value.

  Definition of_value_Legacy :
    OfValue.t (
      Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Legacy" []
    ).
  Proof. econstructor; apply of_value_with_Legacy; eassumption. Defined.
  Smpl Add simple apply of_value_Legacy : of_value.

  Definition of_value_Eip2930 :
    OfValue.t (
      Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip2930" []
    ).
  Proof. econstructor; apply of_value_with_Eip2930; eassumption. Defined.
  Smpl Add simple apply of_value_Eip2930 : of_value.

  Definition of_value_Eip1559 :
    OfValue.t (
      Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip1559" []
    ).
  Proof. econstructor; apply of_value_with_Eip1559; eassumption. Defined.
  Smpl Add simple apply of_value_Eip1559 : of_value.

  Definition of_value_Eip4844 :
    OfValue.t (
      Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip4844" []
    ).
  Proof. econstructor; apply of_value_with_Eip4844; eassumption. Defined.
  Smpl Add simple apply of_value_Eip4844 : of_value.

  Definition of_value_Eip7702 :
    OfValue.t (
      Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip7702" []
    ).
  Proof. econstructor; apply of_value_with_Eip7702; eassumption. Defined.
  Smpl Add simple apply of_value_Eip7702 : of_value.

  Definition of_value_Custom :
    OfValue.t (
      Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Custom" []
    ).
  Proof. econstructor; apply of_value_with_Custom; eassumption. Defined.
  Smpl Add simple apply of_value_Custom : of_value.
End TransactionType.

Module Gas.
  Record t : Set := {
    limit: U64.t;
    remaining: U64.t;
    refunded: I64.t;
    memory: revm_interpreter.links.gas.MemoryGas.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::gas::Gas";
    φ '(Build_t limit remaining refunded memory) :=
      Value.StructRecord "revm_interpreter::gas::Gas" [
        ("limit", φ limit);
        ("remaining", φ remaining);
        ("refunded", φ refunded);
        ("memory", φ memory)
      ]
  }.
End Gas.

Module MemoryExtensionResult.
  Inductive t : Set :=
  | Extended
  | Same
  | OutOfGas
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::gas::MemoryExtensionResult";
    φ x :=
      match x with
      | Extended =>
        Value.StructTuple "revm_interpreter::gas::MemoryExtensionResult::Extended" []
      | Same =>
        Value.StructTuple "revm_interpreter::gas::MemoryExtensionResult::Same" []
      | OutOfGas =>
        Value.StructTuple "revm_interpreter::gas::MemoryExtensionResult::OutOfGas" []
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_interpreter::gas::MemoryExtensionResult").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_Extended :
    Value.StructTuple "revm_interpreter::gas::MemoryExtensionResult::Extended" [] =
    φ Extended.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Extended : of_value.

  Lemma of_value_with_Same :
    Value.StructTuple "revm_interpreter::gas::MemoryExtensionResult::Same" [] =
    φ Same.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Same : of_value.

  Lemma of_value_with_OutOfGas :
    Value.StructTuple "revm_interpreter::gas::MemoryExtensionResult::OutOfGas" [] =
    φ OutOfGas.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_OutOfGas : of_value.

  Definition of_value_Extended :
    OfValue.t (
      Value.StructTuple "revm_interpreter::gas::MemoryExtensionResult::Extended" []
    ).
  Proof. econstructor; apply of_value_with_Extended; eassumption. Defined.
  Smpl Add simple apply of_value_Extended : of_value.

  Definition of_value_Same :
    OfValue.t (
      Value.StructTuple "revm_interpreter::gas::MemoryExtensionResult::Same" []
    ).
  Proof. econstructor; apply of_value_with_Same; eassumption. Defined.
  Smpl Add simple apply of_value_Same : of_value.

  Definition of_value_OutOfGas :
    OfValue.t (
      Value.StructTuple "revm_interpreter::gas::MemoryExtensionResult::OutOfGas" []
    ).
  Proof. econstructor; apply of_value_with_OutOfGas; eassumption. Defined.
  Smpl Add simple apply of_value_OutOfGas : of_value.
End MemoryExtensionResult.

Module MemoryGas.
  Record t : Set := {
    words_num: Usize.t;
    expansion_cost: U64.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::gas::MemoryGas";
    φ '(Build_t words_num expansion_cost) :=
      Value.StructRecord "revm_interpreter::gas::MemoryGas" [
        ("words_num", φ words_num);
        ("expansion_cost", φ expansion_cost)
      ]
  }.
End MemoryGas.

Module InstructionResult.
  Inductive t : Set :=
  | Continue
  | Stop
  | Return
  | SelfDestruct
  | ReturnContract
  | Revert
  | CallTooDeep
  | OutOfFunds
  | CreateInitCodeStartingEF00
  | InvalidEOFInitCode
  | InvalidExtDelegateCallTarget
  | CallOrCreate
  | OutOfGas
  | MemoryOOG
  | MemoryLimitOOG
  | PrecompileOOG
  | InvalidOperandOOG
  | ReentrancySentryOOG
  | OpcodeNotFound
  | CallNotAllowedInsideStatic
  | StateChangeDuringStaticCall
  | InvalidFEOpcode
  | InvalidJump
  | NotActivated
  | StackUnderflow
  | StackOverflow
  | OutOfOffset
  | CreateCollision
  | OverflowPayment
  | PrecompileError
  | NonceOverflow
  | CreateContractSizeLimit
  | CreateContractStartingWithEF
  | CreateInitCodeSizeLimit
  | FatalExternalError
  | ReturnContractInNotInitEOF
  | EOFOpcodeDisabledInLegacy
  | SubRoutineStackOverflow
  | EofAuxDataOverflow
  | EofAuxDataTooSmall
  | InvalidEXTCALLTarget
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::instruction_result::InstructionResult";
    φ x :=
      match x with
      | Continue =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::Continue" []
      | Stop =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::Stop" []
      | Return =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::Return" []
      | SelfDestruct =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::SelfDestruct" []
      | ReturnContract =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::ReturnContract" []
      | Revert =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::Revert" []
      | CallTooDeep =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CallTooDeep" []
      | OutOfFunds =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OutOfFunds" []
      | CreateInitCodeStartingEF00 =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateInitCodeStartingEF00" []
      | InvalidEOFInitCode =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidEOFInitCode" []
      | InvalidExtDelegateCallTarget =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidExtDelegateCallTarget" []
      | CallOrCreate =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CallOrCreate" []
      | OutOfGas =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OutOfGas" []
      | MemoryOOG =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::MemoryOOG" []
      | MemoryLimitOOG =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::MemoryLimitOOG" []
      | PrecompileOOG =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::PrecompileOOG" []
      | InvalidOperandOOG =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidOperandOOG" []
      | ReentrancySentryOOG =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::ReentrancySentryOOG" []
      | OpcodeNotFound =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OpcodeNotFound" []
      | CallNotAllowedInsideStatic =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CallNotAllowedInsideStatic" []
      | StateChangeDuringStaticCall =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::StateChangeDuringStaticCall" []
      | InvalidFEOpcode =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidFEOpcode" []
      | InvalidJump =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidJump" []
      | NotActivated =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::NotActivated" []
      | StackUnderflow =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::StackUnderflow" []
      | StackOverflow =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::StackOverflow" []
      | OutOfOffset =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OutOfOffset" []
      | CreateCollision =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateCollision" []
      | OverflowPayment =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OverflowPayment" []
      | PrecompileError =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::PrecompileError" []
      | NonceOverflow =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::NonceOverflow" []
      | CreateContractSizeLimit =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateContractSizeLimit" []
      | CreateContractStartingWithEF =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateContractStartingWithEF" []
      | CreateInitCodeSizeLimit =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateInitCodeSizeLimit" []
      | FatalExternalError =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::FatalExternalError" []
      | ReturnContractInNotInitEOF =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::ReturnContractInNotInitEOF" []
      | EOFOpcodeDisabledInLegacy =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::EOFOpcodeDisabledInLegacy" []
      | SubRoutineStackOverflow =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::SubRoutineStackOverflow" []
      | EofAuxDataOverflow =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::EofAuxDataOverflow" []
      | EofAuxDataTooSmall =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::EofAuxDataTooSmall" []
      | InvalidEXTCALLTarget =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidEXTCALLTarget" []
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_interpreter::instruction_result::InstructionResult").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_Continue :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::Continue" [] =
    φ Continue.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Continue : of_value.

  Lemma of_value_with_Stop :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::Stop" [] =
    φ Stop.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Stop : of_value.

  Lemma of_value_with_Return :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::Return" [] =
    φ Return.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Return : of_value.

  Lemma of_value_with_SelfDestruct :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::SelfDestruct" [] =
    φ SelfDestruct.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_SelfDestruct : of_value.

  Lemma of_value_with_ReturnContract :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::ReturnContract" [] =
    φ ReturnContract.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_ReturnContract : of_value.

  Lemma of_value_with_Revert :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::Revert" [] =
    φ Revert.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Revert : of_value.

  Lemma of_value_with_CallTooDeep :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CallTooDeep" [] =
    φ CallTooDeep.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CallTooDeep : of_value.

  Lemma of_value_with_OutOfFunds :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OutOfFunds" [] =
    φ OutOfFunds.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_OutOfFunds : of_value.

  Lemma of_value_with_CreateInitCodeStartingEF00 :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateInitCodeStartingEF00" [] =
    φ CreateInitCodeStartingEF00.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CreateInitCodeStartingEF00 : of_value.

  Lemma of_value_with_InvalidEOFInitCode :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidEOFInitCode" [] =
    φ InvalidEOFInitCode.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InvalidEOFInitCode : of_value.

  Lemma of_value_with_InvalidExtDelegateCallTarget :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidExtDelegateCallTarget" [] =
    φ InvalidExtDelegateCallTarget.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InvalidExtDelegateCallTarget : of_value.

  Lemma of_value_with_CallOrCreate :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CallOrCreate" [] =
    φ CallOrCreate.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CallOrCreate : of_value.

  Lemma of_value_with_OutOfGas :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OutOfGas" [] =
    φ OutOfGas.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_OutOfGas : of_value.

  Lemma of_value_with_MemoryOOG :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::MemoryOOG" [] =
    φ MemoryOOG.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_MemoryOOG : of_value.

  Lemma of_value_with_MemoryLimitOOG :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::MemoryLimitOOG" [] =
    φ MemoryLimitOOG.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_MemoryLimitOOG : of_value.

  Lemma of_value_with_PrecompileOOG :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::PrecompileOOG" [] =
    φ PrecompileOOG.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_PrecompileOOG : of_value.

  Lemma of_value_with_InvalidOperandOOG :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidOperandOOG" [] =
    φ InvalidOperandOOG.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InvalidOperandOOG : of_value.

  Lemma of_value_with_ReentrancySentryOOG :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::ReentrancySentryOOG" [] =
    φ ReentrancySentryOOG.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_ReentrancySentryOOG : of_value.

  Lemma of_value_with_OpcodeNotFound :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OpcodeNotFound" [] =
    φ OpcodeNotFound.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_OpcodeNotFound : of_value.

  Lemma of_value_with_CallNotAllowedInsideStatic :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CallNotAllowedInsideStatic" [] =
    φ CallNotAllowedInsideStatic.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CallNotAllowedInsideStatic : of_value.

  Lemma of_value_with_StateChangeDuringStaticCall :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::StateChangeDuringStaticCall" [] =
    φ StateChangeDuringStaticCall.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_StateChangeDuringStaticCall : of_value.

  Lemma of_value_with_InvalidFEOpcode :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidFEOpcode" [] =
    φ InvalidFEOpcode.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InvalidFEOpcode : of_value.

  Lemma of_value_with_InvalidJump :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidJump" [] =
    φ InvalidJump.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InvalidJump : of_value.

  Lemma of_value_with_NotActivated :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::NotActivated" [] =
    φ NotActivated.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_NotActivated : of_value.

  Lemma of_value_with_StackUnderflow :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::StackUnderflow" [] =
    φ StackUnderflow.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_StackUnderflow : of_value.

  Lemma of_value_with_StackOverflow :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::StackOverflow" [] =
    φ StackOverflow.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_StackOverflow : of_value.

  Lemma of_value_with_OutOfOffset :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OutOfOffset" [] =
    φ OutOfOffset.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_OutOfOffset : of_value.

  Lemma of_value_with_CreateCollision :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateCollision" [] =
    φ CreateCollision.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CreateCollision : of_value.

  Lemma of_value_with_OverflowPayment :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OverflowPayment" [] =
    φ OverflowPayment.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_OverflowPayment : of_value.

  Lemma of_value_with_PrecompileError :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::PrecompileError" [] =
    φ PrecompileError.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_PrecompileError : of_value.

  Lemma of_value_with_NonceOverflow :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::NonceOverflow" [] =
    φ NonceOverflow.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_NonceOverflow : of_value.

  Lemma of_value_with_CreateContractSizeLimit :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateContractSizeLimit" [] =
    φ CreateContractSizeLimit.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CreateContractSizeLimit : of_value.

  Lemma of_value_with_CreateContractStartingWithEF :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateContractStartingWithEF" [] =
    φ CreateContractStartingWithEF.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CreateContractStartingWithEF : of_value.

  Lemma of_value_with_CreateInitCodeSizeLimit :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateInitCodeSizeLimit" [] =
    φ CreateInitCodeSizeLimit.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CreateInitCodeSizeLimit : of_value.

  Lemma of_value_with_FatalExternalError :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::FatalExternalError" [] =
    φ FatalExternalError.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_FatalExternalError : of_value.

  Lemma of_value_with_ReturnContractInNotInitEOF :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::ReturnContractInNotInitEOF" [] =
    φ ReturnContractInNotInitEOF.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_ReturnContractInNotInitEOF : of_value.

  Lemma of_value_with_EOFOpcodeDisabledInLegacy :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::EOFOpcodeDisabledInLegacy" [] =
    φ EOFOpcodeDisabledInLegacy.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_EOFOpcodeDisabledInLegacy : of_value.

  Lemma of_value_with_SubRoutineStackOverflow :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::SubRoutineStackOverflow" [] =
    φ SubRoutineStackOverflow.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_SubRoutineStackOverflow : of_value.

  Lemma of_value_with_EofAuxDataOverflow :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::EofAuxDataOverflow" [] =
    φ EofAuxDataOverflow.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_EofAuxDataOverflow : of_value.

  Lemma of_value_with_EofAuxDataTooSmall :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::EofAuxDataTooSmall" [] =
    φ EofAuxDataTooSmall.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_EofAuxDataTooSmall : of_value.

  Lemma of_value_with_InvalidEXTCALLTarget :
    Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidEXTCALLTarget" [] =
    φ InvalidEXTCALLTarget.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InvalidEXTCALLTarget : of_value.

  Definition of_value_Continue :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::Continue" []
    ).
  Proof. econstructor; apply of_value_with_Continue; eassumption. Defined.
  Smpl Add simple apply of_value_Continue : of_value.

  Definition of_value_Stop :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::Stop" []
    ).
  Proof. econstructor; apply of_value_with_Stop; eassumption. Defined.
  Smpl Add simple apply of_value_Stop : of_value.

  Definition of_value_Return :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::Return" []
    ).
  Proof. econstructor; apply of_value_with_Return; eassumption. Defined.
  Smpl Add simple apply of_value_Return : of_value.

  Definition of_value_SelfDestruct :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::SelfDestruct" []
    ).
  Proof. econstructor; apply of_value_with_SelfDestruct; eassumption. Defined.
  Smpl Add simple apply of_value_SelfDestruct : of_value.

  Definition of_value_ReturnContract :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::ReturnContract" []
    ).
  Proof. econstructor; apply of_value_with_ReturnContract; eassumption. Defined.
  Smpl Add simple apply of_value_ReturnContract : of_value.

  Definition of_value_Revert :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::Revert" []
    ).
  Proof. econstructor; apply of_value_with_Revert; eassumption. Defined.
  Smpl Add simple apply of_value_Revert : of_value.

  Definition of_value_CallTooDeep :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CallTooDeep" []
    ).
  Proof. econstructor; apply of_value_with_CallTooDeep; eassumption. Defined.
  Smpl Add simple apply of_value_CallTooDeep : of_value.

  Definition of_value_OutOfFunds :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OutOfFunds" []
    ).
  Proof. econstructor; apply of_value_with_OutOfFunds; eassumption. Defined.
  Smpl Add simple apply of_value_OutOfFunds : of_value.

  Definition of_value_CreateInitCodeStartingEF00 :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateInitCodeStartingEF00" []
    ).
  Proof. econstructor; apply of_value_with_CreateInitCodeStartingEF00; eassumption. Defined.
  Smpl Add simple apply of_value_CreateInitCodeStartingEF00 : of_value.

  Definition of_value_InvalidEOFInitCode :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidEOFInitCode" []
    ).
  Proof. econstructor; apply of_value_with_InvalidEOFInitCode; eassumption. Defined.
  Smpl Add simple apply of_value_InvalidEOFInitCode : of_value.

  Definition of_value_InvalidExtDelegateCallTarget :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidExtDelegateCallTarget" []
    ).
  Proof. econstructor; apply of_value_with_InvalidExtDelegateCallTarget; eassumption. Defined.
  Smpl Add simple apply of_value_InvalidExtDelegateCallTarget : of_value.

  Definition of_value_CallOrCreate :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CallOrCreate" []
    ).
  Proof. econstructor; apply of_value_with_CallOrCreate; eassumption. Defined.
  Smpl Add simple apply of_value_CallOrCreate : of_value.

  Definition of_value_OutOfGas :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OutOfGas" []
    ).
  Proof. econstructor; apply of_value_with_OutOfGas; eassumption. Defined.
  Smpl Add simple apply of_value_OutOfGas : of_value.

  Definition of_value_MemoryOOG :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::MemoryOOG" []
    ).
  Proof. econstructor; apply of_value_with_MemoryOOG; eassumption. Defined.
  Smpl Add simple apply of_value_MemoryOOG : of_value.

  Definition of_value_MemoryLimitOOG :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::MemoryLimitOOG" []
    ).
  Proof. econstructor; apply of_value_with_MemoryLimitOOG; eassumption. Defined.
  Smpl Add simple apply of_value_MemoryLimitOOG : of_value.

  Definition of_value_PrecompileOOG :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::PrecompileOOG" []
    ).
  Proof. econstructor; apply of_value_with_PrecompileOOG; eassumption. Defined.
  Smpl Add simple apply of_value_PrecompileOOG : of_value.

  Definition of_value_InvalidOperandOOG :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidOperandOOG" []
    ).
  Proof. econstructor; apply of_value_with_InvalidOperandOOG; eassumption. Defined.
  Smpl Add simple apply of_value_InvalidOperandOOG : of_value.

  Definition of_value_ReentrancySentryOOG :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::ReentrancySentryOOG" []
    ).
  Proof. econstructor; apply of_value_with_ReentrancySentryOOG; eassumption. Defined.
  Smpl Add simple apply of_value_ReentrancySentryOOG : of_value.

  Definition of_value_OpcodeNotFound :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OpcodeNotFound" []
    ).
  Proof. econstructor; apply of_value_with_OpcodeNotFound; eassumption. Defined.
  Smpl Add simple apply of_value_OpcodeNotFound : of_value.

  Definition of_value_CallNotAllowedInsideStatic :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CallNotAllowedInsideStatic" []
    ).
  Proof. econstructor; apply of_value_with_CallNotAllowedInsideStatic; eassumption. Defined.
  Smpl Add simple apply of_value_CallNotAllowedInsideStatic : of_value.

  Definition of_value_StateChangeDuringStaticCall :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::StateChangeDuringStaticCall" []
    ).
  Proof. econstructor; apply of_value_with_StateChangeDuringStaticCall; eassumption. Defined.
  Smpl Add simple apply of_value_StateChangeDuringStaticCall : of_value.

  Definition of_value_InvalidFEOpcode :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidFEOpcode" []
    ).
  Proof. econstructor; apply of_value_with_InvalidFEOpcode; eassumption. Defined.
  Smpl Add simple apply of_value_InvalidFEOpcode : of_value.

  Definition of_value_InvalidJump :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidJump" []
    ).
  Proof. econstructor; apply of_value_with_InvalidJump; eassumption. Defined.
  Smpl Add simple apply of_value_InvalidJump : of_value.

  Definition of_value_NotActivated :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::NotActivated" []
    ).
  Proof. econstructor; apply of_value_with_NotActivated; eassumption. Defined.
  Smpl Add simple apply of_value_NotActivated : of_value.

  Definition of_value_StackUnderflow :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::StackUnderflow" []
    ).
  Proof. econstructor; apply of_value_with_StackUnderflow; eassumption. Defined.
  Smpl Add simple apply of_value_StackUnderflow : of_value.

  Definition of_value_StackOverflow :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::StackOverflow" []
    ).
  Proof. econstructor; apply of_value_with_StackOverflow; eassumption. Defined.
  Smpl Add simple apply of_value_StackOverflow : of_value.

  Definition of_value_OutOfOffset :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OutOfOffset" []
    ).
  Proof. econstructor; apply of_value_with_OutOfOffset; eassumption. Defined.
  Smpl Add simple apply of_value_OutOfOffset : of_value.

  Definition of_value_CreateCollision :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateCollision" []
    ).
  Proof. econstructor; apply of_value_with_CreateCollision; eassumption. Defined.
  Smpl Add simple apply of_value_CreateCollision : of_value.

  Definition of_value_OverflowPayment :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OverflowPayment" []
    ).
  Proof. econstructor; apply of_value_with_OverflowPayment; eassumption. Defined.
  Smpl Add simple apply of_value_OverflowPayment : of_value.

  Definition of_value_PrecompileError :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::PrecompileError" []
    ).
  Proof. econstructor; apply of_value_with_PrecompileError; eassumption. Defined.
  Smpl Add simple apply of_value_PrecompileError : of_value.

  Definition of_value_NonceOverflow :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::NonceOverflow" []
    ).
  Proof. econstructor; apply of_value_with_NonceOverflow; eassumption. Defined.
  Smpl Add simple apply of_value_NonceOverflow : of_value.

  Definition of_value_CreateContractSizeLimit :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateContractSizeLimit" []
    ).
  Proof. econstructor; apply of_value_with_CreateContractSizeLimit; eassumption. Defined.
  Smpl Add simple apply of_value_CreateContractSizeLimit : of_value.

  Definition of_value_CreateContractStartingWithEF :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateContractStartingWithEF" []
    ).
  Proof. econstructor; apply of_value_with_CreateContractStartingWithEF; eassumption. Defined.
  Smpl Add simple apply of_value_CreateContractStartingWithEF : of_value.

  Definition of_value_CreateInitCodeSizeLimit :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateInitCodeSizeLimit" []
    ).
  Proof. econstructor; apply of_value_with_CreateInitCodeSizeLimit; eassumption. Defined.
  Smpl Add simple apply of_value_CreateInitCodeSizeLimit : of_value.

  Definition of_value_FatalExternalError :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::FatalExternalError" []
    ).
  Proof. econstructor; apply of_value_with_FatalExternalError; eassumption. Defined.
  Smpl Add simple apply of_value_FatalExternalError : of_value.

  Definition of_value_ReturnContractInNotInitEOF :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::ReturnContractInNotInitEOF" []
    ).
  Proof. econstructor; apply of_value_with_ReturnContractInNotInitEOF; eassumption. Defined.
  Smpl Add simple apply of_value_ReturnContractInNotInitEOF : of_value.

  Definition of_value_EOFOpcodeDisabledInLegacy :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::EOFOpcodeDisabledInLegacy" []
    ).
  Proof. econstructor; apply of_value_with_EOFOpcodeDisabledInLegacy; eassumption. Defined.
  Smpl Add simple apply of_value_EOFOpcodeDisabledInLegacy : of_value.

  Definition of_value_SubRoutineStackOverflow :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::SubRoutineStackOverflow" []
    ).
  Proof. econstructor; apply of_value_with_SubRoutineStackOverflow; eassumption. Defined.
  Smpl Add simple apply of_value_SubRoutineStackOverflow : of_value.

  Definition of_value_EofAuxDataOverflow :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::EofAuxDataOverflow" []
    ).
  Proof. econstructor; apply of_value_with_EofAuxDataOverflow; eassumption. Defined.
  Smpl Add simple apply of_value_EofAuxDataOverflow : of_value.

  Definition of_value_EofAuxDataTooSmall :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::EofAuxDataTooSmall" []
    ).
  Proof. econstructor; apply of_value_with_EofAuxDataTooSmall; eassumption. Defined.
  Smpl Add simple apply of_value_EofAuxDataTooSmall : of_value.

  Definition of_value_InvalidEXTCALLTarget :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidEXTCALLTarget" []
    ).
  Proof. econstructor; apply of_value_with_InvalidEXTCALLTarget; eassumption. Defined.
  Smpl Add simple apply of_value_InvalidEXTCALLTarget : of_value.
End InstructionResult.

Module InternalResult.
  Inductive t : Set :=
  | InternalContinue
  | InternalCallOrCreate
  | CreateInitCodeStartingEF00
  | InvalidExtDelegateCallTarget
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::instruction_result::InternalResult";
    φ x :=
      match x with
      | InternalContinue =>
        Value.StructTuple "revm_interpreter::instruction_result::InternalResult::InternalContinue" []
      | InternalCallOrCreate =>
        Value.StructTuple "revm_interpreter::instruction_result::InternalResult::InternalCallOrCreate" []
      | CreateInitCodeStartingEF00 =>
        Value.StructTuple "revm_interpreter::instruction_result::InternalResult::CreateInitCodeStartingEF00" []
      | InvalidExtDelegateCallTarget =>
        Value.StructTuple "revm_interpreter::instruction_result::InternalResult::InvalidExtDelegateCallTarget" []
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_interpreter::instruction_result::InternalResult").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_InternalContinue :
    Value.StructTuple "revm_interpreter::instruction_result::InternalResult::InternalContinue" [] =
    φ InternalContinue.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InternalContinue : of_value.

  Lemma of_value_with_InternalCallOrCreate :
    Value.StructTuple "revm_interpreter::instruction_result::InternalResult::InternalCallOrCreate" [] =
    φ InternalCallOrCreate.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InternalCallOrCreate : of_value.

  Lemma of_value_with_CreateInitCodeStartingEF00 :
    Value.StructTuple "revm_interpreter::instruction_result::InternalResult::CreateInitCodeStartingEF00" [] =
    φ CreateInitCodeStartingEF00.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CreateInitCodeStartingEF00 : of_value.

  Lemma of_value_with_InvalidExtDelegateCallTarget :
    Value.StructTuple "revm_interpreter::instruction_result::InternalResult::InvalidExtDelegateCallTarget" [] =
    φ InvalidExtDelegateCallTarget.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InvalidExtDelegateCallTarget : of_value.

  Definition of_value_InternalContinue :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InternalResult::InternalContinue" []
    ).
  Proof. econstructor; apply of_value_with_InternalContinue; eassumption. Defined.
  Smpl Add simple apply of_value_InternalContinue : of_value.

  Definition of_value_InternalCallOrCreate :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InternalResult::InternalCallOrCreate" []
    ).
  Proof. econstructor; apply of_value_with_InternalCallOrCreate; eassumption. Defined.
  Smpl Add simple apply of_value_InternalCallOrCreate : of_value.

  Definition of_value_CreateInitCodeStartingEF00 :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InternalResult::CreateInitCodeStartingEF00" []
    ).
  Proof. econstructor; apply of_value_with_CreateInitCodeStartingEF00; eassumption. Defined.
  Smpl Add simple apply of_value_CreateInitCodeStartingEF00 : of_value.

  Definition of_value_InvalidExtDelegateCallTarget :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::InternalResult::InvalidExtDelegateCallTarget" []
    ).
  Proof. econstructor; apply of_value_with_InvalidExtDelegateCallTarget; eassumption. Defined.
  Smpl Add simple apply of_value_InvalidExtDelegateCallTarget : of_value.
End InternalResult.

Module SuccessOrHalt.
  Inductive t (HaltReasonT: Set) : Set :=
  | Success
    (_ : revm_context_interface.links.result.SuccessReason.t)
  | Revert
  | Halt
    (_ : HaltReasonT)
  | FatalExternalError
  | Internal
    (_ : revm_interpreter.links.instruction_result.InternalResult.t)
  .
  Arguments Success Revert Halt FatalExternalError Internal {_}.

  Global Instance IsLink (HaltReasonT: Set) : Link t HaltReasonT := {
    Φ := Ty.path "revm_interpreter::instruction_result::SuccessOrHalt";
    φ x :=
      match x with
      | Success γ0 =>
        Value.StructTuple "revm_interpreter::instruction_result::SuccessOrHalt::Success" [
          φ γ0
        ]
      | Revert =>
        Value.StructTuple "revm_interpreter::instruction_result::SuccessOrHalt::Revert" []
      | Halt γ0 =>
        Value.StructTuple "revm_interpreter::instruction_result::SuccessOrHalt::Halt" [
          φ γ0
        ]
      | FatalExternalError =>
        Value.StructTuple "revm_interpreter::instruction_result::SuccessOrHalt::FatalExternalError" []
      | Internal γ0 =>
        Value.StructTuple "revm_interpreter::instruction_result::SuccessOrHalt::Internal" [
          φ γ0
        ]
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_interpreter::instruction_result::SuccessOrHalt").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_Success
    (γ0 : revm_context_interface.links.result.SuccessReason.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_interpreter::instruction_result::SuccessOrHalt::Success" [
      γ0
    ] =
    φ (Success γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Success : of_value.

  Lemma of_value_with_Revert :
    Value.StructTuple "revm_interpreter::instruction_result::SuccessOrHalt::Revert" [] =
    φ Revert.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Revert : of_value.

  Lemma of_value_with_Halt
    (γ0 : HaltReasonT) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_interpreter::instruction_result::SuccessOrHalt::Halt" [
      γ0
    ] =
    φ (Halt γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Halt : of_value.

  Lemma of_value_with_FatalExternalError :
    Value.StructTuple "revm_interpreter::instruction_result::SuccessOrHalt::FatalExternalError" [] =
    φ FatalExternalError.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_FatalExternalError : of_value.

  Lemma of_value_with_Internal
    (γ0 : revm_interpreter.links.instruction_result.InternalResult.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_interpreter::instruction_result::SuccessOrHalt::Internal" [
      γ0
    ] =
    φ (Internal γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Internal : of_value.

  Definition of_value_Success
    (γ0 : revm_context_interface.links.result.SuccessReason.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::SuccessOrHalt::Success" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Success; eassumption. Defined.
  Smpl Add simple apply of_value_Success : of_value.

  Definition of_value_Revert :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::SuccessOrHalt::Revert" []
    ).
  Proof. econstructor; apply of_value_with_Revert; eassumption. Defined.
  Smpl Add simple apply of_value_Revert : of_value.

  Definition of_value_Halt
    (γ0 : HaltReasonT) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::SuccessOrHalt::Halt" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Halt; eassumption. Defined.
  Smpl Add simple apply of_value_Halt : of_value.

  Definition of_value_FatalExternalError :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::SuccessOrHalt::FatalExternalError" []
    ).
  Proof. econstructor; apply of_value_with_FatalExternalError; eassumption. Defined.
  Smpl Add simple apply of_value_FatalExternalError : of_value.

  Definition of_value_Internal
    (γ0 : revm_interpreter.links.instruction_result.InternalResult.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_interpreter::instruction_result::SuccessOrHalt::Internal" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Internal; eassumption. Defined.
  Smpl Add simple apply of_value_Internal : of_value.
End SuccessOrHalt.

Module Interpreter.
  Record t {WIRE: Set} : Set := {
    bytecode: Unknown type Associated;
    stack: Unknown type Associated;
    return_data: Unknown type Associated;
    memory: Unknown type Associated;
    input: Unknown type Associated;
    sub_routine: Unknown type Associated;
    control: Unknown type Associated;
    runtime_flag: Unknown type Associated;
    extend: Unknown type Associated;
  }.
  Arguments Build_t {_}.
  Arguments t : clear implicits.

  Global Instance IsLink {WIRE: Set} `{Link WIRE} : Link (t WIRE) := {
    Φ := Ty.path "revm_interpreter::interpreter::Interpreter";
    φ '(Build_t bytecode stack return_data memory input sub_routine control runtime_flag extend) :=
      Value.StructRecord "revm_interpreter::interpreter::Interpreter" [
        ("bytecode", φ bytecode);
        ("stack", φ stack);
        ("return_data", φ return_data);
        ("memory", φ memory);
        ("input", φ input);
        ("sub_routine", φ sub_routine);
        ("control", φ control);
        ("runtime_flag", φ runtime_flag);
        ("extend", φ extend)
      ]
  }.
End Interpreter.

Module EthInterpreter.
  Record t {EXT MG: Set} : Set := {
    _phantom: core.links.marker.PhantomData.t (Function0.t (EXT * MG));
  }.
  Arguments Build_t {_ _}.
  Arguments t : clear implicits.

  Global Instance IsLink {EXT MG: Set} `{Link EXT} `{Link MG} : Link (t EXT MG) := {
    Φ := Ty.path "revm_interpreter::interpreter::EthInterpreter";
    φ '(Build_t _phantom) :=
      Value.StructRecord "revm_interpreter::interpreter::EthInterpreter" [
        ("_phantom", φ _phantom)
      ]
  }.
End EthInterpreter.

Module EthInstructionProvider.
  Record t {WIRE HOST: Set} : Set := {
    instruction_table: alloc.links.rc.Rc.t (array.t 256 (Function2.t (Ref.t Pointer.Kind.MutRef (revm_interpreter.links.interpreter.Interpreter.t WIRE)) (Ref.t Pointer.Kind.MutRef HOST) ())) alloc.links.alloc.Global.t;
  }.
  Arguments Build_t {_ _}.
  Arguments t : clear implicits.

  Global Instance IsLink {WIRE HOST: Set} `{Link WIRE} `{Link HOST} : Link (t WIRE HOST) := {
    Φ := Ty.path "revm_interpreter::interpreter::EthInstructionProvider";
    φ '(Build_t instruction_table) :=
      Value.StructRecord "revm_interpreter::interpreter::EthInstructionProvider" [
        ("instruction_table", φ instruction_table)
      ]
  }.
End EthInstructionProvider.

Module InterpreterResult.
  Record t : Set := {
    result: revm_interpreter.links.instruction_result.InstructionResult.t;
    output: alloy_primitives.links.bytes_.Bytes.t;
    gas: revm_interpreter.links.gas.Gas.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter::InterpreterResult";
    φ '(Build_t result output gas) :=
      Value.StructRecord "revm_interpreter::interpreter::InterpreterResult" [
        ("result", φ result);
        ("output", φ output);
        ("gas", φ gas)
      ]
  }.
End InterpreterResult.

Module FrameInput.
  Inductive t : Set :=
  | Call
    (_ : alloc.links.boxed.Box.t revm_interpreter.interpreter_action.links.call_inputs.CallInputs.t alloc.links.alloc.Global.t)
  | Create
    (_ : alloc.links.boxed.Box.t revm_interpreter.interpreter_action.links.create_inputs.CreateInputs.t alloc.links.alloc.Global.t)
  | EOFCreate
    (_ : alloc.links.boxed.Box.t revm_interpreter.interpreter_action.links.eof_create_inputs.EOFCreateInputs.t alloc.links.alloc.Global.t)
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter_action::FrameInput";
    φ x :=
      match x with
      | Call γ0 =>
        Value.StructTuple "revm_interpreter::interpreter_action::FrameInput::Call" [
          φ γ0
        ]
      | Create γ0 =>
        Value.StructTuple "revm_interpreter::interpreter_action::FrameInput::Create" [
          φ γ0
        ]
      | EOFCreate γ0 =>
        Value.StructTuple "revm_interpreter::interpreter_action::FrameInput::EOFCreate" [
          φ γ0
        ]
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_interpreter::interpreter_action::FrameInput").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_Call
    (γ0 : alloc.links.boxed.Box.t revm_interpreter.interpreter_action.links.call_inputs.CallInputs.t alloc.links.alloc.Global.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_interpreter::interpreter_action::FrameInput::Call" [
      γ0
    ] =
    φ (Call γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Call : of_value.

  Lemma of_value_with_Create
    (γ0 : alloc.links.boxed.Box.t revm_interpreter.interpreter_action.links.create_inputs.CreateInputs.t alloc.links.alloc.Global.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_interpreter::interpreter_action::FrameInput::Create" [
      γ0
    ] =
    φ (Create γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Create : of_value.

  Lemma of_value_with_EOFCreate
    (γ0 : alloc.links.boxed.Box.t revm_interpreter.interpreter_action.links.eof_create_inputs.EOFCreateInputs.t alloc.links.alloc.Global.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_interpreter::interpreter_action::FrameInput::EOFCreate" [
      γ0
    ] =
    φ (EOFCreate γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_EOFCreate : of_value.

  Definition of_value_Call
    (γ0 : alloc.links.boxed.Box.t revm_interpreter.interpreter_action.links.call_inputs.CallInputs.t alloc.links.alloc.Global.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_interpreter::interpreter_action::FrameInput::Call" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Call; eassumption. Defined.
  Smpl Add simple apply of_value_Call : of_value.

  Definition of_value_Create
    (γ0 : alloc.links.boxed.Box.t revm_interpreter.interpreter_action.links.create_inputs.CreateInputs.t alloc.links.alloc.Global.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_interpreter::interpreter_action::FrameInput::Create" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Create; eassumption. Defined.
  Smpl Add simple apply of_value_Create : of_value.

  Definition of_value_EOFCreate
    (γ0 : alloc.links.boxed.Box.t revm_interpreter.interpreter_action.links.eof_create_inputs.EOFCreateInputs.t alloc.links.alloc.Global.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_interpreter::interpreter_action::FrameInput::EOFCreate" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_EOFCreate; eassumption. Defined.
  Smpl Add simple apply of_value_EOFCreate : of_value.
End FrameInput.

Module InterpreterAction.
  Inductive t : Set :=
  | NewFrame
    (_ : revm_interpreter.links.interpreter_action.FrameInput.t)
  | Return
    (result : revm_interpreter.links.interpreter.InterpreterResult.t)
  | None
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter_action::InterpreterAction";
    φ x :=
      match x with
      | NewFrame γ0 =>
        Value.StructTuple "revm_interpreter::interpreter_action::InterpreterAction::NewFrame" [
          φ γ0
        ]
      | Return result =>
        Value.StructRecord "revm_interpreter::interpreter_action::InterpreterAction::Return" [
          ("result", φ result)
        ]
      | None =>
        Value.StructTuple "revm_interpreter::interpreter_action::InterpreterAction::None" []
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_interpreter::interpreter_action::InterpreterAction").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_NewFrame
    (γ0 : revm_interpreter.links.interpreter_action.FrameInput.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_interpreter::interpreter_action::InterpreterAction::NewFrame" [
      γ0
    ] =
    φ (NewFrame γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_NewFrame : of_value.

  Lemma of_value_with_Return
    (result : revm_interpreter.links.interpreter.InterpreterResult.t) (result' : Value.t) :
    result' = φ result ->
    Value.StructRecord "revm_interpreter::interpreter_action::InterpreterAction::Return" [
      ("result", result')
    ] =
    φ (Return result).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Return : of_value.

  Lemma of_value_with_None :
    Value.StructTuple "revm_interpreter::interpreter_action::InterpreterAction::None" [] =
    φ None.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_None : of_value.

  Definition of_value_NewFrame
    (γ0 : revm_interpreter.links.interpreter_action.FrameInput.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_interpreter::interpreter_action::InterpreterAction::NewFrame" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_NewFrame; eassumption. Defined.
  Smpl Add simple apply of_value_NewFrame : of_value.

  Definition of_value_Return
    (result : revm_interpreter.links.interpreter.InterpreterResult.t) (result' : Value.t) :
    result' = φ result ->
    OfValue.t (
      Value.StructRecord "revm_interpreter::interpreter_action::InterpreterAction::Return" [
        ("result", result')
      ]
    ).
  Proof. econstructor; apply of_value_with_Return; eassumption. Defined.
  Smpl Add simple apply of_value_Return : of_value.

  Definition of_value_None :
    OfValue.t (
      Value.StructTuple "revm_interpreter::interpreter_action::InterpreterAction::None" []
    ).
  Proof. econstructor; apply of_value_with_None; eassumption. Defined.
  Smpl Add simple apply of_value_None : of_value.
End InterpreterAction.

Module InstructionTables.
  Inductive t (W H CI: Set) : Set :=
  | Plain
    (_ : alloc.links.boxed.Box.t (array.t 256 (Function2.t (Ref.t Pointer.Kind.MutRef (revm_interpreter.links.interpreter.Interpreter.t W)) (Ref.t Pointer.Kind.MutRef H) ())) alloc.links.alloc.Global.t)
  | Custom
    (_ : alloc.links.boxed.Box.t (array.t 256 CI) alloc.links.alloc.Global.t)
  .
  Arguments Plain Custom {_ _ _}.

  Global Instance IsLink (W H CI: Set) : Link t W H CI := {
    Φ := Ty.path "revm_interpreter::table::InstructionTables";
    φ x :=
      match x with
      | Plain γ0 =>
        Value.StructTuple "revm_interpreter::table::InstructionTables::Plain" [
          φ γ0
        ]
      | Custom γ0 =>
        Value.StructTuple "revm_interpreter::table::InstructionTables::Custom" [
          φ γ0
        ]
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_interpreter::table::InstructionTables").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_Plain
    (γ0 : alloc.links.boxed.Box.t (array.t 256 (Function2.t (Ref.t Pointer.Kind.MutRef (revm_interpreter.links.interpreter.Interpreter.t W)) (Ref.t Pointer.Kind.MutRef H) ())) alloc.links.alloc.Global.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_interpreter::table::InstructionTables::Plain" [
      γ0
    ] =
    φ (Plain γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Plain : of_value.

  Lemma of_value_with_Custom
    (γ0 : alloc.links.boxed.Box.t (array.t 256 CI) alloc.links.alloc.Global.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_interpreter::table::InstructionTables::Custom" [
      γ0
    ] =
    φ (Custom γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Custom : of_value.

  Definition of_value_Plain
    (γ0 : alloc.links.boxed.Box.t (array.t 256 (Function2.t (Ref.t Pointer.Kind.MutRef (revm_interpreter.links.interpreter.Interpreter.t W)) (Ref.t Pointer.Kind.MutRef H) ())) alloc.links.alloc.Global.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_interpreter::table::InstructionTables::Plain" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Plain; eassumption. Defined.
  Smpl Add simple apply of_value_Plain : of_value.

  Definition of_value_Custom
    (γ0 : alloc.links.boxed.Box.t (array.t 256 CI) alloc.links.alloc.Global.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_interpreter::table::InstructionTables::Custom" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Custom; eassumption. Defined.
  Smpl Add simple apply of_value_Custom : of_value.
End InstructionTables.

Module Sign.
  Inductive t : Set :=
  | Minus
  | Zero
  | Plus
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::instructions::i256::Sign";
    φ x :=
      match x with
      | Minus =>
        Value.StructTuple "revm_interpreter::instructions::i256::Sign::Minus" []
      | Zero =>
        Value.StructTuple "revm_interpreter::instructions::i256::Sign::Zero" []
      | Plus =>
        Value.StructTuple "revm_interpreter::instructions::i256::Sign::Plus" []
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_interpreter::instructions::i256::Sign").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_Minus :
    Value.StructTuple "revm_interpreter::instructions::i256::Sign::Minus" [] =
    φ Minus.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Minus : of_value.

  Lemma of_value_with_Zero :
    Value.StructTuple "revm_interpreter::instructions::i256::Sign::Zero" [] =
    φ Zero.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Zero : of_value.

  Lemma of_value_with_Plus :
    Value.StructTuple "revm_interpreter::instructions::i256::Sign::Plus" [] =
    φ Plus.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Plus : of_value.

  Definition of_value_Minus :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instructions::i256::Sign::Minus" []
    ).
  Proof. econstructor; apply of_value_with_Minus; eassumption. Defined.
  Smpl Add simple apply of_value_Minus : of_value.

  Definition of_value_Zero :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instructions::i256::Sign::Zero" []
    ).
  Proof. econstructor; apply of_value_with_Zero; eassumption. Defined.
  Smpl Add simple apply of_value_Zero : of_value.

  Definition of_value_Plus :
    OfValue.t (
      Value.StructTuple "revm_interpreter::instructions::i256::Sign::Plus" []
    ).
  Proof. econstructor; apply of_value_with_Plus; eassumption. Defined.
  Smpl Add simple apply of_value_Plus : of_value.
End Sign.

Module ExtBytecode.
  Record t : Set := {
    base: revm_bytecode.links.bytecode.Bytecode.t;
    instruction_pointer: Ref.t Pointer.Kind.ConstPointer U8.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter::ext_bytecode::ExtBytecode";
    φ '(Build_t base instruction_pointer) :=
      Value.StructRecord "revm_interpreter::interpreter::ext_bytecode::ExtBytecode" [
        ("base", φ base);
        ("instruction_pointer", φ instruction_pointer)
      ]
  }.
End ExtBytecode.

Module InputsImpl.
  Record t : Set := {
    target_address: alloy_primitives.bits.links.address.Address.t;
    caller_address: alloy_primitives.bits.links.address.Address.t;
    input: alloy_primitives.links.bytes_.Bytes.t;
    call_value: ruint.Uint.t 256 4;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter::input::InputsImpl";
    φ '(Build_t target_address caller_address input call_value) :=
      Value.StructRecord "revm_interpreter::interpreter::input::InputsImpl" [
        ("target_address", φ target_address);
        ("caller_address", φ caller_address);
        ("input", φ input);
        ("call_value", φ call_value)
      ]
  }.
End InputsImpl.

Module LoopControl.
  Record t : Set := {
    instruction_result: revm_interpreter.links.instruction_result.InstructionResult.t;
    next_action: revm_interpreter.links.interpreter_action.InterpreterAction.t;
    gas: revm_interpreter.links.gas.Gas.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter::loop_control::LoopControl";
    φ '(Build_t instruction_result next_action gas) :=
      Value.StructRecord "revm_interpreter::interpreter::loop_control::LoopControl" [
        ("instruction_result", φ instruction_result);
        ("next_action", φ next_action);
        ("gas", φ gas)
      ]
  }.
End LoopControl.

Module RuntimeFlags.
  Record t : Set := {
    is_static: bool;
    is_eof_init: bool;
    is_eof: bool;
    spec_id: revm_specification.links.hardfork.SpecId.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter::runtime_flags::RuntimeFlags";
    φ '(Build_t is_static is_eof_init is_eof spec_id) :=
      Value.StructRecord "revm_interpreter::interpreter::runtime_flags::RuntimeFlags" [
        ("is_static", φ is_static);
        ("is_eof_init", φ is_eof_init);
        ("is_eof", φ is_eof);
        ("spec_id", φ spec_id)
      ]
  }.
End RuntimeFlags.

Module SharedMemory.
  Record t : Set := {
    buffer: alloc.links.vec.Vec.t U8.t alloc.links.alloc.Global.t;
    checkpoints: alloc.links.vec.Vec.t Usize.t alloc.links.alloc.Global.t;
    last_checkpoint: Usize.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter::shared_memory::SharedMemory";
    φ '(Build_t buffer checkpoints last_checkpoint) :=
      Value.StructRecord "revm_interpreter::interpreter::shared_memory::SharedMemory" [
        ("buffer", φ buffer);
        ("checkpoints", φ checkpoints);
        ("last_checkpoint", φ last_checkpoint)
      ]
  }.
End SharedMemory.

Module Stack.
  Record t : Set := {
    data: alloc.links.vec.Vec.t (ruint.Uint.t 256 4) alloc.links.alloc.Global.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter::stack::Stack";
    φ '(Build_t data) :=
      Value.StructRecord "revm_interpreter::interpreter::stack::Stack" [
        ("data", φ data)
      ]
  }.
End Stack.

Module SubRoutineReturnFrame.
  Record t : Set := {
    idx: Usize.t;
    pc: Usize.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter::subroutine_stack::SubRoutineReturnFrame";
    φ '(Build_t idx pc) :=
      Value.StructRecord "revm_interpreter::interpreter::subroutine_stack::SubRoutineReturnFrame" [
        ("idx", φ idx);
        ("pc", φ pc)
      ]
  }.
End SubRoutineReturnFrame.

Module SubRoutineImpl.
  Record t : Set := {
    return_stack: alloc.links.vec.Vec.t revm_interpreter.interpreter.links.subroutine_stack.SubRoutineReturnFrame.t alloc.links.alloc.Global.t;
    current_code_idx: Usize.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter::subroutine_stack::SubRoutineImpl";
    φ '(Build_t return_stack current_code_idx) :=
      Value.StructRecord "revm_interpreter::interpreter::subroutine_stack::SubRoutineImpl" [
        ("return_stack", φ return_stack);
        ("current_code_idx", φ current_code_idx)
      ]
  }.
End SubRoutineImpl.

Module CallInputs.
  Record t : Set := {
    input: alloy_primitives.links.bytes_.Bytes.t;
    return_memory_offset: core.ops.links.range.Range.t Usize.t;
    gas_limit: U64.t;
    bytecode_address: alloy_primitives.bits.links.address.Address.t;
    target_address: alloy_primitives.bits.links.address.Address.t;
    caller: alloy_primitives.bits.links.address.Address.t;
    value: revm_interpreter.interpreter_action.links.call_inputs.CallValue.t;
    scheme: revm_interpreter.interpreter_action.links.call_inputs.CallScheme.t;
    is_static: bool;
    is_eof: bool;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter_action::call_inputs::CallInputs";
    φ '(Build_t input return_memory_offset gas_limit bytecode_address target_address caller value scheme is_static is_eof) :=
      Value.StructRecord "revm_interpreter::interpreter_action::call_inputs::CallInputs" [
        ("input", φ input);
        ("return_memory_offset", φ return_memory_offset);
        ("gas_limit", φ gas_limit);
        ("bytecode_address", φ bytecode_address);
        ("target_address", φ target_address);
        ("caller", φ caller);
        ("value", φ value);
        ("scheme", φ scheme);
        ("is_static", φ is_static);
        ("is_eof", φ is_eof)
      ]
  }.
End CallInputs.

Module CallScheme.
  Inductive t : Set :=
  | Call
  | CallCode
  | DelegateCall
  | StaticCall
  | ExtCall
  | ExtStaticCall
  | ExtDelegateCall
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter_action::call_inputs::CallScheme";
    φ x :=
      match x with
      | Call =>
        Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::Call" []
      | CallCode =>
        Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::CallCode" []
      | DelegateCall =>
        Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::DelegateCall" []
      | StaticCall =>
        Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::StaticCall" []
      | ExtCall =>
        Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::ExtCall" []
      | ExtStaticCall =>
        Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::ExtStaticCall" []
      | ExtDelegateCall =>
        Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::ExtDelegateCall" []
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_interpreter::interpreter_action::call_inputs::CallScheme").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_Call :
    Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::Call" [] =
    φ Call.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Call : of_value.

  Lemma of_value_with_CallCode :
    Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::CallCode" [] =
    φ CallCode.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CallCode : of_value.

  Lemma of_value_with_DelegateCall :
    Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::DelegateCall" [] =
    φ DelegateCall.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_DelegateCall : of_value.

  Lemma of_value_with_StaticCall :
    Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::StaticCall" [] =
    φ StaticCall.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_StaticCall : of_value.

  Lemma of_value_with_ExtCall :
    Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::ExtCall" [] =
    φ ExtCall.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_ExtCall : of_value.

  Lemma of_value_with_ExtStaticCall :
    Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::ExtStaticCall" [] =
    φ ExtStaticCall.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_ExtStaticCall : of_value.

  Lemma of_value_with_ExtDelegateCall :
    Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::ExtDelegateCall" [] =
    φ ExtDelegateCall.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_ExtDelegateCall : of_value.

  Definition of_value_Call :
    OfValue.t (
      Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::Call" []
    ).
  Proof. econstructor; apply of_value_with_Call; eassumption. Defined.
  Smpl Add simple apply of_value_Call : of_value.

  Definition of_value_CallCode :
    OfValue.t (
      Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::CallCode" []
    ).
  Proof. econstructor; apply of_value_with_CallCode; eassumption. Defined.
  Smpl Add simple apply of_value_CallCode : of_value.

  Definition of_value_DelegateCall :
    OfValue.t (
      Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::DelegateCall" []
    ).
  Proof. econstructor; apply of_value_with_DelegateCall; eassumption. Defined.
  Smpl Add simple apply of_value_DelegateCall : of_value.

  Definition of_value_StaticCall :
    OfValue.t (
      Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::StaticCall" []
    ).
  Proof. econstructor; apply of_value_with_StaticCall; eassumption. Defined.
  Smpl Add simple apply of_value_StaticCall : of_value.

  Definition of_value_ExtCall :
    OfValue.t (
      Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::ExtCall" []
    ).
  Proof. econstructor; apply of_value_with_ExtCall; eassumption. Defined.
  Smpl Add simple apply of_value_ExtCall : of_value.

  Definition of_value_ExtStaticCall :
    OfValue.t (
      Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::ExtStaticCall" []
    ).
  Proof. econstructor; apply of_value_with_ExtStaticCall; eassumption. Defined.
  Smpl Add simple apply of_value_ExtStaticCall : of_value.

  Definition of_value_ExtDelegateCall :
    OfValue.t (
      Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::ExtDelegateCall" []
    ).
  Proof. econstructor; apply of_value_with_ExtDelegateCall; eassumption. Defined.
  Smpl Add simple apply of_value_ExtDelegateCall : of_value.
End CallScheme.

Module CallValue.
  Inductive t : Set :=
  | Transfer
    (_ : ruint.Uint.t 256 4)
  | Apparent
    (_ : ruint.Uint.t 256 4)
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter_action::call_inputs::CallValue";
    φ x :=
      match x with
      | Transfer γ0 =>
        Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallValue::Transfer" [
          φ γ0
        ]
      | Apparent γ0 =>
        Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallValue::Apparent" [
          φ γ0
        ]
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_interpreter::interpreter_action::call_inputs::CallValue").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_Transfer
    (γ0 : ruint.Uint.t 256 4) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallValue::Transfer" [
      γ0
    ] =
    φ (Transfer γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Transfer : of_value.

  Lemma of_value_with_Apparent
    (γ0 : ruint.Uint.t 256 4) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallValue::Apparent" [
      γ0
    ] =
    φ (Apparent γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Apparent : of_value.

  Definition of_value_Transfer
    (γ0 : ruint.Uint.t 256 4) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallValue::Transfer" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Transfer; eassumption. Defined.
  Smpl Add simple apply of_value_Transfer : of_value.

  Definition of_value_Apparent
    (γ0 : ruint.Uint.t 256 4) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallValue::Apparent" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Apparent; eassumption. Defined.
  Smpl Add simple apply of_value_Apparent : of_value.
End CallValue.

Module CallOutcome.
  Record t : Set := {
    result: revm_interpreter.links.interpreter.InterpreterResult.t;
    memory_offset: core.ops.links.range.Range.t Usize.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter_action::call_outcome::CallOutcome";
    φ '(Build_t result memory_offset) :=
      Value.StructRecord "revm_interpreter::interpreter_action::call_outcome::CallOutcome" [
        ("result", φ result);
        ("memory_offset", φ memory_offset)
      ]
  }.
End CallOutcome.

Module CreateInputs.
  Record t : Set := {
    caller: alloy_primitives.bits.links.address.Address.t;
    scheme: revm_context_interface.links.cfg.CreateScheme.t;
    value: ruint.Uint.t 256 4;
    init_code: alloy_primitives.links.bytes_.Bytes.t;
    gas_limit: U64.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter_action::create_inputs::CreateInputs";
    φ '(Build_t caller scheme value init_code gas_limit) :=
      Value.StructRecord "revm_interpreter::interpreter_action::create_inputs::CreateInputs" [
        ("caller", φ caller);
        ("scheme", φ scheme);
        ("value", φ value);
        ("init_code", φ init_code);
        ("gas_limit", φ gas_limit)
      ]
  }.
End CreateInputs.

Module CreateOutcome.
  Record t : Set := {
    result: revm_interpreter.links.interpreter.InterpreterResult.t;
    address: core.links.option.Option.t alloy_primitives.bits.links.address.Address.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter_action::create_outcome::CreateOutcome";
    φ '(Build_t result address) :=
      Value.StructRecord "revm_interpreter::interpreter_action::create_outcome::CreateOutcome" [
        ("result", φ result);
        ("address", φ address)
      ]
  }.
End CreateOutcome.

Module EOFCreateKind.
  Inductive t : Set :=
  | Tx
    (initdata : alloy_primitives.links.bytes_.Bytes.t)
  | Opcode
    (initcode : revm_bytecode.links.eof.Eof.t)
    (input : alloy_primitives.links.bytes_.Bytes.t)
    (created_address : alloy_primitives.bits.links.address.Address.t)
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter_action::eof_create_inputs::EOFCreateKind";
    φ x :=
      match x with
      | Tx initdata =>
        Value.StructRecord "revm_interpreter::interpreter_action::eof_create_inputs::EOFCreateKind::Tx" [
          ("initdata", φ initdata)
        ]
      | Opcode initcode input created_address =>
        Value.StructRecord "revm_interpreter::interpreter_action::eof_create_inputs::EOFCreateKind::Opcode" [
          ("initcode", φ initcode);
          ("input", φ input);
          ("created_address", φ created_address)
        ]
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_interpreter::interpreter_action::eof_create_inputs::EOFCreateKind").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_Tx
    (initdata : alloy_primitives.links.bytes_.Bytes.t) (initdata' : Value.t) :
    initdata' = φ initdata ->
    Value.StructRecord "revm_interpreter::interpreter_action::eof_create_inputs::EOFCreateKind::Tx" [
      ("initdata", initdata')
    ] =
    φ (Tx initdata).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Tx : of_value.

  Lemma of_value_with_Opcode
    (initcode : revm_bytecode.links.eof.Eof.t) (initcode' : Value.t)
    (input : alloy_primitives.links.bytes_.Bytes.t) (input' : Value.t)
    (created_address : alloy_primitives.bits.links.address.Address.t) (created_address' : Value.t) :
    initcode' = φ initcode ->
    input' = φ input ->
    created_address' = φ created_address ->
    Value.StructRecord "revm_interpreter::interpreter_action::eof_create_inputs::EOFCreateKind::Opcode" [
      ("initcode", initcode');
      ("input", input');
      ("created_address", created_address')
    ] =
    φ (Opcode initcode input created_address).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Opcode : of_value.

  Definition of_value_Tx
    (initdata : alloy_primitives.links.bytes_.Bytes.t) (initdata' : Value.t) :
    initdata' = φ initdata ->
    OfValue.t (
      Value.StructRecord "revm_interpreter::interpreter_action::eof_create_inputs::EOFCreateKind::Tx" [
        ("initdata", initdata')
      ]
    ).
  Proof. econstructor; apply of_value_with_Tx; eassumption. Defined.
  Smpl Add simple apply of_value_Tx : of_value.

  Definition of_value_Opcode
    (initcode : revm_bytecode.links.eof.Eof.t) (initcode' : Value.t)
    (input : alloy_primitives.links.bytes_.Bytes.t) (input' : Value.t)
    (created_address : alloy_primitives.bits.links.address.Address.t) (created_address' : Value.t) :
    initcode' = φ initcode ->
    input' = φ input ->
    created_address' = φ created_address ->
    OfValue.t (
      Value.StructRecord "revm_interpreter::interpreter_action::eof_create_inputs::EOFCreateKind::Opcode" [
        ("initcode", initcode');
        ("input", input');
        ("created_address", created_address')
      ]
    ).
  Proof. econstructor; apply of_value_with_Opcode; eassumption. Defined.
  Smpl Add simple apply of_value_Opcode : of_value.
End EOFCreateKind.

Module EOFCreateInputs.
  Record t : Set := {
    caller: alloy_primitives.bits.links.address.Address.t;
    value: ruint.Uint.t 256 4;
    gas_limit: U64.t;
    kind: revm_interpreter.interpreter_action.links.eof_create_inputs.EOFCreateKind.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::interpreter_action::eof_create_inputs::EOFCreateInputs";
    φ '(Build_t caller value gas_limit kind) :=
      Value.StructRecord "revm_interpreter::interpreter_action::eof_create_inputs::EOFCreateInputs" [
        ("caller", φ caller);
        ("value", φ value);
        ("gas_limit", φ gas_limit);
        ("kind", φ kind)
      ]
  }.
End EOFCreateInputs.

Module PrecompileOutput.
  Record t : Set := {
    gas_used: U64.t;
    bytes: alloy_primitives.links.bytes_.Bytes.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_precompile::interface::PrecompileOutput";
    φ '(Build_t gas_used bytes) :=
      Value.StructRecord "revm_precompile::interface::PrecompileOutput" [
        ("gas_used", φ gas_used);
        ("bytes", φ bytes)
      ]
  }.
End PrecompileOutput.

Module PrecompileErrors.
  Inductive t : Set :=
  | Error
    (_ : revm_precompile.links.interface.PrecompileError.t)
  | Fatal
    (msg : alloc.links.string.String.t)
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_precompile::interface::PrecompileErrors";
    φ x :=
      match x with
      | Error γ0 =>
        Value.StructTuple "revm_precompile::interface::PrecompileErrors::Error" [
          φ γ0
        ]
      | Fatal msg =>
        Value.StructRecord "revm_precompile::interface::PrecompileErrors::Fatal" [
          ("msg", φ msg)
        ]
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_precompile::interface::PrecompileErrors").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_Error
    (γ0 : revm_precompile.links.interface.PrecompileError.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_precompile::interface::PrecompileErrors::Error" [
      γ0
    ] =
    φ (Error γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Error : of_value.

  Lemma of_value_with_Fatal
    (msg : alloc.links.string.String.t) (msg' : Value.t) :
    msg' = φ msg ->
    Value.StructRecord "revm_precompile::interface::PrecompileErrors::Fatal" [
      ("msg", msg')
    ] =
    φ (Fatal msg).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Fatal : of_value.

  Definition of_value_Error
    (γ0 : revm_precompile.links.interface.PrecompileError.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_precompile::interface::PrecompileErrors::Error" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Error; eassumption. Defined.
  Smpl Add simple apply of_value_Error : of_value.

  Definition of_value_Fatal
    (msg : alloc.links.string.String.t) (msg' : Value.t) :
    msg' = φ msg ->
    OfValue.t (
      Value.StructRecord "revm_precompile::interface::PrecompileErrors::Fatal" [
        ("msg", msg')
      ]
    ).
  Proof. econstructor; apply of_value_with_Fatal; eassumption. Defined.
  Smpl Add simple apply of_value_Fatal : of_value.
End PrecompileErrors.

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
      γ0
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
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Other; eassumption. Defined.
  Smpl Add simple apply of_value_Other : of_value.
End PrecompileError.

Module Precompiles.
  Record t : Set := {
    inner: std.collections.hash.links.map.HashMap.t alloy_primitives.bits.links.address.Address.t (Function2.t (Ref.t Pointer.Kind.Ref alloy_primitives.links.bytes_.Bytes.t) U64.t (core.links.result.Result.t revm_precompile.links.interface.PrecompileOutput.t revm_precompile.links.interface.PrecompileErrors.t)) std.hash.links.random.RandomState.t;
    addresses: std.collections.hash.links.set.HashSet.t alloy_primitives.bits.links.address.Address.t std.hash.links.random.RandomState.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_precompile::Precompiles";
    φ '(Build_t inner addresses) :=
      Value.StructRecord "revm_precompile::Precompiles" [
        ("inner", φ inner);
        ("addresses", φ addresses)
      ]
  }.
End Precompiles.

Module PrecompileSpecId.
  Inductive t : Set :=
  | HOMESTEAD
  | BYZANTIUM
  | ISTANBUL
  | BERLIN
  | CANCUN
  | PRAGUE
  | LATEST
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_precompile::PrecompileSpecId";
    φ x :=
      match x with
      | HOMESTEAD =>
        Value.StructTuple "revm_precompile::PrecompileSpecId::HOMESTEAD" []
      | BYZANTIUM =>
        Value.StructTuple "revm_precompile::PrecompileSpecId::BYZANTIUM" []
      | ISTANBUL =>
        Value.StructTuple "revm_precompile::PrecompileSpecId::ISTANBUL" []
      | BERLIN =>
        Value.StructTuple "revm_precompile::PrecompileSpecId::BERLIN" []
      | CANCUN =>
        Value.StructTuple "revm_precompile::PrecompileSpecId::CANCUN" []
      | PRAGUE =>
        Value.StructTuple "revm_precompile::PrecompileSpecId::PRAGUE" []
      | LATEST =>
        Value.StructTuple "revm_precompile::PrecompileSpecId::LATEST" []
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_precompile::PrecompileSpecId").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_HOMESTEAD :
    Value.StructTuple "revm_precompile::PrecompileSpecId::HOMESTEAD" [] =
    φ HOMESTEAD.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_HOMESTEAD : of_value.

  Lemma of_value_with_BYZANTIUM :
    Value.StructTuple "revm_precompile::PrecompileSpecId::BYZANTIUM" [] =
    φ BYZANTIUM.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_BYZANTIUM : of_value.

  Lemma of_value_with_ISTANBUL :
    Value.StructTuple "revm_precompile::PrecompileSpecId::ISTANBUL" [] =
    φ ISTANBUL.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_ISTANBUL : of_value.

  Lemma of_value_with_BERLIN :
    Value.StructTuple "revm_precompile::PrecompileSpecId::BERLIN" [] =
    φ BERLIN.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_BERLIN : of_value.

  Lemma of_value_with_CANCUN :
    Value.StructTuple "revm_precompile::PrecompileSpecId::CANCUN" [] =
    φ CANCUN.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CANCUN : of_value.

  Lemma of_value_with_PRAGUE :
    Value.StructTuple "revm_precompile::PrecompileSpecId::PRAGUE" [] =
    φ PRAGUE.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_PRAGUE : of_value.

  Lemma of_value_with_LATEST :
    Value.StructTuple "revm_precompile::PrecompileSpecId::LATEST" [] =
    φ LATEST.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_LATEST : of_value.

  Definition of_value_HOMESTEAD :
    OfValue.t (
      Value.StructTuple "revm_precompile::PrecompileSpecId::HOMESTEAD" []
    ).
  Proof. econstructor; apply of_value_with_HOMESTEAD; eassumption. Defined.
  Smpl Add simple apply of_value_HOMESTEAD : of_value.

  Definition of_value_BYZANTIUM :
    OfValue.t (
      Value.StructTuple "revm_precompile::PrecompileSpecId::BYZANTIUM" []
    ).
  Proof. econstructor; apply of_value_with_BYZANTIUM; eassumption. Defined.
  Smpl Add simple apply of_value_BYZANTIUM : of_value.

  Definition of_value_ISTANBUL :
    OfValue.t (
      Value.StructTuple "revm_precompile::PrecompileSpecId::ISTANBUL" []
    ).
  Proof. econstructor; apply of_value_with_ISTANBUL; eassumption. Defined.
  Smpl Add simple apply of_value_ISTANBUL : of_value.

  Definition of_value_BERLIN :
    OfValue.t (
      Value.StructTuple "revm_precompile::PrecompileSpecId::BERLIN" []
    ).
  Proof. econstructor; apply of_value_with_BERLIN; eassumption. Defined.
  Smpl Add simple apply of_value_BERLIN : of_value.

  Definition of_value_CANCUN :
    OfValue.t (
      Value.StructTuple "revm_precompile::PrecompileSpecId::CANCUN" []
    ).
  Proof. econstructor; apply of_value_with_CANCUN; eassumption. Defined.
  Smpl Add simple apply of_value_CANCUN : of_value.

  Definition of_value_PRAGUE :
    OfValue.t (
      Value.StructTuple "revm_precompile::PrecompileSpecId::PRAGUE" []
    ).
  Proof. econstructor; apply of_value_with_PRAGUE; eassumption. Defined.
  Smpl Add simple apply of_value_PRAGUE : of_value.

  Definition of_value_LATEST :
    OfValue.t (
      Value.StructTuple "revm_precompile::PrecompileSpecId::LATEST" []
    ).
  Proof. econstructor; apply of_value_with_LATEST; eassumption. Defined.
  Smpl Add simple apply of_value_LATEST : of_value.
End PrecompileSpecId.

Module SpecId.
  Inductive t : Set :=
  | FRONTIER
  | FRONTIER_THAWING
  | HOMESTEAD
  | DAO_FORK
  | TANGERINE
  | SPURIOUS_DRAGON
  | BYZANTIUM
  | CONSTANTINOPLE
  | PETERSBURG
  | ISTANBUL
  | MUIR_GLACIER
  | BERLIN
  | LONDON
  | ARROW_GLACIER
  | GRAY_GLACIER
  | MERGE
  | SHANGHAI
  | CANCUN
  | PRAGUE
  | OSAKA
  | LATEST
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_specification::hardfork::SpecId";
    φ x :=
      match x with
      | FRONTIER =>
        Value.StructTuple "revm_specification::hardfork::SpecId::FRONTIER" []
      | FRONTIER_THAWING =>
        Value.StructTuple "revm_specification::hardfork::SpecId::FRONTIER_THAWING" []
      | HOMESTEAD =>
        Value.StructTuple "revm_specification::hardfork::SpecId::HOMESTEAD" []
      | DAO_FORK =>
        Value.StructTuple "revm_specification::hardfork::SpecId::DAO_FORK" []
      | TANGERINE =>
        Value.StructTuple "revm_specification::hardfork::SpecId::TANGERINE" []
      | SPURIOUS_DRAGON =>
        Value.StructTuple "revm_specification::hardfork::SpecId::SPURIOUS_DRAGON" []
      | BYZANTIUM =>
        Value.StructTuple "revm_specification::hardfork::SpecId::BYZANTIUM" []
      | CONSTANTINOPLE =>
        Value.StructTuple "revm_specification::hardfork::SpecId::CONSTANTINOPLE" []
      | PETERSBURG =>
        Value.StructTuple "revm_specification::hardfork::SpecId::PETERSBURG" []
      | ISTANBUL =>
        Value.StructTuple "revm_specification::hardfork::SpecId::ISTANBUL" []
      | MUIR_GLACIER =>
        Value.StructTuple "revm_specification::hardfork::SpecId::MUIR_GLACIER" []
      | BERLIN =>
        Value.StructTuple "revm_specification::hardfork::SpecId::BERLIN" []
      | LONDON =>
        Value.StructTuple "revm_specification::hardfork::SpecId::LONDON" []
      | ARROW_GLACIER =>
        Value.StructTuple "revm_specification::hardfork::SpecId::ARROW_GLACIER" []
      | GRAY_GLACIER =>
        Value.StructTuple "revm_specification::hardfork::SpecId::GRAY_GLACIER" []
      | MERGE =>
        Value.StructTuple "revm_specification::hardfork::SpecId::MERGE" []
      | SHANGHAI =>
        Value.StructTuple "revm_specification::hardfork::SpecId::SHANGHAI" []
      | CANCUN =>
        Value.StructTuple "revm_specification::hardfork::SpecId::CANCUN" []
      | PRAGUE =>
        Value.StructTuple "revm_specification::hardfork::SpecId::PRAGUE" []
      | OSAKA =>
        Value.StructTuple "revm_specification::hardfork::SpecId::OSAKA" []
      | LATEST =>
        Value.StructTuple "revm_specification::hardfork::SpecId::LATEST" []
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_specification::hardfork::SpecId").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_FRONTIER :
    Value.StructTuple "revm_specification::hardfork::SpecId::FRONTIER" [] =
    φ FRONTIER.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_FRONTIER : of_value.

  Lemma of_value_with_FRONTIER_THAWING :
    Value.StructTuple "revm_specification::hardfork::SpecId::FRONTIER_THAWING" [] =
    φ FRONTIER_THAWING.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_FRONTIER_THAWING : of_value.

  Lemma of_value_with_HOMESTEAD :
    Value.StructTuple "revm_specification::hardfork::SpecId::HOMESTEAD" [] =
    φ HOMESTEAD.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_HOMESTEAD : of_value.

  Lemma of_value_with_DAO_FORK :
    Value.StructTuple "revm_specification::hardfork::SpecId::DAO_FORK" [] =
    φ DAO_FORK.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_DAO_FORK : of_value.

  Lemma of_value_with_TANGERINE :
    Value.StructTuple "revm_specification::hardfork::SpecId::TANGERINE" [] =
    φ TANGERINE.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_TANGERINE : of_value.

  Lemma of_value_with_SPURIOUS_DRAGON :
    Value.StructTuple "revm_specification::hardfork::SpecId::SPURIOUS_DRAGON" [] =
    φ SPURIOUS_DRAGON.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_SPURIOUS_DRAGON : of_value.

  Lemma of_value_with_BYZANTIUM :
    Value.StructTuple "revm_specification::hardfork::SpecId::BYZANTIUM" [] =
    φ BYZANTIUM.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_BYZANTIUM : of_value.

  Lemma of_value_with_CONSTANTINOPLE :
    Value.StructTuple "revm_specification::hardfork::SpecId::CONSTANTINOPLE" [] =
    φ CONSTANTINOPLE.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CONSTANTINOPLE : of_value.

  Lemma of_value_with_PETERSBURG :
    Value.StructTuple "revm_specification::hardfork::SpecId::PETERSBURG" [] =
    φ PETERSBURG.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_PETERSBURG : of_value.

  Lemma of_value_with_ISTANBUL :
    Value.StructTuple "revm_specification::hardfork::SpecId::ISTANBUL" [] =
    φ ISTANBUL.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_ISTANBUL : of_value.

  Lemma of_value_with_MUIR_GLACIER :
    Value.StructTuple "revm_specification::hardfork::SpecId::MUIR_GLACIER" [] =
    φ MUIR_GLACIER.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_MUIR_GLACIER : of_value.

  Lemma of_value_with_BERLIN :
    Value.StructTuple "revm_specification::hardfork::SpecId::BERLIN" [] =
    φ BERLIN.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_BERLIN : of_value.

  Lemma of_value_with_LONDON :
    Value.StructTuple "revm_specification::hardfork::SpecId::LONDON" [] =
    φ LONDON.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_LONDON : of_value.

  Lemma of_value_with_ARROW_GLACIER :
    Value.StructTuple "revm_specification::hardfork::SpecId::ARROW_GLACIER" [] =
    φ ARROW_GLACIER.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_ARROW_GLACIER : of_value.

  Lemma of_value_with_GRAY_GLACIER :
    Value.StructTuple "revm_specification::hardfork::SpecId::GRAY_GLACIER" [] =
    φ GRAY_GLACIER.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_GRAY_GLACIER : of_value.

  Lemma of_value_with_MERGE :
    Value.StructTuple "revm_specification::hardfork::SpecId::MERGE" [] =
    φ MERGE.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_MERGE : of_value.

  Lemma of_value_with_SHANGHAI :
    Value.StructTuple "revm_specification::hardfork::SpecId::SHANGHAI" [] =
    φ SHANGHAI.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_SHANGHAI : of_value.

  Lemma of_value_with_CANCUN :
    Value.StructTuple "revm_specification::hardfork::SpecId::CANCUN" [] =
    φ CANCUN.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_CANCUN : of_value.

  Lemma of_value_with_PRAGUE :
    Value.StructTuple "revm_specification::hardfork::SpecId::PRAGUE" [] =
    φ PRAGUE.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_PRAGUE : of_value.

  Lemma of_value_with_OSAKA :
    Value.StructTuple "revm_specification::hardfork::SpecId::OSAKA" [] =
    φ OSAKA.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_OSAKA : of_value.

  Lemma of_value_with_LATEST :
    Value.StructTuple "revm_specification::hardfork::SpecId::LATEST" [] =
    φ LATEST.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_LATEST : of_value.

  Definition of_value_FRONTIER :
    OfValue.t (
      Value.StructTuple "revm_specification::hardfork::SpecId::FRONTIER" []
    ).
  Proof. econstructor; apply of_value_with_FRONTIER; eassumption. Defined.
  Smpl Add simple apply of_value_FRONTIER : of_value.

  Definition of_value_FRONTIER_THAWING :
    OfValue.t (
      Value.StructTuple "revm_specification::hardfork::SpecId::FRONTIER_THAWING" []
    ).
  Proof. econstructor; apply of_value_with_FRONTIER_THAWING; eassumption. Defined.
  Smpl Add simple apply of_value_FRONTIER_THAWING : of_value.

  Definition of_value_HOMESTEAD :
    OfValue.t (
      Value.StructTuple "revm_specification::hardfork::SpecId::HOMESTEAD" []
    ).
  Proof. econstructor; apply of_value_with_HOMESTEAD; eassumption. Defined.
  Smpl Add simple apply of_value_HOMESTEAD : of_value.

  Definition of_value_DAO_FORK :
    OfValue.t (
      Value.StructTuple "revm_specification::hardfork::SpecId::DAO_FORK" []
    ).
  Proof. econstructor; apply of_value_with_DAO_FORK; eassumption. Defined.
  Smpl Add simple apply of_value_DAO_FORK : of_value.

  Definition of_value_TANGERINE :
    OfValue.t (
      Value.StructTuple "revm_specification::hardfork::SpecId::TANGERINE" []
    ).
  Proof. econstructor; apply of_value_with_TANGERINE; eassumption. Defined.
  Smpl Add simple apply of_value_TANGERINE : of_value.

  Definition of_value_SPURIOUS_DRAGON :
    OfValue.t (
      Value.StructTuple "revm_specification::hardfork::SpecId::SPURIOUS_DRAGON" []
    ).
  Proof. econstructor; apply of_value_with_SPURIOUS_DRAGON; eassumption. Defined.
  Smpl Add simple apply of_value_SPURIOUS_DRAGON : of_value.

  Definition of_value_BYZANTIUM :
    OfValue.t (
      Value.StructTuple "revm_specification::hardfork::SpecId::BYZANTIUM" []
    ).
  Proof. econstructor; apply of_value_with_BYZANTIUM; eassumption. Defined.
  Smpl Add simple apply of_value_BYZANTIUM : of_value.

  Definition of_value_CONSTANTINOPLE :
    OfValue.t (
      Value.StructTuple "revm_specification::hardfork::SpecId::CONSTANTINOPLE" []
    ).
  Proof. econstructor; apply of_value_with_CONSTANTINOPLE; eassumption. Defined.
  Smpl Add simple apply of_value_CONSTANTINOPLE : of_value.

  Definition of_value_PETERSBURG :
    OfValue.t (
      Value.StructTuple "revm_specification::hardfork::SpecId::PETERSBURG" []
    ).
  Proof. econstructor; apply of_value_with_PETERSBURG; eassumption. Defined.
  Smpl Add simple apply of_value_PETERSBURG : of_value.

  Definition of_value_ISTANBUL :
    OfValue.t (
      Value.StructTuple "revm_specification::hardfork::SpecId::ISTANBUL" []
    ).
  Proof. econstructor; apply of_value_with_ISTANBUL; eassumption. Defined.
  Smpl Add simple apply of_value_ISTANBUL : of_value.

  Definition of_value_MUIR_GLACIER :
    OfValue.t (
      Value.StructTuple "revm_specification::hardfork::SpecId::MUIR_GLACIER" []
    ).
  Proof. econstructor; apply of_value_with_MUIR_GLACIER; eassumption. Defined.
  Smpl Add simple apply of_value_MUIR_GLACIER : of_value.

  Definition of_value_BERLIN :
    OfValue.t (
      Value.StructTuple "revm_specification::hardfork::SpecId::BERLIN" []
    ).
  Proof. econstructor; apply of_value_with_BERLIN; eassumption. Defined.
  Smpl Add simple apply of_value_BERLIN : of_value.

  Definition of_value_LONDON :
    OfValue.t (
      Value.StructTuple "revm_specification::hardfork::SpecId::LONDON" []
    ).
  Proof. econstructor; apply of_value_with_LONDON; eassumption. Defined.
  Smpl Add simple apply of_value_LONDON : of_value.

  Definition of_value_ARROW_GLACIER :
    OfValue.t (
      Value.StructTuple "revm_specification::hardfork::SpecId::ARROW_GLACIER" []
    ).
  Proof. econstructor; apply of_value_with_ARROW_GLACIER; eassumption. Defined.
  Smpl Add simple apply of_value_ARROW_GLACIER : of_value.

  Definition of_value_GRAY_GLACIER :
    OfValue.t (
      Value.StructTuple "revm_specification::hardfork::SpecId::GRAY_GLACIER" []
    ).
  Proof. econstructor; apply of_value_with_GRAY_GLACIER; eassumption. Defined.
  Smpl Add simple apply of_value_GRAY_GLACIER : of_value.

  Definition of_value_MERGE :
    OfValue.t (
      Value.StructTuple "revm_specification::hardfork::SpecId::MERGE" []
    ).
  Proof. econstructor; apply of_value_with_MERGE; eassumption. Defined.
  Smpl Add simple apply of_value_MERGE : of_value.

  Definition of_value_SHANGHAI :
    OfValue.t (
      Value.StructTuple "revm_specification::hardfork::SpecId::SHANGHAI" []
    ).
  Proof. econstructor; apply of_value_with_SHANGHAI; eassumption. Defined.
  Smpl Add simple apply of_value_SHANGHAI : of_value.

  Definition of_value_CANCUN :
    OfValue.t (
      Value.StructTuple "revm_specification::hardfork::SpecId::CANCUN" []
    ).
  Proof. econstructor; apply of_value_with_CANCUN; eassumption. Defined.
  Smpl Add simple apply of_value_CANCUN : of_value.

  Definition of_value_PRAGUE :
    OfValue.t (
      Value.StructTuple "revm_specification::hardfork::SpecId::PRAGUE" []
    ).
  Proof. econstructor; apply of_value_with_PRAGUE; eassumption. Defined.
  Smpl Add simple apply of_value_PRAGUE : of_value.

  Definition of_value_OSAKA :
    OfValue.t (
      Value.StructTuple "revm_specification::hardfork::SpecId::OSAKA" []
    ).
  Proof. econstructor; apply of_value_with_OSAKA; eassumption. Defined.
  Smpl Add simple apply of_value_OSAKA : of_value.

  Definition of_value_LATEST :
    OfValue.t (
      Value.StructTuple "revm_specification::hardfork::SpecId::LATEST" []
    ).
  Proof. econstructor; apply of_value_with_LATEST; eassumption. Defined.
  Smpl Add simple apply of_value_LATEST : of_value.
End SpecId.

Module AuthorizationList.
  Inductive t : Set :=
  | Signed
    (_ : alloc.links.vec.Vec.t alloy_eip7702.links.auth_list.SignedAuthorization.t alloc.links.alloc.Global.t)
  | Recovered
    (_ : alloc.links.vec.Vec.t revm_specification.eip7702.links.recovered_authorization.RecoveredAuthorization.t alloc.links.alloc.Global.t)
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_specification::eip7702::authorization_list::AuthorizationList";
    φ x :=
      match x with
      | Signed γ0 =>
        Value.StructTuple "revm_specification::eip7702::authorization_list::AuthorizationList::Signed" [
          φ γ0
        ]
      | Recovered γ0 =>
        Value.StructTuple "revm_specification::eip7702::authorization_list::AuthorizationList::Recovered" [
          φ γ0
        ]
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_specification::eip7702::authorization_list::AuthorizationList").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_Signed
    (γ0 : alloc.links.vec.Vec.t alloy_eip7702.links.auth_list.SignedAuthorization.t alloc.links.alloc.Global.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_specification::eip7702::authorization_list::AuthorizationList::Signed" [
      γ0
    ] =
    φ (Signed γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Signed : of_value.

  Lemma of_value_with_Recovered
    (γ0 : alloc.links.vec.Vec.t revm_specification.eip7702.links.recovered_authorization.RecoveredAuthorization.t alloc.links.alloc.Global.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    Value.StructTuple "revm_specification::eip7702::authorization_list::AuthorizationList::Recovered" [
      γ0
    ] =
    φ (Recovered γ0).
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Recovered : of_value.

  Definition of_value_Signed
    (γ0 : alloc.links.vec.Vec.t alloy_eip7702.links.auth_list.SignedAuthorization.t alloc.links.alloc.Global.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_specification::eip7702::authorization_list::AuthorizationList::Signed" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Signed; eassumption. Defined.
  Smpl Add simple apply of_value_Signed : of_value.

  Definition of_value_Recovered
    (γ0 : alloc.links.vec.Vec.t revm_specification.eip7702.links.recovered_authorization.RecoveredAuthorization.t alloc.links.alloc.Global.t) (γ0' : Value.t) :
    γ0' = φ γ0 ->
    OfValue.t (
      Value.StructTuple "revm_specification::eip7702::authorization_list::AuthorizationList::Recovered" [
        γ0
      ]
    ).
  Proof. econstructor; apply of_value_with_Recovered; eassumption. Defined.
  Smpl Add simple apply of_value_Recovered : of_value.
End AuthorizationList.

Module InvalidAuthorization.
  Inductive t : Set :=
  | InvalidChainId
  | InvalidYParity
  | Eip2InvalidSValue
  .

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_specification::eip7702::authorization_list::InvalidAuthorization";
    φ x :=
      match x with
      | InvalidChainId =>
        Value.StructTuple "revm_specification::eip7702::authorization_list::InvalidAuthorization::InvalidChainId" []
      | InvalidYParity =>
        Value.StructTuple "revm_specification::eip7702::authorization_list::InvalidAuthorization::InvalidYParity" []
      | Eip2InvalidSValue =>
        Value.StructTuple "revm_specification::eip7702::authorization_list::InvalidAuthorization::Eip2InvalidSValue" []
      end
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_specification::eip7702::authorization_list::InvalidAuthorization").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add simple apply of_ty : of_ty.

  Lemma of_value_with_InvalidChainId :
    Value.StructTuple "revm_specification::eip7702::authorization_list::InvalidAuthorization::InvalidChainId" [] =
    φ InvalidChainId.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InvalidChainId : of_value.

  Lemma of_value_with_InvalidYParity :
    Value.StructTuple "revm_specification::eip7702::authorization_list::InvalidAuthorization::InvalidYParity" [] =
    φ InvalidYParity.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_InvalidYParity : of_value.

  Lemma of_value_with_Eip2InvalidSValue :
    Value.StructTuple "revm_specification::eip7702::authorization_list::InvalidAuthorization::Eip2InvalidSValue" [] =
    φ Eip2InvalidSValue.
  Proof. now intros; subst. Qed.
  Smpl Add simple apply of_value_with_Eip2InvalidSValue : of_value.

  Definition of_value_InvalidChainId :
    OfValue.t (
      Value.StructTuple "revm_specification::eip7702::authorization_list::InvalidAuthorization::InvalidChainId" []
    ).
  Proof. econstructor; apply of_value_with_InvalidChainId; eassumption. Defined.
  Smpl Add simple apply of_value_InvalidChainId : of_value.

  Definition of_value_InvalidYParity :
    OfValue.t (
      Value.StructTuple "revm_specification::eip7702::authorization_list::InvalidAuthorization::InvalidYParity" []
    ).
  Proof. econstructor; apply of_value_with_InvalidYParity; eassumption. Defined.
  Smpl Add simple apply of_value_InvalidYParity : of_value.

  Definition of_value_Eip2InvalidSValue :
    OfValue.t (
      Value.StructTuple "revm_specification::eip7702::authorization_list::InvalidAuthorization::Eip2InvalidSValue" []
    ).
  Proof. econstructor; apply of_value_with_Eip2InvalidSValue; eassumption. Defined.
  Smpl Add simple apply of_value_Eip2InvalidSValue : of_value.
End InvalidAuthorization.

Module RecoveredAuthorization.
  Record t : Set := {
    inner: alloy_eip7702.links.auth_list.SignedAuthorization.t;
    authority: core.links.option.Option.t alloy_primitives.bits.links.address.Address.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_specification::eip7702::recovered_authorization::RecoveredAuthorization";
    φ '(Build_t inner authority) :=
      Value.StructRecord "revm_specification::eip7702::recovered_authorization::RecoveredAuthorization" [
        ("inner", φ inner);
        ("authority", φ authority)
      ]
  }.
End RecoveredAuthorization.
