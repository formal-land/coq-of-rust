Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import alloc.links.alloc.
Require Import core.links.result.
Require Import alloy_primitives.bytes.links.mod.
Require Import revm.revm_bytecode.eof.links.body_EofBody.
Require Import revm.revm_bytecode.eof.links.header.
Require Import revm.revm_bytecode.eof.

Module Eof.
  Record t : Set := {
    header: revm_bytecode.eof.links.header.EofHeader.t;
    body: EofBody.t;
    raw: Bytes.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_bytecode::eof::Eof";
    φ '(Build_t header body raw) :=
      Value.StructRecord "revm_bytecode::eof::Eof" [] [] [
        ("header", φ header);
        ("body", φ body);
        ("raw", φ raw)
      ]
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_bytecode::eof::Eof").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.

  Lemma of_value_with header header' body body' raw raw' :
    header' = φ header ->
    body' = φ body ->
    raw' = φ raw ->
    Value.StructRecord "revm_bytecode::eof::Eof" [] [] [
      ("header", header');
      ("body", body');
      ("raw", raw')
    ] = φ (Build_t header body raw).
  Proof. now intros; subst. Qed.
  Smpl Add apply of_value_with : of_value.

  Definition of_value
      (header : revm_bytecode.eof.links.header.EofHeader.t) header'
      (body : EofBody.t) body'
      (raw : Bytes.t) raw' :
    header' = φ header ->
    body' = φ body ->
    raw' = φ raw ->
    OfValue.t (Value.StructRecord "revm_bytecode::eof::Eof" [] [] [
      ("header", header');
      ("body", body');
      ("raw", raw')
    ]).
  Proof. econstructor; apply of_value_with; eassumption. Defined.
  Smpl Add apply of_value : of_value.

  Module SubPointer.
    Definition get_header : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_bytecode::eof::Eof" "header") :=
    {|
      SubPointer.Runner.projection x := Some x.(header);
      SubPointer.Runner.injection x y := Some (x <| header := y |>);
    |}.

    Lemma get_header_is_valid :
      SubPointer.Runner.Valid.t get_header.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_header_is_valid : run_sub_pointer.

    Definition get_body : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_bytecode::eof::Eof" "body") :=
    {|
      SubPointer.Runner.projection x := Some x.(body);
      SubPointer.Runner.injection x y := Some (x <| body := y |>);
    |}.

    Lemma get_body_is_valid :
      SubPointer.Runner.Valid.t get_body.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_body_is_valid : run_sub_pointer.

    Definition get_raw : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_bytecode::eof::Eof" "raw") :=
    {|
      SubPointer.Runner.projection x := Some x.(raw);
      SubPointer.Runner.injection x y := Some (x <| raw := y |>);
    |}.

    Lemma get_raw_is_valid :
      SubPointer.Runner.Valid.t get_raw.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_raw_is_valid : run_sub_pointer.
  End SubPointer.
End Eof.

Module EofDecodeError.
  Inductive t : Set :=
  | MissingInput : t
  | MissingBodyWithoutData : t
  | DanglingData : t
  | InvalidCodeInfo : t
  | InvalidCodeInfoSize : t
  | InvalidEOFMagicNumber : t
  | InvalidEOFVersion : t
  | InvalidTypesKind : t
  | InvalidCodeKind : t
  | InvalidTerminalByte : t
  | InvalidDataKind : t
  | InvalidKindAfterCode : t
  | MismatchCodeAndInfoSize : t
  | NonSizes : t
  | ShortInputForSizes : t
  | ZeroSize : t
  | TooManyCodeSections : t
  | ZeroCodeSections : t
  | TooManyContainerSections : t
  | InvalidEOFSize : t.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_bytecode::eof::EofDecodeError";
    φ x := 
      match x with
      | MissingInput => Value.StructTuple "revm_bytecode::eof::EofDecodeError::MissingInput" [] [] []
      | MissingBodyWithoutData => Value.StructTuple "revm_bytecode::eof::EofDecodeError::MissingBodyWithoutData" [] [] []
      | DanglingData => Value.StructTuple "revm_bytecode::eof::EofDecodeError::DanglingData" [] [] []
      | InvalidCodeInfo => Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidCodeInfo" [] [] []
      | InvalidCodeInfoSize => Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidCodeInfoSize" [] [] []
      | InvalidEOFMagicNumber => Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidEOFMagicNumber" [] [] []
      | InvalidEOFVersion => Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidEOFVersion" [] [] []
      | InvalidTypesKind => Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidTypesKind" [] [] []
      | InvalidCodeKind => Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidCodeKind" [] [] []
      | InvalidTerminalByte => Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidTerminalByte" [] [] []
      | InvalidDataKind => Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidDataKind" [] [] []
      | InvalidKindAfterCode => Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidKindAfterCode" [] [] []
      | MismatchCodeAndInfoSize => Value.StructTuple "revm_bytecode::eof::EofDecodeError::MismatchCodeAndInfoSize" [] [] []
      | NonSizes => Value.StructTuple "revm_bytecode::eof::EofDecodeError::NonSizes" [] [] []
      | ShortInputForSizes => Value.StructTuple "revm_bytecode::eof::EofDecodeError::ShortInputForSizes" [] [] []
      | ZeroSize => Value.StructTuple "revm_bytecode::eof::EofDecodeError::ZeroSize" [] [] []
      | TooManyCodeSections => Value.StructTuple "revm_bytecode::eof::EofDecodeError::TooManyCodeSections" [] [] []
      | ZeroCodeSections => Value.StructTuple "revm_bytecode::eof::EofDecodeError::ZeroCodeSections" [] [] []
      | TooManyContainerSections => Value.StructTuple "revm_bytecode::eof::EofDecodeError::TooManyContainerSections" [] [] []
      | InvalidEOFSize => Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidEOFSize" [] [] []
      end;
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_bytecode::eof::EofDecodeError").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.
End EofDecodeError.

Module Impl_Eof.
  Definition Self : Set :=
    Eof.t.

  (* pub fn decode(raw: Bytes) -> Result<Self, EofDecodeError> *)
  Instance run_decode (raw : Bytes.t) :
    Run.Trait eof.Impl_revm_bytecode_eof_Eof.decode [] [] [φ raw] (Result.t Self EofDecodeError.t).
  Proof.
    constructor.
    run_symbolic.
  Admitted.
End Impl_Eof.
Export Impl_Eof.
