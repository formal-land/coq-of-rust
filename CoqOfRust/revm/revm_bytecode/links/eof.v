Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require alloc.links.alloc.
Require Import revm.links.dependencies.
Require Import revm.revm_bytecode.eof.links.body_EofBody.
Require revm.revm_bytecode.eof.links.header.

Module Eof.
  Record t : Set := {
    header: revm_bytecode.eof.links.header.EofHeader.t;
    body: EofBody.t;
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
    Φ := Ty.apply (Ty.path "revm_bytecode::eof::EofDecodeError") [] [];
    φ x := 
      match x with
      | MissingInput => Value.StructTuple "revm_bytecode::eof::EofDecodeError::MissingInput" []
      | MissingBodyWithoutData => Value.StructTuple "revm_bytecode::eof::EofDecodeError::MissingBodyWithoutData" []
      | DanglingData => Value.StructTuple "revm_bytecode::eof::EofDecodeError::DanglingData" []
      | InvalidCodeInfo => Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidCodeInfo" []
      | InvalidCodeInfoSize => Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidCodeInfoSize" []
      | InvalidEOFMagicNumber => Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidEOFMagicNumber" []
      | InvalidEOFVersion => Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidEOFVersion" []
      | InvalidTypesKind => Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidTypesKind" []
      | InvalidCodeKind => Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidCodeKind" []
      | InvalidTerminalByte => Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidTerminalByte" []
      | InvalidDataKind => Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidDataKind" []
      | InvalidKindAfterCode => Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidKindAfterCode" []
      | MismatchCodeAndInfoSize => Value.StructTuple "revm_bytecode::eof::EofDecodeError::MismatchCodeAndInfoSize" []
      | NonSizes => Value.StructTuple "revm_bytecode::eof::EofDecodeError::NonSizes" []
      | ShortInputForSizes => Value.StructTuple "revm_bytecode::eof::EofDecodeError::ShortInputForSizes" []
      | ZeroSize => Value.StructTuple "revm_bytecode::eof::EofDecodeError::ZeroSize" []
      | TooManyCodeSections => Value.StructTuple "revm_bytecode::eof::EofDecodeError::TooManyCodeSections" []
      | ZeroCodeSections => Value.StructTuple "revm_bytecode::eof::EofDecodeError::ZeroCodeSections" []
      | TooManyContainerSections => Value.StructTuple "revm_bytecode::eof::EofDecodeError::TooManyContainerSections" []
      | InvalidEOFSize => Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidEOFSize" []
      end;
  }.
End EofDecodeError.
