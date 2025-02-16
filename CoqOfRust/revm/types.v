(* Generated file. Do not edit. *)
Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require Import revm.links.dependencies.

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
      | InvalidLength  =>
        Value.StructTuple "revm_bytecode::eip7702::Eip7702DecodeError::InvalidLength" []
      | InvalidMagic  =>
        Value.StructTuple "revm_bytecode::eip7702::Eip7702DecodeError::InvalidMagic" []
      | UnsupportedVersion  =>
        Value.StructTuple "revm_bytecode::eip7702::Eip7702DecodeError::UnsupportedVersion" []
      end
  }.
End Eip7702DecodeError.

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
End Bytecode.

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
      | MissingInput  =>
        Value.StructTuple "revm_bytecode::eof::EofDecodeError::MissingInput" []
      | MissingBodyWithoutData  =>
        Value.StructTuple "revm_bytecode::eof::EofDecodeError::MissingBodyWithoutData" []
      | DanglingData  =>
        Value.StructTuple "revm_bytecode::eof::EofDecodeError::DanglingData" []
      | InvalidTypesSection  =>
        Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidTypesSection" []
      | InvalidTypesSectionSize  =>
        Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidTypesSectionSize" []
      | InvalidEOFMagicNumber  =>
        Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidEOFMagicNumber" []
      | InvalidEOFVersion  =>
        Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidEOFVersion" []
      | InvalidTypesKind  =>
        Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidTypesKind" []
      | InvalidCodeKind  =>
        Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidCodeKind" []
      | InvalidTerminalByte  =>
        Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidTerminalByte" []
      | InvalidDataKind  =>
        Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidDataKind" []
      | InvalidKindAfterCode  =>
        Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidKindAfterCode" []
      | MismatchCodeAndTypesSize  =>
        Value.StructTuple "revm_bytecode::eof::EofDecodeError::MismatchCodeAndTypesSize" []
      | NonSizes  =>
        Value.StructTuple "revm_bytecode::eof::EofDecodeError::NonSizes" []
      | ShortInputForSizes  =>
        Value.StructTuple "revm_bytecode::eof::EofDecodeError::ShortInputForSizes" []
      | ZeroSize  =>
        Value.StructTuple "revm_bytecode::eof::EofDecodeError::ZeroSize" []
      | TooManyCodeSections  =>
        Value.StructTuple "revm_bytecode::eof::EofDecodeError::TooManyCodeSections" []
      | ZeroCodeSections  =>
        Value.StructTuple "revm_bytecode::eof::EofDecodeError::ZeroCodeSections" []
      | TooManyContainerSections  =>
        Value.StructTuple "revm_bytecode::eof::EofDecodeError::TooManyContainerSections" []
      | InvalidEOFSize  =>
        Value.StructTuple "revm_bytecode::eof::EofDecodeError::InvalidEOFSize" []
      end
  }.
End EofDecodeError.

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
End BytecodeDecodeError.

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
      | FalsePositive  =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::FalsePositive" []
      | UnknownOpcode  =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::UnknownOpcode" []
      | OpcodeDisabled  =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::OpcodeDisabled" []
      | InstructionNotForwardAccessed  =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::InstructionNotForwardAccessed" []
      | MissingImmediateBytes  =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::MissingImmediateBytes" []
      | MissingRJUMPVImmediateBytes  =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::MissingRJUMPVImmediateBytes" []
      | JumpToImmediateBytes  =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::JumpToImmediateBytes" []
      | BackwardJumpToImmediateBytes  =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::BackwardJumpToImmediateBytes" []
      | RJUMPVZeroMaxIndex  =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::RJUMPVZeroMaxIndex" []
      | JumpZeroOffset  =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::JumpZeroOffset" []
      | EOFCREATEInvalidIndex  =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::EOFCREATEInvalidIndex" []
      | CodeSectionOutOfBounds  =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::CodeSectionOutOfBounds" []
      | CALLFNonReturningFunction  =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::CALLFNonReturningFunction" []
      | StackOverflow  =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::StackOverflow" []
      | JUMPFEnoughOutputs  =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::JUMPFEnoughOutputs" []
      | JUMPFStackHigherThanOutputs  =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::JUMPFStackHigherThanOutputs" []
      | DataLoadOutOfBounds  =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::DataLoadOutOfBounds" []
      | RETFBiggestStackNumMoreThenOutputs  =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::RETFBiggestStackNumMoreThenOutputs" []
      | StackUnderflow  =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::StackUnderflow" []
      | TypesStackUnderflow  =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::TypesStackUnderflow" []
      | JumpUnderflow  =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::JumpUnderflow" []
      | JumpOverflow  =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::JumpOverflow" []
      | BackwardJumpBiggestNumMismatch  =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::BackwardJumpBiggestNumMismatch" []
      | BackwardJumpSmallestNumMismatch  =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::BackwardJumpSmallestNumMismatch" []
      | LastInstructionNotTerminating  =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::LastInstructionNotTerminating" []
      | CodeSectionNotAccessed  =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::CodeSectionNotAccessed" []
      | InvalidTypesSection  =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::InvalidTypesSection" []
      | InvalidFirstTypesSection  =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::InvalidFirstTypesSection" []
      | MaxStackMismatch  =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::MaxStackMismatch" []
      | NoCodeSections  =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::NoCodeSections" []
      | SubContainerCalledInTwoModes  =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::SubContainerCalledInTwoModes" []
      | SubContainerNotAccessed  =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::SubContainerNotAccessed" []
      | DataNotFilled  =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::DataNotFilled" []
      | NonReturningSectionIsReturning  =>
        Value.StructTuple "revm_bytecode::eof::verification::EofValidationError::NonReturningSectionIsReturning" []
      end
  }.
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
      | ReturnContract  =>
        Value.StructTuple "revm_bytecode::eof::verification::CodeType::ReturnContract" []
      | ReturnOrStop  =>
        Value.StructTuple "revm_bytecode::eof::verification::CodeType::ReturnOrStop" []
      end
  }.
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
      | Raw  =>
        Value.StructTuple "revm_context_interface::cfg::AnalysisKind::Raw" []
      | Analyse  =>
        Value.StructTuple "revm_context_interface::cfg::AnalysisKind::Analyse" []
      end
  }.
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
      | Create  =>
        Value.StructTuple "revm_context_interface::cfg::CreateScheme::Create" []
      | Create2 salt =>
        Value.StructRecord "revm_context_interface::cfg::CreateScheme::Create2" [
          ("salt", φ salt)
        ]
      end
  }.
End CreateScheme.

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
      | PriorityFeeGreaterThanMaxFee  =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::PriorityFeeGreaterThanMaxFee" []
      | GasPriceLessThanBasefee  =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::GasPriceLessThanBasefee" []
      | CallerGasLimitMoreThanBlock  =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::CallerGasLimitMoreThanBlock" []
      | CallGasCostMoreThanGasLimit  =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::CallGasCostMoreThanGasLimit" []
      | RejectCallerWithCode  =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::RejectCallerWithCode" []
      | LackOfFundForMaxFee fee balance =>
        Value.StructRecord "revm_context_interface::result::InvalidTransaction::LackOfFundForMaxFee" [
          ("fee", φ fee);
          ("balance", φ balance)
        ]
      | OverflowPaymentInTransaction  =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::OverflowPaymentInTransaction" []
      | NonceOverflowInTransaction  =>
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
      | CreateInitCodeSizeLimit  =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::CreateInitCodeSizeLimit" []
      | InvalidChainId  =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::InvalidChainId" []
      | AccessListNotSupported  =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::AccessListNotSupported" []
      | MaxFeePerBlobGasNotSupported  =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::MaxFeePerBlobGasNotSupported" []
      | BlobVersionedHashesNotSupported  =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::BlobVersionedHashesNotSupported" []
      | BlobGasPriceGreaterThanMax  =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::BlobGasPriceGreaterThanMax" []
      | EmptyBlobs  =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::EmptyBlobs" []
      | BlobCreateTransaction  =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::BlobCreateTransaction" []
      | TooManyBlobs max have =>
        Value.StructRecord "revm_context_interface::result::InvalidTransaction::TooManyBlobs" [
          ("max", φ max);
          ("have", φ have)
        ]
      | BlobVersionNotSupported  =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::BlobVersionNotSupported" []
      | EofCrateShouldHaveToAddress  =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::EofCrateShouldHaveToAddress" []
      | AuthorizationListNotSupported  =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::AuthorizationListNotSupported" []
      | AuthorizationListInvalidFields  =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::AuthorizationListInvalidFields" []
      | EmptyAuthorizationList  =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::EmptyAuthorizationList" []
      | InvalidAuthorizationList γ0 =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::InvalidAuthorizationList" [
          φ γ0
        ]
      | Eip2930NotSupported  =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::Eip2930NotSupported" []
      | Eip1559NotSupported  =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::Eip1559NotSupported" []
      | Eip4844NotSupported  =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::Eip4844NotSupported" []
      | Eip7702NotSupported  =>
        Value.StructTuple "revm_context_interface::result::InvalidTransaction::Eip7702NotSupported" []
      end
  }.
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
      | PrevrandaoNotSet  =>
        Value.StructTuple "revm_context_interface::result::InvalidHeader::PrevrandaoNotSet" []
      | ExcessBlobGasNotSet  =>
        Value.StructTuple "revm_context_interface::result::InvalidHeader::ExcessBlobGasNotSet" []
      end
  }.
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
      | Stop  =>
        Value.StructTuple "revm_context_interface::result::SuccessReason::Stop" []
      | Return  =>
        Value.StructTuple "revm_context_interface::result::SuccessReason::Return" []
      | SelfDestruct  =>
        Value.StructTuple "revm_context_interface::result::SuccessReason::SelfDestruct" []
      | EofReturnContract  =>
        Value.StructTuple "revm_context_interface::result::SuccessReason::EofReturnContract" []
      end
  }.
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
      | OpcodeNotFound  =>
        Value.StructTuple "revm_context_interface::result::HaltReason::OpcodeNotFound" []
      | InvalidFEOpcode  =>
        Value.StructTuple "revm_context_interface::result::HaltReason::InvalidFEOpcode" []
      | InvalidJump  =>
        Value.StructTuple "revm_context_interface::result::HaltReason::InvalidJump" []
      | NotActivated  =>
        Value.StructTuple "revm_context_interface::result::HaltReason::NotActivated" []
      | StackUnderflow  =>
        Value.StructTuple "revm_context_interface::result::HaltReason::StackUnderflow" []
      | StackOverflow  =>
        Value.StructTuple "revm_context_interface::result::HaltReason::StackOverflow" []
      | OutOfOffset  =>
        Value.StructTuple "revm_context_interface::result::HaltReason::OutOfOffset" []
      | CreateCollision  =>
        Value.StructTuple "revm_context_interface::result::HaltReason::CreateCollision" []
      | PrecompileError  =>
        Value.StructTuple "revm_context_interface::result::HaltReason::PrecompileError" []
      | NonceOverflow  =>
        Value.StructTuple "revm_context_interface::result::HaltReason::NonceOverflow" []
      | CreateContractSizeLimit  =>
        Value.StructTuple "revm_context_interface::result::HaltReason::CreateContractSizeLimit" []
      | CreateContractStartingWithEF  =>
        Value.StructTuple "revm_context_interface::result::HaltReason::CreateContractStartingWithEF" []
      | CreateInitCodeSizeLimit  =>
        Value.StructTuple "revm_context_interface::result::HaltReason::CreateInitCodeSizeLimit" []
      | OverflowPayment  =>
        Value.StructTuple "revm_context_interface::result::HaltReason::OverflowPayment" []
      | StateChangeDuringStaticCall  =>
        Value.StructTuple "revm_context_interface::result::HaltReason::StateChangeDuringStaticCall" []
      | CallNotAllowedInsideStatic  =>
        Value.StructTuple "revm_context_interface::result::HaltReason::CallNotAllowedInsideStatic" []
      | OutOfFunds  =>
        Value.StructTuple "revm_context_interface::result::HaltReason::OutOfFunds" []
      | CallTooDeep  =>
        Value.StructTuple "revm_context_interface::result::HaltReason::CallTooDeep" []
      | EofAuxDataOverflow  =>
        Value.StructTuple "revm_context_interface::result::HaltReason::EofAuxDataOverflow" []
      | EofAuxDataTooSmall  =>
        Value.StructTuple "revm_context_interface::result::HaltReason::EofAuxDataTooSmall" []
      | SubRoutineStackOverflow  =>
        Value.StructTuple "revm_context_interface::result::HaltReason::SubRoutineStackOverflow" []
      | InvalidEXTCALLTarget  =>
        Value.StructTuple "revm_context_interface::result::HaltReason::InvalidEXTCALLTarget" []
      end
  }.
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
      | Basic  =>
        Value.StructTuple "revm_context_interface::result::OutOfGasError::Basic" []
      | MemoryLimit  =>
        Value.StructTuple "revm_context_interface::result::OutOfGasError::MemoryLimit" []
      | Memory  =>
        Value.StructTuple "revm_context_interface::result::OutOfGasError::Memory" []
      | Precompile  =>
        Value.StructTuple "revm_context_interface::result::OutOfGasError::Precompile" []
      | InvalidOperand  =>
        Value.StructTuple "revm_context_interface::result::OutOfGasError::InvalidOperand" []
      | ReentrancySentry  =>
        Value.StructTuple "revm_context_interface::result::OutOfGasError::ReentrancySentry" []
      end
  }.
End OutOfGasError.

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
      | OutOfFunds  =>
        Value.StructTuple "revm_context_interface::journaled_state::TransferError::OutOfFunds" []
      | OverflowPayment  =>
        Value.StructTuple "revm_context_interface::journaled_state::TransferError::OverflowPayment" []
      | CreateCollision  =>
        Value.StructTuple "revm_context_interface::journaled_state::TransferError::CreateCollision" []
      end
  }.
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
      | Legacy  =>
        Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Legacy" []
      | Eip2930  =>
        Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip2930" []
      | Eip1559  =>
        Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip1559" []
      | Eip4844  =>
        Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip4844" []
      | Eip7702  =>
        Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip7702" []
      | Custom  =>
        Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Custom" []
      end
  }.
End TransactionType.

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
End InstructionTables.

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
      | None  =>
        Value.StructTuple "revm_interpreter::interpreter_action::InterpreterAction::None" []
      end
  }.
End InterpreterAction.

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
      | Continue  =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::Continue" []
      | Stop  =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::Stop" []
      | Return  =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::Return" []
      | SelfDestruct  =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::SelfDestruct" []
      | ReturnContract  =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::ReturnContract" []
      | Revert  =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::Revert" []
      | CallTooDeep  =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CallTooDeep" []
      | OutOfFunds  =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OutOfFunds" []
      | CreateInitCodeStartingEF00  =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateInitCodeStartingEF00" []
      | InvalidEOFInitCode  =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidEOFInitCode" []
      | InvalidExtDelegateCallTarget  =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidExtDelegateCallTarget" []
      | CallOrCreate  =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CallOrCreate" []
      | OutOfGas  =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OutOfGas" []
      | MemoryOOG  =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::MemoryOOG" []
      | MemoryLimitOOG  =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::MemoryLimitOOG" []
      | PrecompileOOG  =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::PrecompileOOG" []
      | InvalidOperandOOG  =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidOperandOOG" []
      | ReentrancySentryOOG  =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::ReentrancySentryOOG" []
      | OpcodeNotFound  =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OpcodeNotFound" []
      | CallNotAllowedInsideStatic  =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CallNotAllowedInsideStatic" []
      | StateChangeDuringStaticCall  =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::StateChangeDuringStaticCall" []
      | InvalidFEOpcode  =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidFEOpcode" []
      | InvalidJump  =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidJump" []
      | NotActivated  =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::NotActivated" []
      | StackUnderflow  =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::StackUnderflow" []
      | StackOverflow  =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::StackOverflow" []
      | OutOfOffset  =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OutOfOffset" []
      | CreateCollision  =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateCollision" []
      | OverflowPayment  =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OverflowPayment" []
      | PrecompileError  =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::PrecompileError" []
      | NonceOverflow  =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::NonceOverflow" []
      | CreateContractSizeLimit  =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateContractSizeLimit" []
      | CreateContractStartingWithEF  =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateContractStartingWithEF" []
      | CreateInitCodeSizeLimit  =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateInitCodeSizeLimit" []
      | FatalExternalError  =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::FatalExternalError" []
      | ReturnContractInNotInitEOF  =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::ReturnContractInNotInitEOF" []
      | EOFOpcodeDisabledInLegacy  =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::EOFOpcodeDisabledInLegacy" []
      | SubRoutineStackOverflow  =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::SubRoutineStackOverflow" []
      | EofAuxDataOverflow  =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::EofAuxDataOverflow" []
      | EofAuxDataTooSmall  =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::EofAuxDataTooSmall" []
      | InvalidEXTCALLTarget  =>
        Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidEXTCALLTarget" []
      end
  }.
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
      | InternalContinue  =>
        Value.StructTuple "revm_interpreter::instruction_result::InternalResult::InternalContinue" []
      | InternalCallOrCreate  =>
        Value.StructTuple "revm_interpreter::instruction_result::InternalResult::InternalCallOrCreate" []
      | CreateInitCodeStartingEF00  =>
        Value.StructTuple "revm_interpreter::instruction_result::InternalResult::CreateInitCodeStartingEF00" []
      | InvalidExtDelegateCallTarget  =>
        Value.StructTuple "revm_interpreter::instruction_result::InternalResult::InvalidExtDelegateCallTarget" []
      end
  }.
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
      | Revert  =>
        Value.StructTuple "revm_interpreter::instruction_result::SuccessOrHalt::Revert" []
      | Halt γ0 =>
        Value.StructTuple "revm_interpreter::instruction_result::SuccessOrHalt::Halt" [
          φ γ0
        ]
      | FatalExternalError  =>
        Value.StructTuple "revm_interpreter::instruction_result::SuccessOrHalt::FatalExternalError" []
      | Internal γ0 =>
        Value.StructTuple "revm_interpreter::instruction_result::SuccessOrHalt::Internal" [
          φ γ0
        ]
      end
  }.
End SuccessOrHalt.

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
      | Extended  =>
        Value.StructTuple "revm_interpreter::gas::MemoryExtensionResult::Extended" []
      | Same  =>
        Value.StructTuple "revm_interpreter::gas::MemoryExtensionResult::Same" []
      | OutOfGas  =>
        Value.StructTuple "revm_interpreter::gas::MemoryExtensionResult::OutOfGas" []
      end
  }.
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
      | Minus  =>
        Value.StructTuple "revm_interpreter::instructions::i256::Sign::Minus" []
      | Zero  =>
        Value.StructTuple "revm_interpreter::instructions::i256::Sign::Zero" []
      | Plus  =>
        Value.StructTuple "revm_interpreter::instructions::i256::Sign::Plus" []
      end
  }.
End Sign.

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
      | Call  =>
        Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::Call" []
      | CallCode  =>
        Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::CallCode" []
      | DelegateCall  =>
        Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::DelegateCall" []
      | StaticCall  =>
        Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::StaticCall" []
      | ExtCall  =>
        Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::ExtCall" []
      | ExtStaticCall  =>
        Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::ExtStaticCall" []
      | ExtDelegateCall  =>
        Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::ExtDelegateCall" []
      end
  }.
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
End CallValue.

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
      | OutOfGas  =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::OutOfGas" []
      | Blake2WrongLength  =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::Blake2WrongLength" []
      | Blake2WrongFinalIndicatorFlag  =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::Blake2WrongFinalIndicatorFlag" []
      | ModexpExpOverflow  =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::ModexpExpOverflow" []
      | ModexpBaseOverflow  =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::ModexpBaseOverflow" []
      | ModexpModOverflow  =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::ModexpModOverflow" []
      | Bn128FieldPointNotAMember  =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::Bn128FieldPointNotAMember" []
      | Bn128AffineGFailedToCreate  =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::Bn128AffineGFailedToCreate" []
      | Bn128PairLength  =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::Bn128PairLength" []
      | BlobInvalidInputLength  =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::BlobInvalidInputLength" []
      | BlobMismatchedVersion  =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::BlobMismatchedVersion" []
      | BlobVerifyKzgProofFailed  =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::BlobVerifyKzgProofFailed" []
      | Other γ0 =>
        Value.StructTuple "revm_precompile::interface::PrecompileError::Other" [
          φ γ0
        ]
      end
  }.
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
      | HOMESTEAD  =>
        Value.StructTuple "revm_precompile::PrecompileSpecId::HOMESTEAD" []
      | BYZANTIUM  =>
        Value.StructTuple "revm_precompile::PrecompileSpecId::BYZANTIUM" []
      | ISTANBUL  =>
        Value.StructTuple "revm_precompile::PrecompileSpecId::ISTANBUL" []
      | BERLIN  =>
        Value.StructTuple "revm_precompile::PrecompileSpecId::BERLIN" []
      | CANCUN  =>
        Value.StructTuple "revm_precompile::PrecompileSpecId::CANCUN" []
      | PRAGUE  =>
        Value.StructTuple "revm_precompile::PrecompileSpecId::PRAGUE" []
      | LATEST  =>
        Value.StructTuple "revm_precompile::PrecompileSpecId::LATEST" []
      end
  }.
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
      | FRONTIER  =>
        Value.StructTuple "revm_specification::hardfork::SpecId::FRONTIER" []
      | FRONTIER_THAWING  =>
        Value.StructTuple "revm_specification::hardfork::SpecId::FRONTIER_THAWING" []
      | HOMESTEAD  =>
        Value.StructTuple "revm_specification::hardfork::SpecId::HOMESTEAD" []
      | DAO_FORK  =>
        Value.StructTuple "revm_specification::hardfork::SpecId::DAO_FORK" []
      | TANGERINE  =>
        Value.StructTuple "revm_specification::hardfork::SpecId::TANGERINE" []
      | SPURIOUS_DRAGON  =>
        Value.StructTuple "revm_specification::hardfork::SpecId::SPURIOUS_DRAGON" []
      | BYZANTIUM  =>
        Value.StructTuple "revm_specification::hardfork::SpecId::BYZANTIUM" []
      | CONSTANTINOPLE  =>
        Value.StructTuple "revm_specification::hardfork::SpecId::CONSTANTINOPLE" []
      | PETERSBURG  =>
        Value.StructTuple "revm_specification::hardfork::SpecId::PETERSBURG" []
      | ISTANBUL  =>
        Value.StructTuple "revm_specification::hardfork::SpecId::ISTANBUL" []
      | MUIR_GLACIER  =>
        Value.StructTuple "revm_specification::hardfork::SpecId::MUIR_GLACIER" []
      | BERLIN  =>
        Value.StructTuple "revm_specification::hardfork::SpecId::BERLIN" []
      | LONDON  =>
        Value.StructTuple "revm_specification::hardfork::SpecId::LONDON" []
      | ARROW_GLACIER  =>
        Value.StructTuple "revm_specification::hardfork::SpecId::ARROW_GLACIER" []
      | GRAY_GLACIER  =>
        Value.StructTuple "revm_specification::hardfork::SpecId::GRAY_GLACIER" []
      | MERGE  =>
        Value.StructTuple "revm_specification::hardfork::SpecId::MERGE" []
      | SHANGHAI  =>
        Value.StructTuple "revm_specification::hardfork::SpecId::SHANGHAI" []
      | CANCUN  =>
        Value.StructTuple "revm_specification::hardfork::SpecId::CANCUN" []
      | PRAGUE  =>
        Value.StructTuple "revm_specification::hardfork::SpecId::PRAGUE" []
      | OSAKA  =>
        Value.StructTuple "revm_specification::hardfork::SpecId::OSAKA" []
      | LATEST  =>
        Value.StructTuple "revm_specification::hardfork::SpecId::LATEST" []
      end
  }.
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
      | InvalidChainId  =>
        Value.StructTuple "revm_specification::eip7702::authorization_list::InvalidAuthorization::InvalidChainId" []
      | InvalidYParity  =>
        Value.StructTuple "revm_specification::eip7702::authorization_list::InvalidAuthorization::InvalidYParity" []
      | Eip2InvalidSValue  =>
        Value.StructTuple "revm_specification::eip7702::authorization_list::InvalidAuthorization::Eip2InvalidSValue" []
      end
  }.
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
