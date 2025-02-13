Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.

(*
  #[repr(u8)]
  #[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
  #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
  pub enum InstructionResult {
      // success codes
      #[default]
      Continue = 0x00,
      Stop,
      Return,
      SelfDestruct,
      ReturnContract,

      // revert codes
      Revert = 0x10, // revert opcode
      CallTooDeep,
      OutOfFunds,

      // Actions
      CallOrCreate = 0x20,

      // error codes
      OutOfGas = 0x50,
      MemoryOOG,
      MemoryLimitOOG,
      PrecompileOOG,
      InvalidOperandOOG,
      OpcodeNotFound,
      CallNotAllowedInsideStatic,
      StateChangeDuringStaticCall,
      InvalidFEOpcode,
      InvalidJump,
      NotActivated,
      StackUnderflow,
      StackOverflow,
      OutOfOffset,
      CreateCollision,
      OverflowPayment,
      PrecompileError,
      NonceOverflow,
      /// Create init code size exceeds limit (runtime).
      CreateContractSizeLimit,
      /// Error on created contract that begins with EF
      CreateContractStartingWithEF,
      /// EIP-3860: Limit and meter initcode. Initcode size limit exceeded.
      CreateInitCodeSizeLimit,
      /// Fatal external error. Returned by database.
      FatalExternalError,
      /// RETURNCONTRACT called in not init eof code.
      ReturnContractInNotInitEOF,
      /// Legacy contract is calling opcode that is enabled only in EOF.
      EOFOpcodeDisabledInLegacy,
      /// EOF function stack overflow
      EOFFunctionStackOverflow,
  }
*)

Module InstructionResult.
  Inductive t : Set :=
  (* success codes *)
  | Continue
  | Stop
  | Return
  | SelfDestruct
  | ReturnContract
  (* revert codes *)
  | Revert
  | CallTooDeep
  | OutOfFunds
  (* Actions *)
  | CallOrCreate
  (* error codes *)
  | OutOfGas
  | MemoryOOG
  | MemoryLimitOOG
  | PrecompileOOG
  | InvalidOperandOOG
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
  | EOFFunctionStackOverflow.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::instruction_result::InstructionResult";
    φ x :=
      match x with
      | Continue => Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::Continue" []
      | Stop => Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::Stop" []
      | Return => Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::Return" []
      | SelfDestruct => Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::SelfDestruct" []
      | ReturnContract => Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::ReturnContract" []
      | Revert => Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::Revert" []
      | CallTooDeep => Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CallTooDeep" []
      | OutOfFunds => Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OutOfFunds" []
      | CallOrCreate => Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CallOrCreate" []
      | OutOfGas => Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OutOfGas" []
      | MemoryOOG => Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::MemoryOOG" []
      | MemoryLimitOOG => Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::MemoryLimitOOG" []
      | PrecompileOOG => Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::PrecompileOOG" []
      | InvalidOperandOOG => Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidOperandOOG" []
      | OpcodeNotFound => Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OpcodeNotFound" []
      | CallNotAllowedInsideStatic => Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CallNotAllowedInsideStatic" []
      | StateChangeDuringStaticCall => Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::StateChangeDuringStaticCall" []
      | InvalidFEOpcode => Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidFEOpcode" []
      | InvalidJump => Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::InvalidJump" []
      | NotActivated => Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::NotActivated" []
      | StackUnderflow => Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::StackUnderflow" []
      | StackOverflow => Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::StackOverflow" []
      | OutOfOffset => Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OutOfOffset" []
      | CreateCollision => Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateCollision" []
      | OverflowPayment => Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::OverflowPayment" []
      | PrecompileError => Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::PrecompileError" []
      | NonceOverflow => Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::NonceOverflow" []
      | CreateContractSizeLimit => Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateContractSizeLimit" []
      | CreateContractStartingWithEF => Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateContractStartingWithEF" []
      | CreateInitCodeSizeLimit => Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::CreateInitCodeSizeLimit" []
      | FatalExternalError => Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::FatalExternalError" []
      | ReturnContractInNotInitEOF => Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::ReturnContractInNotInitEOF" []
      | EOFOpcodeDisabledInLegacy => Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::EOFOpcodeDisabledInLegacy" []
      | EOFFunctionStackOverflow => Value.StructTuple "revm_interpreter::instruction_result::InstructionResult::EOFFunctionStackOverflow" []
      end;
  }.
End InstructionResult.
