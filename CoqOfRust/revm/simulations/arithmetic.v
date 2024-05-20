Require Import CoqOfRust.CoqOfRust.
Require CoqOfRust.core.simulations.default.
Require Import CoqOfRust.core.simulations.option.
Require Import CoqOfRust.core.simulations.result.
Require Import CoqOfRust.core.simulations.array.
Require Import CoqOfRust.core.simulations.bool.
Require CoqOfRust.examples.default.examples.ink_contracts.simulations.lib.
Require Import CoqOfRust.simulations.M.

Import simulations.M.Notations.
Import simulations.bool.Notations.

(** ** Primitives *)


(*
  /// Represents the state of gas during execution.
  #[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
  #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
  pub struct Gas {
      /// The initial gas limit. This is constant throughout execution.
      limit: u64,
      /// The remaining gas.
      remaining: u64,
      /// Refunded gas. This is used only at the end of execution.
      refunded: i64,
  }
*)

Module Gas.
  Record t : Set := {
    limit : Z;
    remaining : Z;
    refunded : Z;
  }.

  Global Instance IsToTy : ToTy t := {
    Φ := Ty.path "revm_interpreter::gas::Gas";
  }.

  Global Instance IsToValue : ToValue t := {
    φ x :=
      Value.StructRecord "revm_interpreter::gas::Gas" [
        ("limit", φ x.(limit));
        ("remaining", φ x.(remaining));
        ("refunded", φ x.(refunded))
      ];
  }.
End Gas.

(*
  /// Wrapper type around [`bytes::Bytes`] to support "0x" prefixed hex strings.
  #[derive(Clone, Default, Hash, PartialEq, Eq, PartialOrd, Ord)]
  #[repr(transparent)]
  pub struct Bytes(pub bytes::Bytes);
*)

Module Bytes.
  Parameter t : Set.

  Global Instance IsToTy : ToTy t := {
    Φ := Ty.path "bytes::bytes::Bytes";
  }.

  Global Instance IsToValue : ToValue t.
  Admitted.
End Bytes.

Module Bytecode.
  Parameter t : Set.

  Global Instance IsToTy : ToTy t := {
    Φ := Ty.path "revm_primitives::bytecode::Bytecode";
  }.

  Global Instance IsToValue : ToValue t.
  Admitted.
End Bytecode.

Module Address.
  Parameter t : Set.

  Global Instance IsToTy : ToTy t := {
    Φ := Ty.path "alloy_primitives::bits::address::Address";
  }.

  Global Instance IsToValue : ToValue t.
  Admitted.
End Address.

Module FixedBytes.
  Parameter t : Set.

  Global Instance IsToTy : ToTy t := {
    Φ := Ty.path "alloy_primitives::bits::fixed::FixedBytes";
  }.

  Global Instance IsToValue : ToValue t.
  Admitted.
End FixedBytes.

Definition B256 := FixedBytes.t.
Definition U256 := FixedBytes.t.

(*
  /// EVM contract information.
  #[derive(Clone, Debug, Default)]
  #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
  pub struct Contract {
      /// Contracts data
      pub input: Bytes,
      /// Bytecode contains contract code, size of original code, analysis with gas block and jump table.
      /// Note that current code is extended with push padding and STOP at end.
      pub bytecode: Bytecode,
      /// Bytecode hash for legacy. For EOF this would be None.
      pub hash: Option<B256>,
      /// Target address of the account. Storage of this address is going to be modified.
      pub target_address: Address,
      /// Caller of the EVM.
      pub caller: Address,
      /// Value send to contract from transaction or from CALL opcodes.
      pub call_value: U256,
  }
*)

Module Contract.
  Record t : Set := {
    input : Bytes.t;
    bytecode : Bytecode.t;
    hash : option B256;
    target_address : Address.t;
    caller : Address.t;
    call_value : Z;
  }.

  Global Instance IsToTy : ToTy t := {
    Φ := Ty.path "revm_interpreter::interpreter::contract::Contract";
  }.

  Global Instance IsToValue : ToValue t := {
    φ x :=
      Value.StructRecord "revm_interpreter::interpreter::contract::Contract" [
        ("input", φ x.(input));
        ("bytecode", φ x.(bytecode));
        ("hash", φ x.(hash));
        ("target_address", φ x.(target_address));
        ("caller", φ x.(caller));
        ("call_value", φ x.(call_value))
      ];
  }.
End Contract.

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

  Global Instance IsToTy : ToTy t := {
    Φ := Ty.path "revm_interpreter::instruction_result::InstructionResult";
  }.

  Global Instance IsToValue : ToValue t := {
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

(*
  /// A sequential memory shared between calls, which uses
  /// a `Vec` for internal representation.
  /// A [SharedMemory] instance should always be obtained using
  /// the `new` static method to ensure memory safety.
  #[derive(Clone, PartialEq, Eq, Hash)]
  #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
  pub struct SharedMemory {
      /// The underlying buffer.
      buffer: Vec<u8>,
      /// Memory checkpoints for each depth.
      /// Invariant: these are always in bounds of `data`.
      checkpoints: Vec<usize>,
      /// Invariant: equals `self.checkpoints.last()`
      last_checkpoint: usize,
      /// Memory limit. See [`CfgEnv`](revm_primitives::CfgEnv).
      #[cfg(feature = "memory_limit")]
      memory_limit: u64,
  }
*)

Module SharedMemory.
  Record t : Set := {
    buffer : list Z;
    checkpoints : list Z;
    last_checkpoint : Z;
    memory_limit : option Z;
  }.

  Global Instance IsToTy : ToTy t := {
    Φ := Ty.path "revm_interpreter::interpreter::shared_memory::SharedMemory";
  }.

  Global Instance IsToValue : ToValue t := {
    φ x :=
      Value.StructRecord "revm_interpreter::interpreter::shared_memory::SharedMemory" [
        ("buffer", φ x.(buffer));
        ("checkpoints", φ x.(checkpoints));
        ("last_checkpoint", φ x.(last_checkpoint));
        ("memory_limit", φ x.(memory_limit))
      ];
  }.
End SharedMemory.

(*
  /// EVM stack with [STACK_LIMIT] capacity of words.
  #[derive(Debug, PartialEq, Eq, Hash)]
  #[cfg_attr(feature = "serde", derive(serde::Serialize))]
  pub struct Stack {
      /// The underlying data of the stack.
      data: Vec<U256>,
  }
*)

Module Stack.
  Record t : Set := {
    data : list U256;
  }.

  Global Instance IsToTy : ToTy t := {
    Φ := Ty.path "revm_interpreter::interpreter::stack::Stack";
  }.

  Global Instance IsToValue : ToValue t := {
    φ x :=
      Value.StructRecord "revm_interpreter::interpreter::stack::Stack" [
        ("data", φ x.(data))
      ];
  }.
End Stack.

(*
  /// Function return frame.
  /// Needed information for returning from a function.
  #[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Hash)]
  #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
  pub struct FunctionReturnFrame {
      /// The index of the code container that this frame is executing.
      pub idx: usize,
      /// The program counter where frame execution should continue.
      pub pc: usize,
  }
*)

Module FunctionReturnFrame.
  Record t : Set := {
    idx : Z;
    pc : Z;
  }.

  Global Instance IsToTy : ToTy t := {
    Φ := Ty.path "revm_interpreter::interpreter::function_return_frame::FunctionReturnFrame";
  }.

  Global Instance IsToValue : ToValue t := {
    φ x :=
      Value.StructRecord "revm_interpreter::interpreter::function_return_frame::FunctionReturnFrame" [
        ("idx", φ x.(idx));
        ("pc", φ x.(pc))
      ];
  }.
End FunctionReturnFrame.

(*
  /// Function Stack
  #[derive(Debug, Default)]
  #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
  pub struct FunctionStack {
      pub return_stack: Vec<FunctionReturnFrame>,
      pub current_code_idx: usize,
  }
*)

(* TODO: Vectors? *)
Module FunctionStack.
  Record t : Set := {
    return_stack : list FunctionReturnFrame.t;
    current_code_idx : Z;
  }.

  Global Instance IsToTy : ToTy t := {
    Φ := Ty.path "revm_interpreter::interpreter::function_stack::FunctionStack";
  }.

  Global Instance IsToValue : ToValue t := {
    φ x :=
      Value.StructRecord "revm_interpreter::interpreter::function_stack::FunctionStack" [
        ("return_stack", φ x.(return_stack));
        ("current_code_idx", φ x.(current_code_idx))
      ];
  }.
End FunctionStack.

(*
  /// Call value.
  #[derive(Clone, Debug, PartialEq, Eq, Hash)]
  #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
  pub enum CallValue {
      /// Concrete value, transferred from caller to callee at the end of the transaction.
      Transfer(U256),
      /// Apparent value, that is **not** actually transferred.
      ///
      /// Set when in a `DELEGATECALL` call type, and used by the `CALLVALUE` opcode.
      Apparent(U256),
  }
*)

Module CallValue.
  Inductive t : Set :=
  | Transfer : Z -> t
  | Apparent : Z -> t.

  Global Instance IsToTy : ToTy t := {
    Φ := Ty.path "revm_interpreter::interpreter_action::call_inputs::CallValue";
  }.

  Global Instance IsToValue : ToValue t := {
    φ x :=
      match x with
      | Transfer x => Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallValue::Transfer" [φ x]
      | Apparent x => Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallValue::Approval" [φ x]
      end;
  }.
End CallValue.

(*
  /// Call scheme.
  #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
  #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
  pub enum CallScheme {
      /// `CALL`.
      Call,
      /// `CALLCODE`
      CallCode,
      /// `DELEGATECALL`
      DelegateCall,
      /// `STATICCALL`
      StaticCall,
  }
*)

Module CallScheme.
  Inductive t : Set :=
  | Call
  | CallCode
  | DelegateCall
  | StaticCall.

  Global Instance IsToTy : ToTy t := {
    Φ := Ty.path "revm_interpreter::interpreter_action::call_inputs::CallScheme";
  }.

  Global Instance IsToValue : ToValue t := {
    φ x :=
      match x with
      | Call => Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::Call" []
      | CallCode => Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::CallCode" []
      | DelegateCall => Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::DelegateCall" []
      | StaticCall => Value.StructTuple "revm_interpreter::interpreter_action::call_inputs::CallScheme::StaticCall" []
      end;
  }.
End CallScheme.

(*
  /// Inputs for a call.
  #[derive(Clone, Debug, PartialEq, Eq, Hash)]
  #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
  pub struct CallInputs {
      /// The call data of the call.
      pub input: Bytes,
      /// The return memory offset where the output of the call is written.
      ///
      /// In EOF, this range is invalid as EOF calls do not write output to memory.
      pub return_memory_offset: Range<usize>,
      /// The gas limit of the call.
      pub gas_limit: u64,
      /// The account address of bytecode that is going to be executed.
      ///
      /// Previously `context.code_address`.
      pub bytecode_address: Address,
      /// Target address, this account storage is going to be modified.
      ///
      /// Previously `context.address`.
      pub target_address: Address,
      /// This caller is invoking the call.
      ///
      /// Previously `context.caller`.
      pub caller: Address,
      /// Call value.
      ///
      /// NOTE: This value may not necessarily be transferred from caller to callee, see [`CallValue`].
      ///
      /// Previously `transfer.value` or `context.apparent_value`.
      pub value: CallValue,
      /// The call scheme.
      ///
      /// Previously `context.scheme`.
      pub scheme: CallScheme,
      /// Whether the call is a static call, or is initiated inside a static call.
      pub is_static: bool,
      /// Whether the call is initiated from EOF bytecode.
      pub is_eof: bool,
  }
*)

(* TODO: Ranges? *)
Module CallInputs.
  Record t : Set := {
    input : Bytes.t;
    return_memory_offset : (Z * Z);
    gas_limit : Z;
    bytecode_address : Address.t;
    target_address : Address.t;
    caller : Address.t;
    value : CallValue.t;
    scheme : CallScheme.t;
    is_static : bool;
    is_eof : bool;
  }.

  Global Instance IsToTy : ToTy t := {
    Φ := Ty.path "revm_interpreter::interpreter::call_inputs::CallInputs";
  }.

  Global Instance IsToValue : ToValue t := {
    φ x :=
      Value.StructRecord "revm_interpreter::interpreter::call_inputs::CallInputs" [
        ("input", φ x.(input));
        ("return_memory_offset", φ x.(return_memory_offset));
        ("gas_limit", φ x.(gas_limit));
        ("bytecode_address", φ x.(bytecode_address));
        ("target_address", φ x.(target_address));
        ("caller", φ x.(caller));
        ("value", φ x.(value));
        ("scheme", φ x.(scheme));
        ("is_static", φ x.(is_static));
        ("is_eof", φ x.(is_eof))
      ];
  }.
End CallInputs.

(*
  /// Create scheme.
  #[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
  #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
  pub enum CreateScheme {
      /// Legacy create scheme of `CREATE`.
      Create,
      /// Create scheme of `CREATE2`.
      Create2 {
          /// Salt.
          salt: U256,
      },
  }
*)

Module CreateScheme.
  Inductive t : Set :=
  | Create
  | Create2 : Z -> t.

  Global Instance IsToTy : ToTy t := {
    Φ := Ty.path "revm_primitives::env::CreateScheme";
  }.

  Global Instance IsToValue : ToValue t := {
    φ x :=
      match x with
      | Create => Value.StructTuple "revm_primitives::env::CreateScheme::Create" []
      | Create2 x => Value.StructTuple "revm_primitives::env::CreateScheme::Create2" [φ x]
      end;
  }.
End CreateScheme.

(*
  /// Inputs for a create call.
  #[derive(Clone, Debug, PartialEq, Eq, Hash)]
  #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
  pub struct CreateInputs {
      /// Caller address of the EVM.
      pub caller: Address,
      /// The create scheme.
      pub scheme: CreateScheme,
      /// The value to transfer.
      pub value: U256,
      /// The init code of the contract.
      pub init_code: Bytes,
      /// The gas limit of the call.
      pub gas_limit: u64,
  }
*)

Module CreateInputs.
  Record t : Set := {
    caller : Address.t;
    scheme : CreateScheme.t;
    value : U256;
    init_code : Bytes.t;
    gas_limit : Z;
  }.

  Global Instance IsToTy : ToTy t := {
    Φ := Ty.path "revm_interpreter::interpreter::create_inputs::CreateInputs";
  }.

  Global Instance IsToValue : ToValue t := {
    φ x :=
      Value.StructRecord "revm_interpreter::interpreter::create_inputs::CreateInputs" [
        ("caller", φ x.(caller));
        ("scheme", φ x.(scheme));
        ("value", φ x.(value));
        ("init_code", φ x.(init_code));
        ("gas_limit", φ x.(gas_limit))
      ];
  }.
End CreateInputs.

(*
  /// EOF Header containing
  #[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
  #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
  pub struct EofHeader {
      /// Size of EOF types section.
      /// types section includes num of input and outputs and max stack size.
      pub types_size: u16,
      /// Sizes of EOF code section.
      /// Code size can't be zero.
      pub code_sizes: Vec<u16>,
      /// EOF Container size.
      /// Container size can be zero.
      pub container_sizes: Vec<u16>,
      /// EOF data size.
      pub data_size: u16,
      /// sum code sizes
      pub sum_code_sizes: usize,
      /// sum container sizes
      pub sum_container_sizes: usize,
  }
*)

Module EofHeader.
  Record t : Set := {
    types_size : Z;
    code_sizes : list Z;
    container_sizes : list Z;
    data_size : Z;
    sum_code_sizes : Z;
    sum_container_sizes : Z;
  }.

  Global Instance IsToTy : ToTy t := {
    Φ := Ty.path "revm_primitives::bytecode::eof::header::EofHeader";
  }.

  Global Instance IsToValue : ToValue t := {
    φ x :=
      Value.StructRecord "revm_primitives::bytecode::eof::header::EofHeader" [
        ("types_size", φ x.(types_size));
        ("code_sizes", φ x.(code_sizes));
        ("container_sizes", φ x.(container_sizes));
        ("data_size", φ x.(data_size));
        ("sum_code_sizes", φ x.(sum_code_sizes));
        ("sum_container_sizes", φ x.(sum_container_sizes))
      ];
  }.
End EofHeader.

(*
  /// Types section that contains stack information for matching code section.
  #[derive(Debug, Clone, Default, Hash, PartialEq, Eq, Copy)]
  #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
  pub struct TypesSection {
      /// inputs - 1 byte - `0x00-0x7F`
      /// number of stack elements the code section consumes
      pub inputs: u8,
      /// outputs - 1 byte - `0x00-0x80`
      /// number of stack elements the code section returns or 0x80 for non-returning functions
      pub outputs: u8,
      /// max_stack_height - 2 bytes - `0x0000-0x03FF`
      /// maximum number of elements ever placed onto the stack by the code section
      pub max_stack_size: u16,
  }
*)

Module TypesSection.
  Record t : Set := {
    inputs : Z;
    outputs : Z;
    max_stack_size : Z;
  }.

  Global Instance IsToTy : ToTy t := {
    Φ := Ty.path "revm_primitives::bytecode::eof::types_section::TypesSection";
  }.

  Global Instance IsToValue : ToValue t := {
    φ x :=
      Value.StructRecord "revm_primitives::bytecode::eof::types_section::TypesSection" [
        ("inputs", φ x.(inputs));
        ("outputs", φ x.(outputs));
        ("max_stack_size", φ x.(max_stack_size))
      ];
  }.
End TypesSection.

(*
  /// EOF Body, contains types, code, container and data sections.
  ///
  /// Can be used to create new EOF object.
  #[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
  #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
  pub struct EofBody {
      pub types_section: Vec<TypesSection>,
      pub code_section: Vec<Bytes>,
      pub container_section: Vec<Bytes>,
      pub data_section: Bytes,
      pub is_data_filled: bool,
  }
*)

Module EofBody.
  Record t : Set := {
    types_section : list TypesSection.t;
    code_section : list Bytes.t;
    container_section : list Bytes.t;
    data_section : Bytes.t;
    is_data_filled : bool;
  }.

  Global Instance IsToTy : ToTy t := {
    Φ := Ty.path "revm_primitives::bytecode::eof::body::EofBody";
  }.

  Global Instance IsToValue : ToValue t := {
    φ x :=
      Value.StructRecord "revm_primitives::bytecode::eof::body::EofBody" [
        ("types_section", φ x.(types_section));
        ("code_section", φ x.(code_section));
        ("container_section", φ x.(container_section));
        ("data_section", φ x.(data_section));
        ("is_data_filled", φ x.(is_data_filled))
      ];
  }.
End EofBody.

(*
  /// EOF - Ethereum Object Format.
  ///
  /// It consist of a header, body and raw original bytes Specified in EIP.
  /// Most of body contain Bytes so it references to the raw bytes.
  ///
  /// If there is a need to create new EOF from scratch, it is recommended to use `EofBody` and
  /// use `encode` function to create full [`Eof`] object.
  #[derive(Clone, Debug, PartialEq, Eq, Hash)]
  #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
  pub struct Eof {
      pub header: EofHeader,
      pub body: EofBody,
      pub raw: Bytes,
  }
*)

Module Eof.
  Record t : Set := {
    header : EofHeader.t;
    body : EofBody.t;
    raw : Bytes.t;
  }.

  Global Instance IsToTy : ToTy t := {
    Φ := Ty.path "revm_primitives::bytecode::eof::Eof";
  }.

  Global Instance IsToValue : ToValue t := {
    φ x :=
      Value.StructRecord "revm_primitives::bytecode::eof::Eof" [
        ("header", φ x.(header));
        ("body", φ x.(body));
        ("raw", φ x.(raw))
      ];
  }.
End Eof.

(*
  /// Inputs for EOF create call.
  #[derive(Debug, Default, Clone, PartialEq, Eq)]
  #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
  pub struct EOFCreateInput {
      /// Caller of Eof Craate
      pub caller: Address,
      /// New contract address.
      pub created_address: Address,
      /// Values of ether transfered
      pub value: U256,
      /// Init eof code that is going to be executed.
      pub eof_init_code: Eof,
      /// Gas limit for the create call.
      pub gas_limit: u64,
      /// Return memory range. If EOF creation Reverts it can return the
      /// the memory range.
      pub return_memory_range: Range<usize>,
  }
*)

Module EOFCreateInput.
  Record t : Set := {
    caller : Address.t;
    created_address : Address.t;
    value : U256;
    eof_init_code : Eof.t;
    gas_limit : Z;
    return_memory_range : (Z * Z);
  }.

  Global Instance IsToTy : ToTy t := {
    Φ := Ty.path "revm_interpreter::interpreter::eof_create_input::EOFCreateInput";
  }.

  Global Instance IsToValue : ToValue t := {
    φ x :=
      Value.StructRecord "revm_interpreter::interpreter::eof_create_input::EOFCreateInput" [
        ("caller", φ x.(caller));
        ("created_address", φ x.(created_address));
        ("value", φ x.(value));
        ("eof_init_code", φ x.(eof_init_code));
        ("gas_limit", φ x.(gas_limit));
        ("return_memory_range", φ x.(return_memory_range))
      ];
  }.
End EOFCreateInput.

(*
  /// The result of an interpreter operation.
  #[derive(Clone, Debug, PartialEq, Eq)]
  #[cfg_attr(feature = "serde", derive(::serde::Serialize, ::serde::Deserialize))]
  pub struct InterpreterResult {
      /// The result of the instruction execution.
      pub result: InstructionResult,
      /// The output of the instruction execution.
      pub output: Bytes,
      /// The gas usage information.
      pub gas: Gas,
  }
*)

Module InterpreterResult.
  Record t : Set := {
    result : InstructionResult.t;
    output : Bytes.t;
    gas : Gas.t;
  }.

  Global Instance IsToTy : ToTy t := {
    Φ := Ty.path "revm_interpreter::interpreter::InterpreterResult";
  }.

  Global Instance IsToValue : ToValue t := {
    φ x :=
      Value.StructRecord "revm_interpreter::interpreter::InterpreterResult" [
        ("result", φ x.(result));
        ("output", φ x.(output));
        ("gas", φ x.(gas))
      ];
  }.
End InterpreterResult.

(*
  #[derive(Clone, Debug, Default, PartialEq, Eq)]
  #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
  pub enum InterpreterAction {
      /// CALL, CALLCODE, DELEGATECALL, STATICCALL
      /// or EOF EXT instuction called.
      Call { inputs: Box<CallInputs> },
      /// CREATE or CREATE2 instruction called.
      Create { inputs: Box<CreateInputs> },
      /// EOF CREATE instruction called.
      EOFCreate { inputs: Box<EOFCreateInput> },
      /// Interpreter finished execution.
      Return { result: InterpreterResult },
      /// No action
      #[default]
      None,
  }
*)

(* TODO: Box? *)
Module InterpreterAction.
  Inductive t : Set :=
  | Call : CallInputs.t -> t
  | Create : CreateInputs.t -> t
  | EOFCreate : EOFCreateInput.t -> t
  | Return : InterpreterResult.t -> t
  | None.

  Global Instance IsToTy : ToTy t := {
    Φ := Ty.path "revm_interpreter::interpreter_action::InterpreterAction";
  }.

  Global Instance IsToValue : ToValue t := {
    φ x :=
      match x with
      | Call x => Value.StructRecord "revm_interpreter::interpreter_action::InterpreterAction::Call" [("inputs", φ x)]
      | Create x => Value.StructRecord "revm_interpreter::interpreter_action::InterpreterAction::Create" [("inputs", φ x)]
      | EOFCreate x => Value.StructRecord "revm_interpreter::interpreter_action::InterpreterAction::EOFCreate" [("inputs", φ x)]
      | Return x => Value.StructRecord "revm_interpreter::interpreter_action::InterpreterAction::Return" [("result", φ x)]
      | None => Value.StructRecord "revm_interpreter::interpreter_action::InterpreterAction::None" []
      end;
  }.
End InterpreterAction.

(*
    /// EVM bytecode interpreter.
    #[derive(Debug)]
    pub struct Interpreter {
        /// The current instruction pointer.
        pub instruction_pointer: *const u8,
        /// The gas state.
        pub gas: Gas,
        /// Contract information and invoking data
        pub contract: Contract,
        /// The execution control flag. If this is not set to `Continue`, the interpreter will stop
        /// execution.
        pub instruction_result: InstructionResult,
        /// Currently run Bytecode that instruction result will point to.
        /// Bytecode is owned by the contract.
        pub bytecode: Bytes,
        /// Whether we are Interpreting the Ethereum Object Format (EOF) bytecode.
        /// This is local field that is set from `contract.is_eof()`.
        pub is_eof: bool,
        /// Is init flag for eof create
        pub is_eof_init: bool,
        /// Shared memory.
        ///
        /// Note: This field is only set while running the interpreter loop.
        /// Otherwise it is taken and replaced with empty shared memory.
        pub shared_memory: SharedMemory,
        /// Stack.
        pub stack: Stack,
        /// EOF function stack.
        pub function_stack: FunctionStack,
        /// The return data buffer for internal calls.
        /// It has multi usage:
        ///
        /// * It contains the output bytes of call sub call.
        /// * When this interpreter finishes execution it contains the output bytes of this contract.
        pub return_data_buffer: Bytes,
        /// Whether the interpreter is in "staticcall" mode, meaning no state changes can happen.
        pub is_static: bool,
        /// Actions that the EVM should do.
        ///
        /// Set inside CALL or CREATE instructions and RETURN or REVERT instructions. Additionally those instructions will set
        /// InstructionResult to CallOrCreate/Return/Revert so we know the reason.
        pub next_action: InterpreterAction,
    }
*)

Module Interpreter.
  Record t : Set := {
    instruction_pointer : list Z;
    gas : Gas.t;
    contract : Contract.t;
    instruction_result : InstructionResult.t;
    Bytecode : Bytes.t;
    IsEof : bool;
    IsEofInit : bool;
    SharedMemory : SharedMemory.t;
    stack : Stack.t;
    function_stack : FunctionStack.t;
    return_data_buffer : Bytes.t;
    is_static : bool;
    next_action : InterpreterAction.t;
  }.

  Global Instance IsToTy : ToTy t := {
    Φ := Ty.path "revm_interpreter::interpreter::Interpreter";
  }.

  Global Instance IsToValue : ToValue t := {
    φ x :=
      Value.StructRecord "revm_interpreter::interpreter::Interpreter" [
        ("instruction_pointer", φ x.(instruction_pointer));
        ("gas", φ x.(gas));
        ("contract", φ x.(contract));
        ("instruction_result", φ x.(instruction_result));
        ("Bytecode", φ x.(Bytecode));
        ("IsEof", φ x.(IsEof));
        ("IsEofInit", φ x.(IsEofInit));
        ("SharedMemory", φ x.(SharedMemory));
        ("stack", φ x.(stack));
        ("function_stack", φ x.(function_stack));
        ("return_data_buffer", φ x.(return_data_buffer));
        ("is_static", φ x.(is_static));
        ("next_action", φ x.(next_action))
      ];
  }.
End Interpreter.
