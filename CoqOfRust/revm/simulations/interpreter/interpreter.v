Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.
Import simulations.M.Notations.
Require Import CoqOfRust.revm.simulations.dependencies.
Require Import CoqOfRust.revm.simulations.interpreter.interpreter.instruction_result.
Require Import CoqOfRust.revm.simulations.interpreter.interpreter.gas.
Require Import CoqOfRust.revm.simulations.interpreter.interpreter.contract.
Require Import CoqOfRust.revm.simulations.interpreter.interpreter.shared_memory.
Require Import CoqOfRust.revm.simulations.interpreter.interpreter.stack.
Require Import CoqOfRust.revm.simulations.interpreter.interpreter.function_stack.
Require Import CoqOfRust.revm.simulations.interpreter.interpreter_action.

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
    instruction_pointer : Z;
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

  Definition update_gas
    {A : Set}
    (m : MS? Gas.t string A) :
    MS? Interpreter.t string A :=
  letS? interp := readS? in
  let gas := Interpreter.gas interp in
  match m gas with
  | (result, state) =>
    match result with
    | inr e => panicS? e
    | inl result =>
      letS? _ := writeS? (interp <|
        Interpreter.gas := state
      |>) in
      returnS? result
    end
  end.
End Interpreter.
