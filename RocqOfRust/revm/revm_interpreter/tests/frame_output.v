Require Import Stdlib.Lists.List.
Require Import Stdlib.ZArith.ZArith.

Require Import revm.revm_interpreter.instructions.simulate.table.
Require Import revm.revm_interpreter.interpreter_action.links.call_inputs.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.simulate.dispatch.
Require Import revm.revm_interpreter.simulate.instruction_context.
Require Import revm.revm_interpreter.tests.dispatch.
Require Import revm.revm_interpreter.tests.host.
Require Import revm.revm_interpreter.tests.interpreter.
Require Import revm.revm_interpreter.tests.interpreter_types.
Require Import revm.revm_primitives.links.hardfork.
Require Import simulate.RocqOfRust.

Import ListNotations.
Open Scope Z_scope.

Module Test.
  Definition should_continue (code : Bytecode.t) : bool :=
    match code.(Bytecode.action) with
    | None => bytecode_is_not_end code
    | Some _ => false
    end.

  Definition run_output_with_gas (gas_limit : Z)
      (spec : SpecId.t) (code input_bytes : list u8) :
      option (InstructionResult.t * list u8 * Z) :=
    let base := make_interpreter_with_bytecode code {| Stack.value := [] |} in
    let initial : Interpreter.t WIRE WIRE_types :=
      base <| @Interpreter.gas WIRE _ WIRE_types _ :=
        base.(Interpreter.gas)
          <| Gas.limit := {| Integer.value := gas_limit |} |>
          <| Gas.remaining := {| Integer.value := gas_limit |} |> |> in
    let input := empty_input <| Input.input := CallInput.Bytes
      {| alloy_primitives.bytes.links.mod.Bytes.value :=
           {| bytes.Bytes.value := input_bytes |} |} |> in
    let interpreter : Interpreter.t WIRE WIRE_types :=
      (interpreter_with_spec_id initial spec)
        <| @Interpreter.input WIRE _ WIRE_types _ := input |> in
    let state : InstructionContext.State.t TestHost.t WIRE WIRE_types := {|
      InstructionContext.State.interpreter := interpreter;
      InstructionContext.State.host := TestHost.Make;
    |} in
    let table := FragmentInstructionTable.table
      (H := TestHost.t) (run_host := run_Host_for_TestHost)
      run_InterpreterTypes_for_WIRE in
    match InterpreterDispatch.run_plain_fuel 100 InterpreterTypes.I
      should_continue table state with
    | Some (InterpreterAction.Return result, _) =>
        Some (result.(InterpreterResult.result),
          result.(InterpreterResult.output)
            .(alloy_primitives.bytes.links.mod.Bytes.value).(bytes.Bytes.value),
          result.(InterpreterResult.gas).(Gas.remaining).(Integer.value))
    | _ => None
    end.

  Definition run_output := run_output_with_gas 1000000.

  Definition one_byte_output (opcode : u8) : list u8 :=
    List.map byte [96; 42; 96; 0; 83; 96; 1; 96; 0] ++ [opcode; (254 : u8)].

  Lemma return_stops_with_output :
    run_output SpecId.CANCUN (one_byte_output 243) [] =
    Some (InstructionResult.Return, [(42 : u8)], 999982).
  Proof. vm_compute. reflexivity. Qed.

  Lemma revert_keeps_output_and_remaining_gas :
    run_output SpecId.CANCUN (one_byte_output 253) [] =
    Some (InstructionResult.Revert, [(42 : u8)], 999982).
  Proof. vm_compute. reflexivity. Qed.

  Lemma return_calldata_with_memory_padding :
    run_output SpecId.CANCUN (List.map byte [54; 96; 0; 96; 0; 55; 89; 96; 0; 243; 254])
      (List.map byte [1; 2; 3]) =
    Some (InstructionResult.Return, List.map byte [1; 2; 3] ++ List.repeat (0 : u8) 29, 999978).
  Proof. vm_compute. reflexivity. Qed.

  Lemma empty_return_ignores_large_offset :
    run_output SpecId.CANCUN
      (List.map byte [96; 0; 127] ++ List.repeat (255 : u8) 32 ++
        List.map byte [243; 254]) [] =
    Some (InstructionResult.Return, ([] : list u8), 999994).
  Proof. vm_compute. reflexivity. Qed.

  Lemma revert_before_byzantium_is_rejected :
    run_output SpecId.FRONTIER (one_byte_output 253) [] =
    Some (InstructionResult.NotActivated, ([] : list u8), 999982).
  Proof. vm_compute. reflexivity. Qed.

  Definition offset_output (opcode : u8) : list u8 :=
    List.map byte [96; 42; 96; 5; 83; 96; 43; 96; 6; 83; 96; 3; 96; 5] ++
    [opcode; (254 : u8)].

  Lemma return_reads_nonzero_offset :
    run_output SpecId.CANCUN (offset_output 243) [] =
    Some (InstructionResult.Return, List.map byte [42; 43; 0], 999973).
  Proof. vm_compute. reflexivity. Qed.

  Lemma revert_reads_nonzero_offset :
    run_output SpecId.CANCUN (offset_output 253) [] =
    Some (InstructionResult.Revert, List.map byte [42; 43; 0], 999973).
  Proof. vm_compute. reflexivity. Qed.

  Lemma empty_revert_ignores_large_offset :
    run_output_with_gas 6 SpecId.CANCUN
      (List.map byte [96; 0; 127] ++ List.repeat (255 : u8) 32 ++
        List.map byte [253; 254]) [] =
    Some (InstructionResult.Revert, ([] : list u8), 0).
  Proof. vm_compute. reflexivity. Qed.

  Lemma return_expansion_exact_gas :
    run_output_with_gas 12 SpecId.CANCUN
      (List.map byte [96; 32; 96; 1; 243; 254]) [] =
    Some (InstructionResult.Return, List.repeat (0 : u8) 32, 0).
  Proof. vm_compute. reflexivity. Qed.

  Lemma return_expansion_insufficient_gas :
    run_output_with_gas 11 SpecId.CANCUN
      (List.map byte [96; 32; 96; 1; 243; 254]) [] =
    Some (InstructionResult.MemoryOOG, ([] : list u8), 5).
  Proof. vm_compute. reflexivity. Qed.

  Lemma revert_expansion_insufficient_gas :
    run_output_with_gas 11 SpecId.CANCUN
      (List.map byte [96; 32; 96; 1; 253; 254]) [] =
    Some (InstructionResult.MemoryOOG, ([] : list u8), 5).
  Proof. vm_compute. reflexivity. Qed.
End Test.
