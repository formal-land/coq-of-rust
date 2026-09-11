From Stdlib Require Import List ZArith.

Require Import core.links.result.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_interpreter.instructions.simulate.table.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.instruction_result.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_action.
Require Import revm.revm_interpreter.simulate.dispatch.
Require Import revm.revm_interpreter.simulate.instruction_context.
Require Import revm.revm_interpreter.tests.interpreter.
Require Import revm.revm_interpreter.tests.interpreter_types.
Require Import revm.revm_interpreter.tests.stateful_dispatch.
Require Import revm.revm_interpreter.tests.stateful_host.
Require Import revm.revm_primitives.links.hardfork.
Require Import ruint.links.lib.
Require Import simulate.RocqOfRust.

Import ListNotations.
Open Scope Z_scope.

Module Test.
  Definition load_status (host : StatefulHost.t) (skip_cold_load : bool) :=
    let '(result, host) := StatefulHost.load_account_info_skip_cold_load
      host (StatefulHost.rust_address 42) skip_cold_load in
    match result with
    | Result.Ok account =>
        Some (account.(AccountInfoLoad.is_cold), host.(StatefulHost.accessed_accounts))
    | Result.Err _ => None
    end.

  Lemma first_account_read_is_cold (input : StatefulHost.Input.t) :
    load_status (StatefulHost.make input) false = Some (true, [42]).
  Proof. reflexivity. Qed.

  Lemma repeated_account_read_is_warm (input : StatefulHost.Input.t) :
    let '(_, host) := StatefulHost.load_account_info_skip_cold_load
      (StatefulHost.make input) (StatefulHost.rust_address 42) false in
    load_status host false = Some (false, [42]).
  Proof. reflexivity. Qed.

  Lemma skipped_cold_read_preserves_host (input : StatefulHost.Input.t) :
    StatefulHost.load_account_info_skip_cold_load
      (StatefulHost.make input) (StatefulHost.rust_address 42) true =
    (Result.Err LoadError.ColdLoadSkipped, StatefulHost.make input).
  Proof. reflexivity. Qed.

  Lemma warm_read_is_not_skipped (input : StatefulHost.Input.t) :
    load_status (StatefulHost.warm_account (StatefulHost.make input) 42) true =
    Some (false, [42]).
  Proof. reflexivity. Qed.

  Lemma warming_does_not_create_accounts (input : StatefulHost.Input.t) :
    (StatefulHost.warm_account (StatefulHost.make input) 42).(StatefulHost.accounts) =
    input.(StatefulHost.Input.state).
  Proof. reflexivity. Qed.
  Definition should_continue (code : Bytecode.t) : bool :=
    match code.(Bytecode.action) with
    | None => bytecode_is_not_end code
    | Some _ => false
    end.

  Definition run_account_program_with_access (spec : SpecId.t) (gas_limit : Z)
      (code warm_accounts : list Z) (access_list : list (Z * list Z)) :
      option (InstructionResult.t * list Z * Z * list Z) :=
    let interpreter := make_interpreter_with_bytecode
      (List.map (fun value => {| Integer.value := value |}) code)
      {| Stack.value := [] |} in
    let interpreter : Interpreter.t WIRE WIRE_types :=
      (interpreter_with_spec_id interpreter spec)
        <| @Interpreter.input WIRE _ WIRE_types _ :=
          empty_input <| Input.target_address := StatefulHost.rust_address 1234 |> |>
        <| @Interpreter.gas WIRE _ WIRE_types _ :=
          interpreter.(Interpreter.gas)
            <| Gas.limit := {| Integer.value := gas_limit |} |>
            <| Gas.remaining := {| Integer.value := gas_limit |} |> |> in
    let host := List.fold_left StatefulHost.warm_account warm_accounts
      (StatefulHost.with_accounts (StatefulHost.make add11_input)
        [StatefulHost.account_with_balance add11_account 99]) in
    let host := StatefulHost.warm_access_list host access_list in
    let state : InstructionContext.State.t StatefulHost.t WIRE WIRE_types := {|
      InstructionContext.State.interpreter := interpreter;
      InstructionContext.State.host := host;
    |} in
    let table := FragmentInstructionTable.table
      (H := StatefulHost.t) (run_host := run_Host_for_StatefulHost)
      run_InterpreterTypes_for_WIRE in
    match InterpreterDispatch.run_plain_stateful_fuel 100 InterpreterTypes.I
      should_continue table state with
    | Some (InterpreterAction.Return result,
        {| InstructionContext.State.interpreter := interpreter;
           InstructionContext.State.host := host |}) =>
        Some (result.(InterpreterResult.result),
          List.map Uint.value interpreter.(Interpreter.stack).(Stack.value),
          result.(InterpreterResult.gas).(Gas.remaining).(Integer.value),
          host.(StatefulHost.accessed_accounts))
    | _ => None
    end.

  Definition run_account_program spec gas_limit code warm_accounts :=
    run_account_program_with_access spec gas_limit code warm_accounts [].

  Lemma address_uses_call_target :
    run_account_program SpecId.CANCUN 2 [48; 0] [] =
    Some (InstructionResult.Stop, [1234], 0, []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma balance_charges_cold_then_warm :
    run_account_program SpecId.CANCUN 2706 [96; 0; 49; 96; 0; 49; 0] [] =
    Some (InstructionResult.Stop, [99; 99], 0, [0]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma balance_pre_warmed_account :
    run_account_program SpecId.CANCUN 103 [96; 0; 49; 0] [0] =
    Some (InstructionResult.Stop, [99], 0, [0]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma missing_account_has_zero_balance :
    run_account_program SpecId.CANCUN 2603 [96; 42; 49; 0] [] =
    Some (InstructionResult.Stop, [0], 0, [42]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma balance_cold_oog_does_not_warm_account :
    run_account_program SpecId.CANCUN 2602 [96; 0; 49; 0] [] =
    Some (InstructionResult.OutOfGas, [0], 0, []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma balance_underflow_does_not_access_host :
    run_account_program SpecId.CANCUN 100 [49; 0] [] =
    Some (InstructionResult.StackUnderflow, [], 100, []).
  Proof. vm_compute. reflexivity. Qed.

  Lemma balance_frontier_gas :
    run_account_program SpecId.FRONTIER 23 [96; 0; 49; 0] [] =
    Some (InstructionResult.Stop, [99], 0, [0]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma balance_istanbul_gas :
    run_account_program SpecId.ISTANBUL 703 [96; 0; 49; 0] [] =
    Some (InstructionResult.Stop, [99], 0, [0]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma balance_uses_low_160_bits :
    run_account_program SpecId.CANCUN 2603
      ([127; 128] ++ List.repeat 0 31 ++ [49; 0]) [] =
    Some (InstructionResult.Stop, [99], 0, [0]).
  Proof. vm_compute. reflexivity. Qed.
  Lemma access_list_balance_is_warm :
    run_account_program_with_access SpecId.CANCUN 103
      [96; 0; 49; 0] [] [(0, [])] =
    Some (InstructionResult.Stop, [99], 0, [0]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma sload_without_access_list_costs_2100 :
    run_account_program_with_access SpecId.CANCUN 2103
      [96; 7; 84; 0] [1234] [] =
    Some (InstructionResult.Stop, [0], 0, [1234]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma sload_with_access_list_costs_100 :
    run_account_program_with_access SpecId.CANCUN 103
      [96; 7; 84; 0] [1234] [(1234, [7])] =
    Some (InstructionResult.Stop, [0], 0, [1234]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma access_list_warms_only_the_selected_slot :
    run_account_program_with_access SpecId.CANCUN 2103
      [96; 8; 84; 0] [1234] [(1234, [7])] =
    Some (InstructionResult.Stop, [0], 0, [1234]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma sstore_without_access_list_costs_22100 :
    run_account_program_with_access SpecId.CANCUN 22106
      [96; 1; 96; 7; 85; 0] [1234] [] =
    Some (InstructionResult.Stop, [], 0, [1234]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma sstore_with_access_list_costs_20000 :
    run_account_program_with_access SpecId.CANCUN 20006
      [96; 1; 96; 7; 85; 0] [1234] [(1234, [7])] =
    Some (InstructionResult.Stop, [], 0, [1234]).
  Proof. vm_compute. reflexivity. Qed.

  Lemma duplicate_access_entries_are_idempotent (input : StatefulHost.Input.t) :
    StatefulHost.warm_access_list (StatefulHost.make input)
      [(42, [7; 7]); (42, [7])] =
    StatefulHost.warm_access_list (StatefulHost.make input) [(42, [7])].
  Proof. reflexivity. Qed.

  Lemma access_list_preserves_account_state (input : StatefulHost.Input.t) :
    (StatefulHost.warm_access_list (StatefulHost.make input) [(42, [7])])
      .(StatefulHost.accounts) = input.(StatefulHost.Input.state).
  Proof. reflexivity. Qed.
End Test.
