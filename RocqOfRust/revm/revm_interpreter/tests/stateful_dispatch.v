Require Import Stdlib.Lists.List.
Require Import Stdlib.ZArith.ZArith.

Require Import alloy_primitives.links.aliases.
Require Import core.links.result.
Require Import core.ops.links.range.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.simulate.host.
Require Import revm.revm_interpreter.instructions.simulate.system.calldataload.
Require Import revm.revm_interpreter.instructions.simulate.table.
Require Import revm.revm_interpreter.interpreter_action.links.call_inputs.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.simulate.dispatch.
Require Import revm.revm_interpreter.simulate.instruction_context.
Require Import revm.revm_interpreter.tests.interpreter.
Require Import revm.revm_interpreter.tests.interpreter_types.
Require Import revm.revm_interpreter.tests.stateful_host.
Require Import revm.revm_primitives.links.hardfork.
Require Import ruint.links.lib.
Require Import simulate.RocqOfRust.

Import ListNotations.

Open Scope Z_scope.

Parameter run_InterpreterTypes_for_WIRE :
  RocqOfRust.revm.revm_interpreter.links.interpreter_types.InterpreterTypes.Run
    WIRE WIRE_types.

Parameter run_Host_for_StatefulHost :
  Host.Run StatefulHost.t StatefulHost.host_types.

Definition bytecode_is_not_end (bytecode : Bytecode.t) : bool :=
  Z.ltb
    bytecode.(Bytecode.pc).(Integer.value)
    (Z.of_nat (List.length bytecode.(Bytecode.code))).

Definition interpreter_with_spec_id
    (interpreter : Interpreter.t WIRE WIRE_types)
    (spec_id : SpecId.t) :
    Interpreter.t WIRE WIRE_types := {|
  Interpreter.bytecode := interpreter.(Interpreter.bytecode);
  Interpreter.gas := interpreter.(Interpreter.gas);
  Interpreter.stack := interpreter.(Interpreter.stack);
  Interpreter.return_data := interpreter.(Interpreter.return_data);
  Interpreter.memory := interpreter.(Interpreter.memory);
  Interpreter.input := interpreter.(Interpreter.input);
  Interpreter.sub_routine := interpreter.(Interpreter.sub_routine);
  Interpreter.control := interpreter.(Interpreter.control);
  Interpreter.runtime_flag := spec_id;
  Interpreter.extend := interpreter.(Interpreter.extend);
|}.

Definition add11_account : StatefulHost.Account.t := {|
  StatefulHost.Account.address := 0;
  StatefulHost.Account.balance := 0;
  StatefulHost.Account.nonce := 0;
  StatefulHost.Account.code := [];
  StatefulHost.Account.code_hash := 0;
  StatefulHost.Account.storage := [];
  StatefulHost.Account.transient_storage := [];
|}.

Definition add11_input : StatefulHost.Input.t := {|
  StatefulHost.Input.block := {|
    StatefulHost.Environment.Block.coinbase := 0;
    StatefulHost.Environment.Block.gas_limit := 1000000;
    StatefulHost.Environment.Block.number := 0;
    StatefulHost.Environment.Block.timestamp := 0;
    StatefulHost.Environment.Block.difficulty := 0;
    StatefulHost.Environment.Block.base_fee := 0;
    StatefulHost.Environment.Block.blob_base_fee := 0;
    StatefulHost.Environment.Block.previous_randao := None;
    StatefulHost.Environment.Block.hashes := [];
  |};
  StatefulHost.Input.transaction := {|
    StatefulHost.Environment.Transaction.chain_id := 1;
    StatefulHost.Environment.Transaction.gas_price := 0;
    StatefulHost.Environment.Transaction.blob_hashes := [];
  |};
  StatefulHost.Input.call := {|
    StatefulHost.Environment.Call.caller := 0;
  |};
  StatefulHost.Input.state := [add11_account];
|}.

Definition add11_code : list u8 :=
  [(96 : u8); (1 : u8); (96 : u8); (1 : u8); (1 : u8);
   (96 : u8); (0 : u8); (85 : u8); (0 : u8)].

Definition run_sstore_once : option (Z * list StatefulHost.Change.t) :=
  let interpreter : Interpreter.t WIRE WIRE_types :=
    make_interpreter
      {| Stack.value :=
           [{| Uint.value := 0 |}; {| Uint.value := 2 |}] |} in
  let interpreter :=
    interpreter_with_spec_id interpreter SpecId.FRONTIER in
  let state : InstructionContext.State.t StatefulHost.t WIRE WIRE_types := {|
    InstructionContext.State.interpreter := interpreter;
    InstructionContext.State.host := StatefulHost.make add11_input;
  |} in
  let state :=
    InterpreterDispatch.stateful
      (H_types := StatefulHost.host_types)
      {| Integer.value := 85 |}
      state in
  match state with
  | {|
      InstructionContext.State.interpreter := _;
      InstructionContext.State.host := host
    |} =>
      match StatefulHost.find_account 0 host.(StatefulHost.accounts) with
      | Some account =>
          Some
            (StatefulHost.lookup_word
              0 account.(StatefulHost.Account.storage),
             StatefulHost.observe_state_changes host)
      | None => None
      end
  end.

Definition run_add11 : option (Z * list StatefulHost.Change.t) :=
  let interpreter : Interpreter.t WIRE WIRE_types :=
    make_interpreter_with_bytecode add11_code {| Stack.value := [] |} in
  let interpreter :=
    interpreter_with_spec_id interpreter SpecId.FRONTIER in
  let initial_state :
      InstructionContext.State.t StatefulHost.t WIRE WIRE_types := {|
    InstructionContext.State.interpreter := interpreter;
    InstructionContext.State.host := StatefulHost.make add11_input;
  |} in
  let table :=
    FragmentInstructionTable.table
      (H := StatefulHost.t)
      (H_types := StatefulHost.host_types)
      (run_host := run_Host_for_StatefulHost)
      run_InterpreterTypes_for_WIRE in
  match
    InterpreterDispatch.run_plain_stateful_fuel
      (List.length add11_code)
      InterpreterTypes.I
      bytecode_is_not_end
      table
      initial_state
  with
  | Some (_, {|
      InstructionContext.State.interpreter := _;
      InstructionContext.State.host := host
    |}) =>
      match StatefulHost.find_account 0 host.(StatefulHost.accounts) with
      | Some account =>
          Some
            (StatefulHost.lookup_word
              0 account.(StatefulHost.Account.storage),
             StatefulHost.observe_state_changes host)
      | None => None
      end
  | None => None
  end.

Module Test.
  Definition shared_calldata_interpreter (offset : Z) :=
    let interpreter :=
      make_interpreter {| Stack.value := [{| Uint.value := offset |}] |} in
    let input :=
      empty_input <| Input.input :=
        CallInput.SharedBuffer
          {| Range.start := {| Integer.value := 1 |};
             Range.end_ := {| Integer.value := 3 |} |} |> in
    interpreter
      <| @Interpreter.input WIRE _ WIRE_types _ := input |>
      <| @Interpreter.memory WIRE _ WIRE_types _ :=
        {| Memory.value := [(9 : u8)];
           Memory.shared_buffer := [(8 : u8); (1 : u8); (2 : u8); (7 : u8)] |} |>.

  Goal
    (calldataload (shared_calldata_interpreter 0)).(Interpreter.stack) =
    {| Stack.value := [{| Uint.value := 1 * 256 ^ 31 + 2 * 256 ^ 30 |}] |}.
  Proof. vm_compute. reflexivity. Qed.

  Goal
    (calldataload (shared_calldata_interpreter 1)).(Interpreter.stack) =
    {| Stack.value := [{| Uint.value := 2 * 256 ^ 31 |}] |}.
  Proof. vm_compute. reflexivity. Qed.

  Goal
    (calldataload (shared_calldata_interpreter (2 ^ 255))).(Interpreter.stack) =
    {| Stack.value := [{| Uint.value := 0 |}] |}.
  Proof. vm_compute. reflexivity. Qed.

  Definition sload_test_address := StatefulHost.rust_address 0.

  Definition sload_test_key := StatefulHost.rust_word 7.

  Definition sload_existing_host : StatefulHost.t :=
    StatefulHost.with_accounts
      (StatefulHost.make add11_input)
      [StatefulHost.account_with_storage add11_account 7 42].

  Goal
    let '(result, host) :=
      StatefulHost.sload_skip_cold_load
        (StatefulHost.make add11_input)
        sload_test_address
        sload_test_key
        false in
    match result with
    | Result.Ok value =>
        (value.(StateLoad.is_cold), host.(StatefulHost.accessed_storage))
    | _ => (false, [])
    end = (true, [(0, 7)]).
  Proof.
    vm_compute.
    reflexivity.
  Qed.

  Goal
    let '(_, host) :=
      StatefulHost.sload_skip_cold_load
        (StatefulHost.make add11_input)
        sload_test_address
        sload_test_key
        false in
    let '(result, host) :=
      StatefulHost.sload_skip_cold_load
        host sload_test_address sload_test_key false in
    match result with
    | Result.Ok value =>
        (value.(StateLoad.is_cold), host.(StatefulHost.accessed_storage))
    | _ => (true, [])
    end = (false, [(0, 7)]).
  Proof.
    vm_compute.
    reflexivity.
  Qed.

  Goal
    let '(result, _) :=
      StatefulHost.sload_skip_cold_load
        sload_existing_host sload_test_address sload_test_key false in
    match result with
    | Result.Ok value => value.(StateLoad.data).(Uint.value)
    | _ => -1
    end = 42.
  Proof.
    vm_compute.
    reflexivity.
  Qed.

  Goal
    let '(_, host) :=
      StatefulHost.sload_skip_cold_load
        (StatefulHost.make add11_input)
        sload_test_address
        sload_test_key
        false in
    let '(result, _) :=
      StatefulHost.sstore_skip_cold_load
        host
        sload_test_address
        sload_test_key
        (StatefulHost.rust_word 1)
        false in
    match result with
    | Result.Ok value => value.(StateLoad.is_cold)
    | _ => true
    end = false.
  Proof.
    vm_compute.
    reflexivity.
  Qed.

  Goal
    let '(result, host) :=
      StatefulHost.sstore_skip_cold_load
        (StatefulHost.make add11_input)
        sload_test_address
        sload_test_key
        (StatefulHost.rust_word 1)
        false in
    match result with
    | Result.Ok value =>
        (value.(StateLoad.is_cold), host.(StatefulHost.accessed_storage))
    | _ => (false, [])
    end = (true, [(0, 7)]).
  Proof.
    vm_compute.
    reflexivity.
  Qed.

  Goal
    let '(_, host) :=
      StatefulHost.sstore_skip_cold_load
        (StatefulHost.make add11_input)
        sload_test_address
        sload_test_key
        (StatefulHost.rust_word 1)
        false in
    let '(result, _) :=
      StatefulHost.sload_skip_cold_load
        host sload_test_address sload_test_key false in
    match result with
    | Result.Ok value => value.(StateLoad.is_cold)
    | _ => true
    end = false.
  Proof.
    vm_compute.
    reflexivity.
  Qed.

  Goal
    let host := StatefulHost.make add11_input in
    StatefulHost.sload_skip_cold_load
      host sload_test_address sload_test_key true =
    (Result.Err LoadError.ColdLoadSkipped, host).
  Proof.
    vm_compute.
    reflexivity.
  Qed.

  Goal
    let host := StatefulHost.make add11_input in
    StatefulHost.sstore_skip_cold_load
      host
      sload_test_address
      sload_test_key
      (StatefulHost.rust_word 1)
      true =
    (Result.Err LoadError.ColdLoadSkipped, host).
  Proof.
    vm_compute.
    reflexivity.
  Qed.

  Goal
    run_sstore_once =
    Some (2, [StatefulHost.Change.Storage 0 0 2]).
  Proof.
    timeout 30 vm_compute.
    reflexivity.
  Qed.

  (** GeneralStateTests/stExample/add11.json executes
      PUSH1 1; PUSH1 1; ADD; PUSH1 0; SSTORE; STOP. *)
  Goal
    run_add11 =
    Some (2, [StatefulHost.Change.Storage 0 0 2]).
  Proof.
    timeout 60 vm_compute.
    reflexivity.
  Qed.
End Test.
