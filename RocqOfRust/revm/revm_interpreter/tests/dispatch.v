Require Import Stdlib.Lists.List.
Require Import Stdlib.ZArith.ZArith.

Require Import alloy_primitives.links.aliases.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.instructions.simulate.table.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.simulate.dispatch.
Require Import revm.revm_interpreter.simulate.instruction_context.
Require Import revm.revm_interpreter.simulate.step.
Require Import revm.revm_interpreter.tests.host.
Require Import revm.revm_interpreter.tests.interpreter.
Require Import revm.revm_interpreter.tests.interpreter_types.
Require Import revm.revm_primitives.links.hardfork.
Require Import ruint.links.lib.
Require Import simulate.RocqOfRust.

Parameter run_InterpreterTypes_for_WIRE :
  RocqOfRust.revm.revm_interpreter.links.interpreter_types.InterpreterTypes.Run
    WIRE WIRE_types.

Parameter run_Host_for_TestHost : Host.Run TestHost.t TestHost.host_types.

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

Definition run_plain_stack_at
    (spec_id : SpecId.t)
    (code : list u8) :
    option (list aliases.U256.t) :=
  let interpreter0 :=
    make_interpreter_with_bytecode code {| Stack.value := [] |} in
  let interpreter := interpreter_with_spec_id interpreter0 spec_id in
  let initial_state :
      InstructionContext.State.t TestHost.t WIRE WIRE_types := {|
    InstructionContext.State.interpreter := interpreter;
    InstructionContext.State.host := TestHost.Make;
  |} in
  let table :=
    FragmentInstructionTable.table
      (H := TestHost.t)
      (run_host := run_Host_for_TestHost)
      run_InterpreterTypes_for_WIRE in
  match
    InterpreterDispatch.run_plain_fuel
      (List.length code)
      InterpreterTypes.I
      bytecode_is_not_end
      table
      initial_state
  with
  | Some (_, {|
      InstructionContext.State.interpreter := final_interpreter;
      InstructionContext.State.host := _
    |}) =>
      Some final_interpreter.(Interpreter.stack).(Stack.value)
  | None => None
  end.

Definition run_plain_stack (code : list u8) : option (list aliases.U256.t) :=
  run_plain_stack_at SpecId.PRAGUE code.

Definition byte (value : Z) : u8 := {| Integer.value := value |}.

Definition run_unary (opcode operand : Z) : option (list aliases.U256.t) :=
  run_plain_stack [byte 96; byte operand; byte opcode; byte 0].

Definition run_binary
    (opcode first second : Z) :
    option (list aliases.U256.t) :=
  run_plain_stack
    [byte 96; byte first; byte 96; byte second; byte opcode; byte 0].

Fixpoint push1_code (values : list Z) : list u8 :=
  match values with
  | [] => []
  | value :: values => byte 96 :: byte value :: push1_code values
  end.

Definition words (values : list Z) : list aliases.U256.t :=
  List.map (fun value => {| Uint.value := value |}) values.

Definition table_static_gas (opcode : Z) : option Z :=
  let table :=
    FragmentInstructionTable.table
      (H := TestHost.t)
      (run_host := run_Host_for_TestHost)
      run_InterpreterTypes_for_WIRE in
  match
    InterpreterStep.instruction_at
      table
      {| Integer.value := opcode |}
  with
  | Some instruction =>
      Some
        (InterpreterStep.instruction_static_gas instruction)
          .(Integer.value)
  | None => None
  end.

Module Test.
  Lemma number_static_gas : table_static_gas 67 = Some 2.
  Proof. timeout 5 vm_compute. reflexivity. Qed.

  Lemma timestamp_static_gas : table_static_gas 66 = Some 2.
  Proof. timeout 5 vm_compute. reflexivity. Qed.

  Lemma timestamp_and_number :
    run_plain_stack [byte 66; byte 67; byte 0] = Some (words [1; 0]).
  Proof. timeout 5 vm_compute. reflexivity. Qed.

  (** Host reads and interpreter-only operations share the same runner. *)
  Lemma number_add :
    run_plain_stack [byte 67; byte 96; byte 2; byte 1; byte 0] =
    Some (words [3]).
  Proof. timeout 5 vm_compute. reflexivity. Qed.
End Test.

(** The executable prefix of GeneralStateTests/stExample/add11.json. *)
Goal
  run_plain_stack
    [(96 : u8); (1 : u8); (96 : u8); (1 : u8); (1 : u8); (0 : u8)] =
    Some [{| Uint.value := 2 |}].
Proof.
  timeout 5 vm_compute.
  reflexivity.
Qed.

(** Stack opcode boundaries through the multi-step dispatcher. *)
Goal table_static_gas 80 = Some 2.
Proof. timeout 5 vm_compute. reflexivity. Qed.

Goal
  List.map
    (fun opcode => table_static_gas (Z.of_nat opcode))
    (List.seq 95 65) =
  Some 2 :: List.repeat (Some 3) 64.
Proof. timeout 5 vm_compute. reflexivity. Qed.

Goal
  run_plain_stack [byte 95; byte 0] =
  Some (words [0]).
Proof. timeout 5 vm_compute. reflexivity. Qed.

Goal
  run_plain_stack
    ([byte 127] ++ List.repeat (byte 0) 31 ++ [byte 42; byte 0]) =
  Some (words [42]).
Proof. timeout 5 vm_compute. reflexivity. Qed.

Goal
  run_plain_stack [byte 96; byte 42; byte 80; byte 0] =
  Some (words []).
Proof. timeout 5 vm_compute. reflexivity. Qed.

Goal
  run_plain_stack [byte 96; byte 42; byte 128; byte 0] =
  Some (words [42; 42]).
Proof. timeout 5 vm_compute. reflexivity. Qed.

Goal
  run_plain_stack
    (push1_code [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16]
      ++ [byte 143; byte 0]) =
  Some (words [1; 16; 15; 14; 13; 12; 11; 10; 9; 8; 7; 6; 5; 4; 3; 2; 1]).
Proof. timeout 5 vm_compute. reflexivity. Qed.

Goal
  run_plain_stack
    (push1_code [1; 2] ++ [byte 144; byte 0]) =
  Some (words [1; 2]).
Proof. timeout 5 vm_compute. reflexivity. Qed.

Goal
  run_plain_stack
    (push1_code
      [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17]
      ++ [byte 159; byte 0]) =
  Some (words [1; 16; 15; 14; 13; 12; 11; 10; 9; 8; 7; 6; 5; 4; 3; 2; 17]).
Proof. timeout 5 vm_compute. reflexivity. Qed.

(** Memory and control-flow opcode gas entries. *)
Goal
  List.map table_static_gas [81; 82; 83; 86; 87; 89; 91] =
  List.map (@Some Z) [3; 3; 3; 8; 10; 2; 1].
Proof. timeout 5 vm_compute. reflexivity. Qed.

Goal
  run_plain_stack
    [byte 96; byte 42; byte 96; byte 0; byte 82;
     byte 96; byte 0; byte 81; byte 0] =
  Some (words [42]).
Proof. timeout 5 vm_compute. reflexivity. Qed.

Goal
  run_plain_stack
    [byte 96; byte 5; byte 86; byte 96; byte 99;
     byte 91; byte 96; byte 42; byte 0] =
  Some (words [42]).
Proof. timeout 5 vm_compute. reflexivity. Qed.

Goal
  run_plain_stack
    [byte 96; byte 1; byte 96; byte 7; byte 87;
     byte 96; byte 99; byte 91; byte 96; byte 42; byte 0] =
  Some (words [42]).
Proof. timeout 5 vm_compute. reflexivity. Qed.

(** An untaken JUMPI does not validate its target. *)
Goal
  run_plain_stack
    [byte 96; byte 0; byte 96; byte 255; byte 87;
     byte 96; byte 42; byte 0] =
  Some (words [42]).
Proof. timeout 5 vm_compute. reflexivity. Qed.

(** The complete bitwise opcode family through the multi-step dispatcher. *)
Goal run_binary 16 20 10 = Some [{| Uint.value := 1 |}].
Proof. timeout 5 vm_compute. reflexivity. Qed.

Goal run_binary 17 20 10 = Some [{| Uint.value := 0 |}].
Proof. timeout 5 vm_compute. reflexivity. Qed.

Goal run_binary 18 20 10 = Some [{| Uint.value := 1 |}].
Proof. timeout 5 vm_compute. reflexivity. Qed.

Goal run_binary 19 20 10 = Some [{| Uint.value := 0 |}].
Proof. timeout 5 vm_compute. reflexivity. Qed.

Goal run_binary 20 42 42 = Some [{| Uint.value := 1 |}].
Proof. timeout 5 vm_compute. reflexivity. Qed.

Goal run_unary 21 0 = Some [{| Uint.value := 1 |}].
Proof. timeout 5 vm_compute. reflexivity. Qed.

Goal run_binary 22 15 240 = Some [{| Uint.value := 0 |}].
Proof. timeout 5 vm_compute. reflexivity. Qed.

Goal run_binary 23 15 240 = Some [{| Uint.value := 255 |}].
Proof. timeout 5 vm_compute. reflexivity. Qed.

Goal run_binary 24 15 240 = Some [{| Uint.value := 255 |}].
Proof. timeout 5 vm_compute. reflexivity. Qed.

Goal run_unary 25 0 = Some [{| Uint.value := 2 ^ 256 - 1 |}].
Proof. timeout 5 vm_compute. reflexivity. Qed.

Goal run_binary 26 18 31 = Some [{| Uint.value := 18 |}].
Proof. timeout 5 vm_compute. reflexivity. Qed.

Goal run_binary 27 8 1 = Some [{| Uint.value := 16 |}].
Proof. timeout 5 vm_compute. reflexivity. Qed.

Goal run_binary 28 8 1 = Some [{| Uint.value := 4 |}].
Proof. timeout 5 vm_compute. reflexivity. Qed.

Goal run_binary 29 8 1 = Some [{| Uint.value := 4 |}].
Proof. timeout 5 vm_compute. reflexivity. Qed.

(** CLZ is enabled starting with Osaka. *)
Goal
  run_plain_stack [byte 96; byte 1; byte 30; byte 0] =
    Some [{| Uint.value := 1 |}].
Proof. timeout 5 vm_compute. reflexivity. Qed.

Goal
  run_plain_stack_at SpecId.OSAKA [byte 96; byte 1; byte 30; byte 0] =
    Some [{| Uint.value := 255 |}].
Proof. timeout 5 vm_compute. reflexivity. Qed.
