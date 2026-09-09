Require Import simulate.RocqOfRust.
Require Import revm.revm_interpreter.instructions.simulate.memory.mcopy.
Require Import revm.revm_interpreter.instructions.simulate.memory.mload.
Require Import revm.revm_interpreter.instructions.simulate.memory.msize.
Require Import revm.revm_interpreter.instructions.simulate.memory.mstore.
Require Import revm.revm_interpreter.instructions.simulate.memory.mstore8.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.tests.interpreter.
Require Import revm.revm_interpreter.tests.interpreter_types.
Require Import revm.revm_primitives.links.hardfork.
Require Import ruint.links.lib.

(** ** MSIZE tests *)

(** Test that MSIZE pushes 0 on an empty memory *)
Goal
  let stack := {| Stack.value := [] |} in
  let interpreter := make_interpreter stack in
  let result := msize interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 0 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** MSTORE tests *)

(** Test that MSTORE with offset 0 and value 42 empties the stack and writes to memory *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 0 |};
    {| Uint.value := 42 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := mstore interpreter in
  result.(Interpreter.stack).(Stack.value) = [].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** MLOAD tests *)

(** Helper to build an interpreter with a given stack and memory *)
Definition make_interpreter_with_memory (stack : Stack.t) (memory : Memory.t)
    (gas_val : Gas.t) : Interpreter.t WIRE WIRE_types := {|
  Interpreter.bytecode := {|
    Bytecode.code := [];
    Bytecode.pc := {| Integer.value := 0 |};
    Bytecode.action := None;
  |};
  Interpreter.gas := gas_val;
  Interpreter.stack := stack;
  Interpreter.return_data :=
    {| alloy_primitives.bytes.links.mod.Bytes.value := {| bytes.Bytes.value := [] |} |};
  Interpreter.memory := memory;
  Interpreter.input := empty_input;
  Interpreter.sub_routine := tt;
  Interpreter.control := {|
    Control.gas := gas_val;
    Control.instruction_result := None;
    Control.next_action := None;
  |};
  Interpreter.runtime_flag := SpecId.PRAGUE;
  Interpreter.extend := tt;
|}.

(** Test that MSTORE followed by MLOAD roundtrips: store 42 at offset 0, then load *)
Goal
  let stack_store := {| Stack.value := [
    {| Uint.value := 0 |};
    {| Uint.value := 42 |}
  ] |} in
  let interpreter := make_interpreter stack_store in
  let after_store := mstore interpreter in
  (* Build a new interpreter reusing the memory and gas from after_store *)
  let stack_load := {| Stack.value := [{| Uint.value := 0 |}] |} in
  let interpreter_for_load :=
    make_interpreter_with_memory stack_load
      after_store.(Interpreter.memory)
      after_store.(Interpreter.control).(Control.gas) in
  let after_load := mload interpreter_for_load in
  after_load.(Interpreter.stack).(Stack.value) = [{| Uint.value := 42 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.

(** ** MSTORE8 tests *)

(** Test that MSTORE8 stores one byte and expands memory to one word *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 0 |};
    {| Uint.value := 65 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := mstore8 interpreter in
  List.hd (0 : u8) result.(Interpreter.memory).(Memory.value) = (65 : u8) /\
  List.length result.(Interpreter.memory).(Memory.value) = 32%nat /\
  result.(Interpreter.gas).(Gas.memory).(MemoryGas.words_num) = 1.
Proof.
  timeout 1 vm_compute.
  repeat split; reflexivity.
Qed.

(** ** MCOPY tests *)

(** Test that MCOPY copies memory from src to dst:
    First mstore 42 at offset 0, then mcopy 32 bytes from offset 0 to offset 32 *)
Goal
  let stack_store := {| Stack.value := [
    {| Uint.value := 0 |};
    {| Uint.value := 42 |}
  ] |} in
  let interpreter := make_interpreter stack_store in
  let after_store := mstore interpreter in
  (* Now mcopy: stack = [dst=32, src=0, len=32] *)
  let stack_copy := {| Stack.value := [
    {| Uint.value := 32 |};
    {| Uint.value := 0 |};
    {| Uint.value := 32 |}
  ] |} in
  let interpreter_for_copy :=
    make_interpreter_with_memory stack_copy
      after_store.(Interpreter.memory)
      after_store.(Interpreter.control).(Control.gas) in
  let after_copy := mcopy interpreter_for_copy in
  (* The memory at offset 32..63 should equal memory at offset 0..31 *)
  Memory.slice after_copy.(Interpreter.memory) 32 32 =
  Memory.slice after_copy.(Interpreter.memory) 0 32.
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.
