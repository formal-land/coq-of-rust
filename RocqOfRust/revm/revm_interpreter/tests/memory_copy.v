Require Import Stdlib.Lists.List.
Require Import Stdlib.ZArith.ZArith.
Require Import core.ops.links.range.
Require Import revm.revm_interpreter.instructions.simulate.system.calldatacopy.
Require Import revm.revm_interpreter.instructions.simulate.system.codecopy.
Require Import revm.revm_interpreter.interpreter_action.links.call_inputs.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.tests.interpreter.
Require Import revm.revm_interpreter.tests.interpreter_types.
Require Import ruint.links.lib.
Require Import simulate.RocqOfRust.

Import ListNotations.
Open Scope Z_scope.

Module Test.
  Definition memory : Memory.t := {|
    Memory.value := [(9 : u8); (9 : u8); (9 : u8); (9 : u8)];
    Memory.shared_buffer := [(8 : u8); (1 : u8); (2 : u8); (7 : u8)];
  |}.

  Lemma copy_pads_source_and_preserves_other_bytes :
    (Memory.set_data memory (1 : usize) (1 : usize) (2 : usize)
      [(1 : u8); (2 : u8)]).(Memory.value) =
    [(9 : u8); (2 : u8); (0 : u8); (9 : u8)].
  Proof. vm_compute. reflexivity. Qed.

  Lemma copy_large_source_offset :
    (Memory.set_data memory (0 : usize) ((2 ^ 64 - 1) : usize) (2 : usize)
      [(1 : u8); (2 : u8)]).(Memory.value) =
    [(0 : u8); (0 : u8); (9 : u8); (9 : u8)].
  Proof. vm_compute. reflexivity. Qed.

  Lemma copy_shared_buffer_range :
    (MemoryTrait.set_data_from_global memory (0 : usize) (1 : usize) (2 : usize)
      {| Range.start := (1 : usize); Range.end_ := (3 : usize) |})
      .(Memory.value) = [(2 : u8); (0 : u8); (9 : u8); (9 : u8)].
  Proof. vm_compute. reflexivity. Qed.

  Lemma codecopy_reads_code_and_charges_gas :
    let interpreter := make_interpreter_with_bytecode
      [(1 : u8); (2 : u8); (3 : u8)]
      {| Stack.value :=
           [{| Uint.value := 1 |}; {| Uint.value := 1 |}; {| Uint.value := 4 |}] |} in
    let result := codecopy interpreter in
    (List.firstn 5 result.(Interpreter.memory).(Memory.value),
     List.length result.(Interpreter.memory).(Memory.value),
     result.(Interpreter.gas).(Gas.remaining).(Integer.value)) =
    ([(0 : u8); (2 : u8); (3 : u8); (0 : u8); (0 : u8)], 32%nat, 999991).
  Proof. vm_compute. reflexivity. Qed.

  Lemma zero_length_copy_ignores_large_offsets :
    let interpreter := make_interpreter
      {| Stack.value :=
           [{| Uint.value := 2 ^ 256 - 1 |};
            {| Uint.value := 2 ^ 256 - 1 |}; {| Uint.value := 0 |}] |} in
    let result := calldatacopy interpreter in
    (result.(Interpreter.memory).(Memory.value),
     result.(Interpreter.gas).(Gas.remaining).(Integer.value)) = ([], 999997).
  Proof. vm_compute. reflexivity. Qed.

  Lemma calldatacopy_reads_input_and_charges_gas :
    let interpreter := make_interpreter
      {| Stack.value :=
           [{| Uint.value := 1 |}; {| Uint.value := 1 |}; {| Uint.value := 4 |}] |} in
    let input := empty_input <| Input.input := CallInput.Bytes
      {| alloy_primitives.bytes.links.mod.Bytes.value :=
           {| bytes.Bytes.value := [(1 : u8); (2 : u8); (3 : u8)] |} |} |> in
    let with_input : Interpreter.t WIRE WIRE_types :=
      interpreter <| @Interpreter.input WIRE _ WIRE_types _ := input |> in
    let result := calldatacopy with_input in
    (List.firstn 5 result.(Interpreter.memory).(Memory.value),
     List.length result.(Interpreter.memory).(Memory.value),
     result.(Interpreter.gas).(Gas.remaining).(Integer.value)) =
    ([(0 : u8); (2 : u8); (3 : u8); (0 : u8); (0 : u8)], 32%nat, 999991).
  Proof. vm_compute. reflexivity. Qed.
End Test.
