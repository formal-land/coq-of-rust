Require Import simulate.RocqOfRust.
Require Import revm.revm_interpreter.links.gas.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.tests.interpreter_types.
Require Import revm.revm_primitives.links.hardfork.

Definition empty_input : Input.t := {|
  Input.target_address :=
    {| alloy_primitives.bits.links.address.Address.value := 0 |};
  Input.caller_address :=
    {| alloy_primitives.bits.links.address.Address.value := 0 |};
  Input.input :=
    revm.revm_interpreter.interpreter_action.links.call_inputs.CallInput.Bytes {|
    alloy_primitives.bytes.links.mod.Bytes.value :=
      {| bytes.Bytes.value := [] |};
  |};
  Input.call_value := {| ruint.links.lib.Uint.value := 0 |};
|}.

Definition make_interpreter_with_bytecode
    (code : list u8)
    (stack : Stack.t) :
    Interpreter.t WIRE WIRE_types := {|
  Interpreter.bytecode := {|
    Bytecode.code := code;
    Bytecode.pc := {| Integer.value := 0 |};
    Bytecode.action := None;
  |};
  Interpreter.gas := {|
    Gas.limit := 1000000;
    Gas.memory := {|
      MemoryGas.expansion_cost := 0;
      MemoryGas.words_num := 0;
    |};
    Gas.refunded := 0;
    Gas.remaining := 1000000;
  |};
  Interpreter.stack := stack;
  Interpreter.return_data :=
    {| alloy_primitives.bytes.links.mod.Bytes.value := {| bytes.Bytes.value := [] |} |};
  Interpreter.memory := {|
    Memory.value := [];
    Memory.shared_buffer := [];
  |};
  Interpreter.input := empty_input;
  Interpreter.sub_routine := tt;
  Interpreter.control := {|
    Control.gas := {|
      Gas.limit := 1000000;
      Gas.memory := {|
        MemoryGas.expansion_cost := 0;
        MemoryGas.words_num := 0;
      |};
      Gas.refunded := 0;
      Gas.remaining := 1000000;
    |};
    Control.instruction_result := None;
    Control.next_action := None;
  |};
  Interpreter.runtime_flag := SpecId.PRAGUE;
  Interpreter.extend := tt;
|}.

Definition make_interpreter (stack : Stack.t) : Interpreter.t WIRE WIRE_types :=
  make_interpreter_with_bytecode [] stack.
