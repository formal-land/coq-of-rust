Require Import core.links.array.
Require Import links.RocqOfRust.
Require Import revm.revm_context_interface.links.host.
Require Import revm.revm_interpreter.instructions.links.arithmetic.
Require Import revm.revm_interpreter.instructions.links.bitwise.bitand.
Require Import revm.revm_interpreter.instructions.links.bitwise.bitor.
Require Import revm.revm_interpreter.instructions.links.bitwise.bitxor.
Require Import revm.revm_interpreter.instructions.links.bitwise.byte.
Require Import revm.revm_interpreter.instructions.links.bitwise.clz.
Require Import revm.revm_interpreter.instructions.links.bitwise.eq.
Require Import revm.revm_interpreter.instructions.links.bitwise.gt.
Require Import revm.revm_interpreter.instructions.links.bitwise.iszero.
Require Import revm.revm_interpreter.instructions.links.bitwise.lt.
Require Import revm.revm_interpreter.instructions.links.bitwise.not.
Require Import revm.revm_interpreter.instructions.links.bitwise.sar.
Require Import revm.revm_interpreter.instructions.links.bitwise.sgt.
Require Import revm.revm_interpreter.instructions.links.bitwise.shl.
Require Import revm.revm_interpreter.instructions.links.bitwise.shr.
Require Import revm.revm_interpreter.instructions.links.bitwise.slt.
Require Import revm.revm_interpreter.instructions.links.block_info.
Require Import revm.revm_interpreter.instructions.links.control.jump.
Require Import revm.revm_interpreter.instructions.links.control.jumpdest.
Require Import revm.revm_interpreter.instructions.links.control.jumpi.
Require Import revm.revm_interpreter.instructions.links.control.stop.
Require Import revm.revm_interpreter.instructions.links.control.unknown.
Require Import revm.revm_interpreter.instructions.links.memory.mload.
Require Import revm.revm_interpreter.instructions.links.memory.msize.
Require Import revm.revm_interpreter.instructions.links.memory.mstore.
Require Import revm.revm_interpreter.instructions.links.memory.mstore8.
Require Import revm.revm_interpreter.instructions.links.stack.
Require Import revm.revm_interpreter.instructions.links.system.calldataload.
Require Import revm.revm_interpreter.instructions.links.system.callvalue.
Require Import revm.revm_interpreter.instructions.links.system.gas.
Require Import revm.revm_interpreter.instructions.links.system.returndatacopy.
Require Import revm.revm_interpreter.instructions.simulate.arithmetic.addmod.
Require Import revm.revm_interpreter.instructions.simulate.arithmetic.div.
Require Import revm.revm_interpreter.instructions.simulate.arithmetic.exp.
Require Import revm.revm_interpreter.instructions.simulate.arithmetic.mulmod.
Require Import revm.revm_interpreter.instructions.simulate.arithmetic.rem.
Require Import revm.revm_interpreter.instructions.simulate.arithmetic.sdiv.
Require Import revm.revm_interpreter.instructions.simulate.arithmetic.signextend.
Require Import revm.revm_interpreter.instructions.simulate.arithmetic.smod.
Require Import revm.revm_interpreter.instructions.simulate.bitwise.bitand.
Require Import revm.revm_interpreter.instructions.simulate.bitwise.bitor.
Require Import revm.revm_interpreter.instructions.simulate.bitwise.bitxor.
Require Import revm.revm_interpreter.instructions.simulate.bitwise.byte.
Require Import revm.revm_interpreter.instructions.simulate.bitwise.clz.
Require Import revm.revm_interpreter.instructions.simulate.bitwise.eq.
Require Import revm.revm_interpreter.instructions.simulate.bitwise.gt.
Require Import revm.revm_interpreter.instructions.simulate.bitwise.iszero.
Require Import revm.revm_interpreter.instructions.simulate.bitwise.lt.
Require Import revm.revm_interpreter.instructions.simulate.bitwise.not.
Require Import revm.revm_interpreter.instructions.simulate.bitwise.sar.
Require Import revm.revm_interpreter.instructions.simulate.bitwise.sgt.
Require Import revm.revm_interpreter.instructions.simulate.bitwise.shl.
Require Import revm.revm_interpreter.instructions.simulate.bitwise.shr.
Require Import revm.revm_interpreter.instructions.simulate.bitwise.slt.
Require Import revm.revm_interpreter.instructions.simulate.block_info.block_number.
Require Import revm.revm_interpreter.instructions.simulate.block_info.chainid.
Require Import revm.revm_interpreter.instructions.simulate.block_info.coinbase.
Require Import revm.revm_interpreter.instructions.simulate.block_info.gaslimit.
Require Import revm.revm_interpreter.instructions.simulate.block_info.timestamp.
Require Import revm.revm_interpreter.instructions.simulate.control.jump.
Require Import revm.revm_interpreter.instructions.simulate.control.jumpdest.
Require Import revm.revm_interpreter.instructions.simulate.control.jumpi.
Require Import revm.revm_interpreter.instructions.simulate.memory.mload.
Require Import revm.revm_interpreter.instructions.simulate.memory.msize.
Require Import revm.revm_interpreter.instructions.simulate.memory.mstore.
Require Import revm.revm_interpreter.instructions.simulate.memory.mstore8.
Require Import revm.revm_interpreter.instructions.simulate.stack.dup.
Require Import revm.revm_interpreter.instructions.simulate.stack.pop.
Require Import revm.revm_interpreter.instructions.simulate.stack.push.
Require Import revm.revm_interpreter.instructions.simulate.stack.push0.
Require Import revm.revm_interpreter.instructions.simulate.stack.swap.
Require Import revm.revm_interpreter.instructions.simulate.system.calldataload.
Require Import revm.revm_interpreter.instructions.simulate.system.callvalue.
Require Import revm.revm_interpreter.instructions.simulate.system.gas.
Require Import revm.revm_interpreter.links.instruction_context.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.links.table.

Module FragmentInstructionTable.
  Fixpoint prepend_repeat {A : Set}
      (value : A)
      (count length : nat)
      (tail : ArrayPairs.t A length) :
      ArrayPairs.t A (count + length) :=
    match count with
    | O => tail
    | S count =>
        ArrayPair.Build_t value (prepend_repeat value count length tail)
    end.

  Fixpoint prepend_map {A : Set}
      (make : nat -> A)
      (start count length : nat)
      (tail : ArrayPairs.t A length) :
      ArrayPairs.t A (count + length) :=
    match count with
    | O => tail
    | S count =>
        ArrayPair.Build_t
          (make start)
          (prepend_map make (S start) count length tail)
    end.

  Definition stop_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      (run_InterpreterTypes_for_WIRE :
        InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run
      (fun context => run_stop run_InterpreterTypes_for_WIRE context).

  Definition add_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
      (run_InterpreterTypes_for_WIRE :
        InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run
      (fun context => run_add run_InterpreterTypes_for_WIRE context).

  Definition sub_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
      (run_InterpreterTypes_for_WIRE :
        InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run
      (fun context => run_sub run_InterpreterTypes_for_WIRE context).

  Definition mul_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
      (run_InterpreterTypes_for_WIRE :
        InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run
      (fun context => run_mul run_InterpreterTypes_for_WIRE context).

  Definition div_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
      (run_InterpreterTypes_for_WIRE :
        InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run
      (fun context => run_div run_InterpreterTypes_for_WIRE context).

  Definition sdiv_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
      (run_InterpreterTypes_for_WIRE :
        InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run
      (fun context => run_sdiv run_InterpreterTypes_for_WIRE context).

  Definition mod_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
      (run_InterpreterTypes_for_WIRE :
        InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run
      (fun context => run_rem run_InterpreterTypes_for_WIRE context).

  Definition smod_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
      (run_InterpreterTypes_for_WIRE :
        InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run
      (fun context => run_smod run_InterpreterTypes_for_WIRE context).

  Definition addmod_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
      (run_InterpreterTypes_for_WIRE :
        InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run
      (fun context => run_addmod run_InterpreterTypes_for_WIRE context).

  Definition mulmod_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
      (run_InterpreterTypes_for_WIRE :
        InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run
      (fun context => run_mulmod run_InterpreterTypes_for_WIRE context).

  Definition exp_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
      (run_InterpreterTypes_for_WIRE :
        InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run
      (fun context => run_exp run_InterpreterTypes_for_WIRE context).

  Definition signextend_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
      (run_InterpreterTypes_for_WIRE :
        InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run
      (fun context => run_signextend run_InterpreterTypes_for_WIRE context).

  Definition lt_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      (run_types : InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run (fun context => run_lt run_types context).

  Definition gt_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      (run_types : InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run (fun context => run_gt run_types context).

  Definition slt_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      (run_types : InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run (fun context => run_slt run_types context).

  Definition sgt_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      (run_types : InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run (fun context => run_sgt run_types context).

  Definition eq_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      (run_types : InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run (fun context => run_bitwise_eq run_types context).

  Definition iszero_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      (run_types : InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run (fun context => run_bitwise_is_zero run_types context).

  Definition and_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      (run_types : InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run (fun context => run_bitwise_bitand run_types context).

  Definition or_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      (run_types : InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run (fun context => run_bitwise_bitor run_types context).

  Definition xor_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      (run_types : InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run (fun context => run_bitwise_bitxor run_types context).

  Definition not_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      (run_types : InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run (fun context => run_bitwise_not run_types context).

  Definition byte_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      (run_types : InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run (fun context => run_byte run_types context).

  Definition shl_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      (run_types : InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run (fun context => run_bitwise_shl run_types context).

  Definition shr_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      (run_types : InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run (fun context => run_bitwise_shr run_types context).

  Definition sar_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      (run_types : InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run (fun context => run_bitwise_sar run_types context).

  Definition clz_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      (run_types : InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run (fun context => run_bitwise_clz run_types context).

  Definition block_number_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
      (run_types : InterpreterTypes.Run WIRE WIRE_types)
      (run_host : Host.Run H H_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run
      (fun context => run_block_number run_types run_host context).

  Definition timestamp_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
      (run_types : InterpreterTypes.Run WIRE WIRE_types)
      (run_host : Host.Run H H_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run
      (fun context => run_timestamp run_types run_host context).

  Definition gaslimit_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
      (run_types : InterpreterTypes.Run WIRE WIRE_types)
      (run_host : Host.Run H H_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run
      (fun context => run_gaslimit run_types run_host context).
  Definition chainid_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
      (run_types : InterpreterTypes.Run WIRE WIRE_types)
      (run_host : Host.Run H H_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run
      (fun context => run_chainid run_types run_host context).
  Definition coinbase_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
      (run_types : InterpreterTypes.Run WIRE WIRE_types)
      (run_host : Host.Run H H_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run
      (fun context => run_coinbase run_types run_host context).

  Definition unknown_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      (run_InterpreterTypes_for_WIRE :
        InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run
      (fun context => run_unknown run_InterpreterTypes_for_WIRE context).

  Definition returndatacopy_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      (run_InterpreterTypes_for_WIRE :
        InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run
      (fun context =>
        run_returndatacopy run_InterpreterTypes_for_WIRE context).

  Definition callvalue_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      (run_InterpreterTypes_for_WIRE :
        InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run
      (fun context => run_callvalue run_InterpreterTypes_for_WIRE context).

  Definition calldataload_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      (run_InterpreterTypes_for_WIRE :
        InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run
      (fun context => run_calldataload run_InterpreterTypes_for_WIRE context).

  Definition gas_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
      (run_InterpreterTypes_for_WIRE :
        InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run
      (fun context => run_gas run_InterpreterTypes_for_WIRE context).

  Definition pop_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      (run_InterpreterTypes_for_WIRE :
        InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run
      (fun context => run_pop run_InterpreterTypes_for_WIRE context).

  Definition mload_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
      (run_InterpreterTypes_for_WIRE :
        InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run
      (fun context => run_mload run_InterpreterTypes_for_WIRE context).

  Definition mstore_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
      (run_InterpreterTypes_for_WIRE :
        InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run
      (fun context => run_mstore run_InterpreterTypes_for_WIRE context).

  Definition mstore8_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
      (run_InterpreterTypes_for_WIRE :
        InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run
      (fun context => run_mstore8 run_InterpreterTypes_for_WIRE context).

  Definition msize_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
      (run_InterpreterTypes_for_WIRE :
        InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run
      (fun context => run_msize run_InterpreterTypes_for_WIRE context).

  Definition jump_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
      (run_InterpreterTypes_for_WIRE :
        InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run
      (fun context => run_jump run_InterpreterTypes_for_WIRE context).

  Definition jumpi_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
      (run_InterpreterTypes_for_WIRE :
        InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run
      (fun context => run_jumpi run_InterpreterTypes_for_WIRE context).

  Definition jumpdest_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
      (run_InterpreterTypes_for_WIRE :
        InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run
      (fun context => run_jumpdest run_InterpreterTypes_for_WIRE context).

  Definition push0_function
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      (run_InterpreterTypes_for_WIRE :
        InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run
      (fun context => run_push0 run_InterpreterTypes_for_WIRE context).

  Definition push_function
      (N : usize)
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
      (run_InterpreterTypes_for_WIRE :
        InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run
      (fun context =>
        run_push
          N
          run_InterpreterTypes_for_WIRE
          context).

  Definition dup_function
      (N : usize)
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
      (run_InterpreterTypes_for_WIRE :
        InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run
      (fun context => run_dup N run_InterpreterTypes_for_WIRE context).

  Definition swap_function
      (N : usize)
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
      (run_InterpreterTypes_for_WIRE :
        InterpreterTypes.Run WIRE WIRE_types) :
    Function1.t (InstructionContext.t H WIRE WIRE_types) unit :=
    Function1.of_run
      (fun context => run_swap N run_InterpreterTypes_for_WIRE context).

  Definition table
      {WIRE H : Set} `{Link WIRE} `{Link H}
      {WIRE_types : InterpreterTypes.Types.t}
      `{InterpreterTypes.Types.AreLinks WIRE_types}
      {H_types : Host.Types.t} `{Host.Types.AreLinks H_types}
      (run_InterpreterTypes_for_WIRE :
        InterpreterTypes.Run WIRE WIRE_types)
      {run_host : Host.Run H H_types} :
    array.t
      (Instruction.t WIRE H WIRE_types)
      {| Integer.value := 256 |} :=
    let unknown_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ :=
        unknown_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 0 |};
    |} in
    let chainid_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ :=
        chainid_function run_InterpreterTypes_for_WIRE run_host;
      Instruction.static_gas := {| Integer.value := 2 |};
    |} in
    let selfbalance_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ :=
        unknown_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 5 |};
    |} in
    let stop_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ :=
        stop_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 0 |};
    |} in
    let add_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ :=
        add_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 3 |};
    |} in
    let sub_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ :=
        sub_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 3 |};
    |} in
    let mul_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ :=
        mul_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 5 |};
    |} in
    let div_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ :=
        div_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 5 |};
    |} in
    let sdiv_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ :=
        sdiv_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 5 |};
    |} in
    let mod_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ :=
        mod_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 5 |};
    |} in
    let smod_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ :=
        smod_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 5 |};
    |} in
    let addmod_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ :=
        addmod_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 8 |};
    |} in
    let mulmod_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ :=
        mulmod_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 8 |};
    |} in
    let exp_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ :=
        exp_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 0 |};
    |} in
    let signextend_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ :=
        signextend_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 5 |};
    |} in
    let lt_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ := lt_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 3 |};
    |} in
    let gt_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ := gt_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 3 |};
    |} in
    let slt_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ := slt_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 3 |};
    |} in
    let sgt_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ := sgt_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 3 |};
    |} in
    let eq_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ := eq_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 3 |};
    |} in
    let iszero_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ :=
        iszero_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 3 |};
    |} in
    let and_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ := and_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 3 |};
    |} in
    let or_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ := or_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 3 |};
    |} in
    let xor_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ := xor_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 3 |};
    |} in
    let not_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ := not_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 3 |};
    |} in
    let byte_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ := byte_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 3 |};
    |} in
    let shl_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ := shl_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 3 |};
    |} in
    let shr_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ := shr_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 3 |};
    |} in
    let sar_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ := sar_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 3 |};
    |} in
    let clz_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ := clz_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 5 |};
    |} in
    let callvalue_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ :=
        callvalue_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 2 |};
    |} in
    let calldataload_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ :=
        calldataload_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 3 |};
    |} in
    let returndatacopy_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ :=
        returndatacopy_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 0 |};
    |} in
    let gas_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ :=
        gas_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 2 |};
    |} in
    let pop_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ :=
        pop_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 2 |};
    |} in
    let mload_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ :=
        mload_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 3 |};
    |} in
    let mstore_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ :=
        mstore_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 3 |};
    |} in
    let mstore8_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ :=
        mstore8_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 3 |};
    |} in
    let msize_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ :=
        msize_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 2 |};
    |} in
    let jump_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ :=
        jump_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 8 |};
    |} in
    let jumpi_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ :=
        jumpi_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 10 |};
    |} in
    let jumpdest_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ :=
        jumpdest_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 1 |};
    |} in
    let push0_instruction : Instruction.t WIRE H WIRE_types := {|
      Instruction.fn_ :=
        push0_function (H := H) run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 2 |};
    |} in
    let push_instruction := fun N : nat => {|
      Instruction.fn_ :=
        push_function
          {| Integer.value := Z.of_nat N |}
          (H := H)
          run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 3 |};
    |} in
    let dup_instruction := fun N : nat => {|
      Instruction.fn_ :=
        dup_function
          {| Integer.value := Z.of_nat N |}
          (H := H)
          run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 3 |};
    |} in
    let swap_instruction := fun N : nat => {|
      Instruction.fn_ :=
        swap_function
          {| Integer.value := Z.of_nat N |}
          (H := H)
          run_InterpreterTypes_for_WIRE;
      Instruction.static_gas := {| Integer.value := 3 |};
    |} in
    let tail_after_push0 :
        ArrayPairs.t (Instruction.t WIRE H WIRE_types) 161 :=
      ArrayPair.Build_t
        push0_instruction
        (prepend_map push_instruction 1 32 128
          (prepend_map dup_instruction 1 16 112
            (prepend_map swap_instruction 1 16 96
              (ArrayPairs.repeat unknown_instruction 96)))) in
    let tail_after_jumpdest :
        ArrayPairs.t (Instruction.t WIRE H WIRE_types) 164 :=
      prepend_repeat unknown_instruction 3 161 tail_after_push0 in
    let tail_after_jumpi :
        ArrayPairs.t (Instruction.t WIRE H WIRE_types) 168 :=
      ArrayPair.Build_t unknown_instruction
        (ArrayPair.Build_t msize_instruction
          (ArrayPair.Build_t gas_instruction
            (ArrayPair.Build_t jumpdest_instruction tail_after_jumpdest))) in
    let tail_after_mstore :
        ArrayPairs.t (Instruction.t WIRE H WIRE_types) 173 :=
      ArrayPair.Build_t mstore8_instruction
        (prepend_repeat unknown_instruction 2 170
          (ArrayPair.Build_t jump_instruction
            (ArrayPair.Build_t jumpi_instruction tail_after_jumpi))) in
    let tail_after_pop :
        ArrayPairs.t (Instruction.t WIRE H WIRE_types) 175 :=
      ArrayPair.Build_t mload_instruction
        (ArrayPair.Build_t mstore_instruction tail_after_mstore) in
    let tail_after_chainid :
        ArrayPairs.t (Instruction.t WIRE H WIRE_types) 186 :=
      ArrayPair.Build_t chainid_instruction
        (ArrayPair.Build_t selfbalance_instruction
          (prepend_repeat unknown_instruction 8 176
            (ArrayPair.Build_t pop_instruction tail_after_pop))) in
    let tail_after_number :
        ArrayPairs.t (Instruction.t WIRE H WIRE_types) 188 :=
      ArrayPair.Build_t unknown_instruction
        (ArrayPair.Build_t
          {| Instruction.fn_ := gaslimit_function
               run_InterpreterTypes_for_WIRE run_host;
             Instruction.static_gas := {| Integer.value := 2 |} |}
          tail_after_chainid) in
    let tail_after_returndatacopy :
        ArrayPairs.t (Instruction.t WIRE H WIRE_types) 193 :=
      prepend_repeat unknown_instruction 2 191
        (ArrayPair.Build_t
          {| Instruction.fn_ := coinbase_function
               run_InterpreterTypes_for_WIRE run_host;
             Instruction.static_gas := {| Integer.value := 2 |} |}
        (ArrayPair.Build_t
          {| Instruction.fn_ := timestamp_function
               run_InterpreterTypes_for_WIRE run_host;
             Instruction.static_gas := {| Integer.value := 2 |} |}
        (ArrayPair.Build_t
          {| Instruction.fn_ := block_number_function
               run_InterpreterTypes_for_WIRE run_host;
             Instruction.static_gas := {| Integer.value := 2 |} |}
          tail_after_number))) in
    let tail_after_callvalue :
        ArrayPairs.t (Instruction.t WIRE H WIRE_types) 204 :=
      ArrayPair.Build_t callvalue_instruction
        (ArrayPair.Build_t calldataload_instruction
          (prepend_repeat
            unknown_instruction
            8
            194
            (ArrayPair.Build_t
              returndatacopy_instruction
              tail_after_returndatacopy))) in
    let tail_after_bitwise :
        ArrayPairs.t (Instruction.t WIRE H WIRE_types) 225 :=
      prepend_repeat unknown_instruction 21 204 tail_after_callvalue in
    let bitwise_instructions :
        ArrayPairs.t (Instruction.t WIRE H WIRE_types) 240 :=
      ArrayPair.Build_t lt_instruction
        (ArrayPair.Build_t gt_instruction
          (ArrayPair.Build_t slt_instruction
            (ArrayPair.Build_t sgt_instruction
              (ArrayPair.Build_t eq_instruction
                (ArrayPair.Build_t iszero_instruction
                  (ArrayPair.Build_t and_instruction
                    (ArrayPair.Build_t or_instruction
                      (ArrayPair.Build_t xor_instruction
                        (ArrayPair.Build_t not_instruction
                          (ArrayPair.Build_t byte_instruction
                            (ArrayPair.Build_t shl_instruction
                              (ArrayPair.Build_t shr_instruction
                                (ArrayPair.Build_t sar_instruction
                                  (ArrayPair.Build_t
                                    clz_instruction
                                    tail_after_bitwise)))))))))))))) in
    @array.Build_t
      (Instruction.t WIRE H WIRE_types)
      {| Integer.value := 256 |}
      (
        ArrayPair.Build_t
          stop_instruction
          (ArrayPair.Build_t
            add_instruction
            (ArrayPair.Build_t
              mul_instruction
              (ArrayPair.Build_t
                sub_instruction
                (ArrayPair.Build_t
                  div_instruction
                  (ArrayPair.Build_t
                    sdiv_instruction
                    (ArrayPair.Build_t
                      mod_instruction
                      (ArrayPair.Build_t
                      smod_instruction
                        (ArrayPair.Build_t
                          addmod_instruction
                          (ArrayPair.Build_t
                            mulmod_instruction
                            (ArrayPair.Build_t
                              exp_instruction
                              (ArrayPair.Build_t
                                signextend_instruction
                                (prepend_repeat
                                  unknown_instruction
                                  4
                                  240
                                  bitwise_instructions))))))))))))
      ).

End FragmentInstructionTable.
