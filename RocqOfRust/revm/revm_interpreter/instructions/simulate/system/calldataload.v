Require Import Stdlib.Lists.List.

Require Import simulate.RocqOfRust.
Require Import alloy_primitives.bits.simulate.fixed.
Require Import alloy_primitives.links.aliases.
Require Import core.convert.simulate.mod.
Require Import core.ops.simulate.deref.
Require Import core.simulate.cmp.
Require Import core.slice.simulate.mod.
Require Import revm.revm_interpreter.gas.simulate.constants.
Require Import revm.revm_interpreter.interpreter_action.simulate.call_inputs.
Require Import revm.revm_interpreter.instructions.links.system.calldataload.
Require Import revm.revm_interpreter.instructions.simulate.macros.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.
Require Import revm.revm_interpreter.simulate.interpreter_types.
Require Import ruint.links.lib.

Import ListNotations.

Open Scope Z_scope.

Fixpoint calldata_take_pad (len : nat) (bytes : list u8) : list u8 :=
  match len with
  | O => []
  | S len =>
      match bytes with
      | [] => (0 : u8) :: calldata_take_pad len []
      | byte :: bytes => byte :: calldata_take_pad len bytes
      end
  end.

Definition calldata_word (bytes : list u8) (offset : usize) : aliases.U256.t :=
  (* Check the binary offset before converting it to a unary list index. *)
  let bytes :=
    if i[offset] <? Z.of_nat (List.length bytes) then
      List.skipn (Z.to_nat i[offset]) bytes
    else [] in
  let bytes :=
    calldata_take_pad 32 bytes in
  {| Uint.value :=
       List.fold_left
         (fun (value : Z) (byte : u8) => (256 * value + i[byte])%Z)
         bytes
         (0 : Z) |}.

Definition calldataload
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    {IInterpreterTypes : InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  popn_top_macro interpreter 0
    id (fun _ offset_ptr_stub interpreter =>
  let offset_ptr := offset_ptr_stub.(RefStub.projection) interpreter.(Interpreter.stack) in
  let offset := as_usize_saturated_macro offset_ptr in
  let input :=
    IInterpreterTypes.(InterpreterTypes.InputsTrait_for_Input).(InputTraits.input)
      .(RefStub.projection) interpreter.(Interpreter.input) in
  let bytes :=
    match input with
    | call_inputs.CallInput.Bytes bytes =>
        call_inputs.CallInput.bytes_as_ref bytes
    | call_inputs.CallInput.SharedBuffer range =>
        let bytes :=
          IInterpreterTypes.(InterpreterTypes.MemoryTrait_for_Memory).(MemoryTrait.global_slice)
            interpreter.(Interpreter.memory) range in
        IInterpreterTypes.(InterpreterTypes.MemoryTrait_for_Memory)
          .(MemoryTrait.Deref_for_Synthetic)
          .(Deref.deref)
          .(RefStub.projection) bytes
    end in
  let word := calldata_word bytes offset in
  let stack :=
    offset_ptr_stub.(RefStub.injection)
      interpreter.(Interpreter.stack)
      word in
  interpreter <| Interpreter.stack := stack |>
  ).

Module Test.
  Goal
    calldata_word [(1 : u8); (2 : u8)] 0 =
    {| Uint.value := 1 * 256 ^ 31 + 2 * 256 ^ 30 |}.
  Proof. vm_compute. reflexivity. Qed.

  Goal
    calldata_word [(1 : u8); (2 : u8)] 1 =
    {| Uint.value := 2 * 256 ^ 31 |}.
  Proof. vm_compute. reflexivity. Qed.

  Goal calldata_word [(1 : u8); (2 : u8)] 2 = {| Uint.value := 0 |}.
  Proof. vm_compute. reflexivity. Qed.
End Test.

Lemma calldataload_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t} `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (IInterpreterTypes : InterpreterTypes.C WIRE_types)
    (InterpreterTypesEq :
      InterpreterTypes.Eq.t WIRE WIRE_types run_InterpreterTypes_for_WIRE IInterpreterTypes)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (host : H) :
  let ref_interpreter := make_ref 0 in
  let ref_host := make_ref (A := H) 1 in
  let context := {|
    instruction_context.InstructionContext.interpreter := ref_interpreter;
    instruction_context.InstructionContext.host := ref_host;
  |} in
    {{
      SimulateM.eval_f
        (run_calldataload run_InterpreterTypes_for_WIRE context)
        [interpreter; host]%stack 🌲
      (
        Output.Success tt,
        [calldataload interpreter; host]%stack
      )
    }}.
Proof.
Admitted.
