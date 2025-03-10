Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import revm.revm_interpreter.instructions.control.
Require Import revm.revm_interpreter.links.interpreter.
Require Import revm.revm_interpreter.links.interpreter_types.

(*
pub fn chainid<WIRE: InterpreterTypes, H: Host + ?Sized>(
    interpreter: &mut Interpreter<WIRE>,
    host: &mut H,
) {
    check!(interpreter, ISTANBUL);
    gas!(interpreter, gas::BASE);
    push!(interpreter, U256::from(host.cfg().chain_id()));
}
*)