Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.lib.lib.

Import simulations.M.Notations.

(* NOTE: STUBs: Only implement if necessary *)

Module AccountAddress.
  Inductive t : Set := .
End AccountAddress.

Module Container.
  Inductive t : Set := .
End Container.

Module ContainerRef.
  Inductive t : Set := .
End ContainerRef.

Module IndexRef.
  Inductive t : Set := .
End IndexRef.

(* **************** *)

(* 
enum ValueImpl {
    Invalid,

    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    U128(u128),
    U256(u256::U256),
    Bool(bool),
    Address(AccountAddress),

    Container(Container),

    ContainerRef(ContainerRef),
    IndexedRef(IndexedRef),
}
*)
Module ValueImpl.
  Inductive t : Set :=
  | Invalid
  | U8 : Z -> t
  | U16 : Z -> t
  | U32 : Z -> t
  | U64 : Z -> t
  | U128 : Z -> t
  | U256 : Z -> t
  | Bool : bool -> t
  | Address : AccountAddress.t -> t
  | Container : Container.t -> t
  | ContainerRef : ContainerRef.t -> t
  | IndexedRef : IndexedRef.t -> t
  .
End ValueImpl.

(* pub struct Value(ValueImpl); *)
Module Value.
  Record t := { a0 : ValueImpl.t }.
End Value.
(* 
/// The operand stack.
struct Stack {
    value: Vec<Value>,
}
*)
Module Stack.
  Record t := { value : list Value.t }.
End Stack.