Require Import CoqOfRust.lib.lib.
Require Import CoqOfRust._std.sync.

(* ********STRUCTS******** *)
(* 
[x] Ready
[x] Context
[x] RawWaker
[x] RawWakerVTable
[x] Waker 
*)

(* pub struct Ready<T>(_); *)
Module Ready.
  Parameter t : Set -> Set.
End Ready.
Definition Ready := Ready.t.

(* pub struct Context<'a> { /* private fields */ } *)
Module Context.
  Parameter t : Set.
End Context.
Definition Context := Context.t.

(* pub struct RawWaker { /* private fields */ } *)
Module RawWaker.
  Parameter t : Set.
End RawWaker.
Definition RawWaker := RawWaker.t.

(* pub struct RawWakerVTable { /* private fields */ } *)
Module RawWakerVTable.
  Parameter t : Set.
End RawWakerVTable.
Definition RawWakerVTable := RawWakerVTable.t.

(* pub struct Waker { /* private fields */ } *)
Module Waker.
  Parameter t : Set.
End Waker.
Definition Waker := Waker.t.

(* ********ENUMS******** *)
(* [x] Poll *)

(* 
pub enum Poll<T> {
    Ready(T),
    Pending,
}
*)
Module Poll.
  Inductive t (T : Set) : Set := 
  | Ready : T -> t T
  | Pending : t T.
End Poll.
Definition Poll := Poll.t.

(* ********TRAITS******** *)
(* [x] Wake *)

(* 
pub trait Wake {
    // Required method
    fn wake(self: Arc<Self>);

    // Provided method
    fn wake_by_ref(self: &Arc<Self>) { ... }
}
*)
Module Wake.
  Class Trait `{State.Trait} (Self : Set) : Set := { 
    wake : Arc Self -> unit;

    wake_by_ref : ref (Arc Self) -> unit;
  }.
End Wake.
