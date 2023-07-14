Require Import CoqOfRust.lib.lib.
Require Import CoqOfRust._std.task.
Require Import CoqOfRust._std.pin.

(* ********STRUCTS******** *)
(*
[x] Pending
[x] PollFn
[x] Ready
*)
(* pub struct Pending<T> { /* private fields */ } *)
Module Pending.
  Parameter t : forall (T : Set), Set.
End Pending.
Definition Pending := Pending.t.

(* pub struct PollFn<F> { /* private fields */ } *)
Module PollFn.
  Parameter t : forall (F : Set), Set.
End PollFn.
Definition PollFn := PollFn.t.

(* pub struct Ready<T>(_); *)
Module Ready.
  Parameter t : forall (T : Set),Set.
End Ready.
Definition Ready := Ready.t.

(* ********TRAITS******** *)
(*
[x] Future
[x] IntoFuture
*)
(* 
pub trait Future {
    type Output;

    // Required method
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output>;
}
*)
Module Future.
  Class Trait (Self Output : Set) : Set := { 
    Output := Output;

    poll : Pin (mut_ref Self) -> mut_ref Context -> Poll Output;
  }.
End Future.

(* 
pub trait IntoFuture {
    type Output;
    type IntoFuture: Future<Output = Self::Output>;

    // Required method
    fn into_future(self) -> Self::IntoFuture;
}
*)
(* NOTE: The syntax for Future trait is weird. It looks like a defaultType but it isn't *)
Module IntoFuture.
  Class Trait (Self Output IntoFuture : Set) 
    `{Future.Trait IntoFuture Output}
  : Set := { 
    Output := Output;
    IntoFuture := IntoFuture;

    into_future : Self -> IntoFuture;
  }.
End IntoFuture.

(* ********FUNCTIONS******** *)
(*
[ ] pending
[ ] poll_fn
[ ] ready
*)
