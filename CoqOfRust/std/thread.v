Require Import CoqOfRust.lib.lib.

Require CoqOfRust.alloc.boxed.
Require CoqOfRust.core.any.
Require CoqOfRust.core.result.
Require CoqOfRust.core.time.

(* ********TYPE DEFINITIONS******** *)
(* 
[ ] Result
*)

Ltac Result T :=
  exact (result.Result.t
    T
    (boxed.Box.t (dyn [core.any.Any.Trait]) boxed.Box.Default.A)
  ).

(* ********STRUCTS******** *)
(* 
[x] AccessError
[x] Builder
[x] JoinHandle
[x] LocalKey
[x] Scope
[x] ScopedJoinHandle
[x] Thread
[x] ThreadId
*)

(* pub struct AccessError; *)
Module AccessError.
  Inductive t : Set := Build.
End AccessError.

(* pub struct Builder { /* private fields */ } *)
Module Builder.
  Parameter t : Set.
End Builder.

(* pub struct JoinHandle<T>(_); *)
Module JoinHandle.
  Parameter t : Set -> Set.

  Module  Impl.
  Section Impl.
    Context {T : Set}.

    Definition Self : Set := t T.

    (* pub fn join(self) -> Result<T> *)
    Parameter join : Self -> M (ltac:(Result T)).

    Global Instance AF_join : Notations.DoubleColon Self "join" := {
      Notations.double_colon := join;
    }.
  End Impl.
  End Impl.
End JoinHandle.

Module local.
  (* pub struct LocalKey<T: 'static> { /* private fields */ } *)
  Module LocalKey.
    Parameter t : Set -> Set.
  End LocalKey.
End local.

(* pub struct Scope<'scope, 'env: 'scope> { /* private fields */ } *)
Module Scope.
  Parameter t : Set.
End Scope.

(* pub struct ScopedJoinHandle<'scope, T>(_); *)
Module ScopedJoinHandle.
  Parameter t : Set -> Set.
End ScopedJoinHandle.

(* pub struct Thread { /* private fields */ } *)
Module Thread.
  Parameter t : Set.
End Thread.

(* pub struct ThreadId(_); *)
Module ThreadId.
  Parameter t : Set.
End ThreadId.

(* ********FUNCTIONS******** *)
(* 
[ ] available_parallelism
[ ] current
[ ] panicking
[ ] park
[ ] park_timeout
[x] park_timeout_ms(Deprecated)
[ ] scope
[ ] sleep
[x] sleep_ms(Deprecated)
[ ] spawn
[ ] yield_now	
*)

(* pub fn sleep(dur: Duration) *)
Parameter sleep : time.Duration.t -> M unit.

(*
pub fn spawn<F, T>(f: F) -> JoinHandle<T>
where
    F: FnOnce() -> T + Send + 'static,
    T: Send + 'static,
*)
Parameter spawn : forall {T : Set}, M T -> M (JoinHandle.t T).
