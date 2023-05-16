Require Import CoqOfRust.lib.lib.

(* ********STRUCTS******** *)
(* 
[x] Exclusive
[ ] LazyLock
[ ] Arc
[ ] Barrier
[ ] BarrierWaitResult
[ ] Condvar
[ ] Mutex
[ ] MutexGuard
[ ] Once
[ ] OnceLock
[ ] OnceState
[ ] PoisonError
[ ] RwLock
[ ] RwLockReadGuard
[ ] RwLockWriteGuard
[ ] WaitTimeoutResult
[ ] Weak
*)
(* 
pub struct Exclusive<T>
where
    T: ?Sized,
{ /* private fields */ }
*)
Module Exclusive.
  Record t (T : Set): Set := { }.
End Exclusive.
Definition Exclusive := Exclusive.t.

(* pub struct LazyLock<T, F = fn() -> T> { /* private fields */ } *)


(* ********ENUMS******** *)
(* 
[ ] TryLockError
*)

(* ********CONSTANTS******** *)
(* (Deprecated) *)

(* ********TYPE DEFINITIONS******** *)
(* 
[ ] LockResult
[ ] TryLockResult
*)


