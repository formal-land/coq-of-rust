Require Import CoqOfRust.lib.lib.

(* ********STRUCTS******** *)
(* 
[x] Exclusive
[?] LazyLock
[x] Arc
[x] Barrier
[x] BarrierWaitResult
[x] Condvar
[x] Mutex
[x] MutexGuard
[x] Once
[x] OnceLock
[x] OnceState
[x] PoisonError
[x] RwLock
[x] RwLockReadGuard
[x] RwLockWriteGuard
[x] WaitTimeoutResult
[x] Weak
*)

(* 
pub struct Exclusive<T>
where
    T: ?Sized,
{ /* private fields */ }
*)
Module Exclusive.
  Parameter t : Set -> Set.
End Exclusive.
Definition Exclusive := Exclusive.t.

(* BUGGED: monad function dependency *)
(* pub struct LazyLock<T, F = fn() -> T> { /* private fields */ } *)
Module LazyLock.
  Parameter t : Set -> Set -> Set.
End LazyLock.
Definition LazyLock := LazyLock.t.

(* 
pub struct Arc<T>
where
    T: ?Sized,
{ /* private fields */ }
*)
Module Arc.
  Parameter t : Set -> Set.
End Arc.
Definition Arc := Arc.t.

(* pub struct Barrier { /* private fields */ } *)
Module Barrier.
  Parameter t : Set.
End Barrier.
Definition Barrier := Barrier.t.

(* pub struct BarrierWaitResult(_); *)
Module BarrierWaitResult.
  Parameter t : Set.
End BarrierWaitResult.
Definition BarrierWaitResult := BarrierWaitResult.t.

(* pub struct Condvar { /* private fields */ } *)
Module Condvar.
  Parameter t : Set.
End Condvar.
Definition Condvar := Condvar.t.

(* pub struct Mutex<T: ?Sized> { /* private fields */ } *)
Module Mutex.
  Parameter t : Set -> Set.
End Mutex.
Definition Mutex := Mutex.t.

(* pub struct MutexGuard<'a, T: ?Sized + 'a> { /* private fields */ } *)
Module MutexGuard.
Parameter t : Set -> Set.
End MutexGuard.
Definition MutexGuard := MutexGuard.t.

(* pub struct Once { /* private fields */ } *)
Module Once.
  Parameter t : Set.
End Once.
Definition Once := Once.t.

(* pub struct OnceLock<T> { /* private fields */ } *)
Module OnceLock.
  Parameter t : Set -> Set.
End OnceLock.
Definition OnceLock := OnceLock.t.

(* pub struct OnceState { /* private fields */ } *)
Module OnceState.
  Parameter t : Set.
End OnceState.
Definition OnceState := OnceState.t.

(* pub struct PoisonError<T> { /* private fields */ } *)
Module PoisonError.
  Parameter t : Set -> Set.
End PoisonError.
Definition PoisonError := PoisonError.t.

(* pub struct RwLock<T: ?Sized> { /* private fields */ } *)
Module RwLock.
  Parameter t : Set -> Set.
End RwLock.
Definition RwLock := RwLock.t.

(* pub struct RwLockReadGuard<'a, T: ?Sized + 'a> { /* private fields */ } *)
Module RwLockReadGuard.
  Parameter t : Set -> Set.
End RwLockReadGuard.
Definition RwLockReadGuard := RwLockReadGuard.t.

(* pub struct RwLockWriteGuard<'a, T: ?Sized + 'a> { /* private fields */ } *)
Module RwLockWriteGuard.
  Parameter t : Set -> Set.
End RwLockWriteGuard.
Definition RwLockWriteGuard := RwLockWriteGuard.t.

(* pub struct WaitTimeoutResult(_); *)
Module WaitTimeoutResult.
  Parameter t : Set.
End WaitTimeoutResult.
Definition WaitTimeoutResult := WaitTimeoutResult.t.

(* 
pub struct Weak<T>
where
    T: ?Sized,
{ /* private fields */ }
*)
Module Weak.
  Parameter t : Set -> Set.
End Weak.
Definition Weak := Weak.t.

(* ********ENUMS******** *)
(* 
[x] TryLockError
*)
(* 
pub enum TryLockError<T> {
  Poisoned(PoisonError<T>),
  WouldBlock,
}
*)
Module TryLockError.
  Inductive t T : Set := 
  | Poisoned: PoisonError T -> t T
  | WouldBlock : t T
  .
End TryLockError.
Definition TryLockError := TryLockError.t.


(* ********CONSTANTS******** *)
(* (Deprecated) *)

(* ********TYPE DEFINITIONS******** *)
(* 
[ ] LockResult
[ ] TryLockResult
*)


