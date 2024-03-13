Require Import CoqOfRust.lib.lib.

Require CoqOfRust.alloc.alloc.

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

(* BUGGED: monad function dependency *)
(* pub struct LazyLock<T, F = fn() -> T> { /* private fields */ } *)
Module LazyLock.
  Parameter t : Set -> Set -> Set.
End LazyLock.

(* pub struct Arc<T: ?Sized, A: Allocator = Global> { /* private fields */ } *)
Module Arc.
  Parameter t : Set -> Set -> Set.

  Module Default.
    Definition A : Set := alloc.Global.t.
  End Default.

  Module  Impl.
  Section Impl.
    Context {T : Set}.

    Definition Self : Set := t T alloc.Global.t.

    (* pub fn new(data: T) -> Arc<T> *)
    Parameter new : T -> M Self.

    Global Instance AF_new : Notations.DoubleColon Self "new" := {
      Notations.double_colon := new;
    }.
  End Impl.
  End Impl.
End Arc.

(* pub struct Barrier { /* private fields */ } *)
Module Barrier.
  Parameter t : Set.
End Barrier.

(* pub struct BarrierWaitResult(_); *)
Module BarrierWaitResult.
  Parameter t : Set.
End BarrierWaitResult.

(* pub struct Condvar { /* private fields */ } *)
Module Condvar.
  Parameter t : Set.
End Condvar.

(* pub struct Mutex<T: ?Sized> { /* private fields */ } *)
Module Mutex.
  Parameter t : Set -> Set.
End Mutex.

(* pub struct MutexGuard<'a, T: ?Sized + 'a> { /* private fields */ } *)
Module MutexGuard.
Parameter t : Set -> Set.
End MutexGuard.

Module once.
  (* pub struct Once { /* private fields */ } *)
  Module Once.
    Parameter t : Set.
  End Once.
End once.

(* pub struct OnceLock<T> { /* private fields */ } *)
Module OnceLock.
  Parameter t : Set -> Set.
End OnceLock.

(* pub struct OnceState { /* private fields */ } *)
Module OnceState.
  Parameter t : Set.
End OnceState.

(* pub struct PoisonError<T> { /* private fields */ } *)
Module PoisonError.
  Parameter t : Set -> Set.
End PoisonError.

(* pub struct RwLock<T: ?Sized> { /* private fields */ } *)
Module RwLock.
  Parameter t : Set -> Set.
End RwLock.

(* pub struct RwLockReadGuard<'a, T: ?Sized + 'a> { /* private fields */ } *)
Module RwLockReadGuard.
  Parameter t : Set -> Set.
End RwLockReadGuard.

(* pub struct RwLockWriteGuard<'a, T: ?Sized + 'a> { /* private fields */ } *)
Module RwLockWriteGuard.
  Parameter t : Set -> Set.
End RwLockWriteGuard.

(* pub struct WaitTimeoutResult(_); *)
Module WaitTimeoutResult.
  Parameter t : Set.
End WaitTimeoutResult.

(* 
pub struct Weak<T>
where
    T: ?Sized,
{ /* private fields */ }
*)
Module Weak.
  Parameter t : Set -> Set.
End Weak.

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
  | Poisoned: PoisonError.t T -> t T
  | WouldBlock : t T
  .
End TryLockError.


(* ********CONSTANTS******** *)
(* (Deprecated) *)

(* ********TYPE DEFINITIONS******** *)
(* 
[ ] LockResult
[ ] TryLockResult
*)


