Require Import CoqOfRust.lib.lib.

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
Definition AccessError := AccessError.t.

(* pub struct Builder { /* private fields */ } *)
Module Builder.
  Parameter t : Set.
End Builder.
Definition Builder := Builder.t.

(* pub struct JoinHandle<T>(_); *)
Module JoinHandle.
  Parameter t : Set -> Set.
End JoinHandle.
Definition JoinHandle := JoinHandle.t.

(* pub struct LocalKey<T: 'static> { /* private fields */ } *)
Module LocalKey.
  Parameter t : Set -> Set.
End LocalKey.
Definition LocalKey := LocalKey.t.

(* pub struct Scope<'scope, 'env: 'scope> { /* private fields */ } *)
Module Scope.
  Parameter t : Set.
End Scope.
Definition Scope := Scope.t.

(* pub struct ScopedJoinHandle<'scope, T>(_); *)
Module ScopedJoinHandle.
  Parameter t : Set -> Set.
End ScopedJoinHandle.
Definition ScopedJoinHandle := ScopedJoinHandle.t.

(* pub struct Thread { /* private fields */ } *)
Module Thread.
  Parameter t : Set.
End Thread.
Definition Thread := Thread.t.

(* pub struct ThreadId(_); *)
Module ThreadId.
  Parameter t : Set.
End ThreadId.
Definition ThreadId := ThreadId.t.

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

(* ********TYPE DEFINITIONS******** *)
(* 
[ ] Result
*)
