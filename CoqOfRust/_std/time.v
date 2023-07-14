Require Import CoqOfRust.lib.lib.

(* ********STRUCTS******** *)
(* 
[x] Duration
[x] Instant
[x] SystemTime
[x] SystemTimeError
[x] TryFromFloatSecsError
*)

(* pub struct Duration { /* private fields */ } *)
Module Duration.
  Parameter t : Set.
End Duration.
Definition Duration := Duration.t.

(* pub struct Instant(_); *)
Module Instant.
  Parameter t : Set.
End Instant.
Definition Instant := Instant.t.

(* pub struct SystemTime(_); *)
Module SystemTime.
  Parameter t : Set.
End SystemTime.
Definition SystemTime := SystemTime.t.

(* pub struct SystemTimeError(_); *)
Module SystemTimeError.
  Parameter t : Set.
End SystemTimeError.
Definition SystemTimeError := SystemTimeError.t.

(* pub struct TryFromFloatSecsError { /* private fields */ } *)
Module TryFromFloatSecsError.
  Parameter t : Set.
End TryFromFloatSecsError.
Definition TryFromFloatSecsError := TryFromFloatSecsError.t.

(* ********CONSTANTS******** *)
(* 
[ ] UNIX_EPOCH
*)