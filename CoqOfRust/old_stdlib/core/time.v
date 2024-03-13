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

  Module Impl.
    Definition Self : Set := t.

    (* pub const fn from_secs(secs: u64) -> Duration *)
    Parameter from_secs : u64.t -> M t.

    Global Instance AF_from_secs :
      Notations.DoubleColon Self "from_secs" := {
      Notations.double_colon := from_secs;
    }.
  End Impl.
End Duration.

(* pub struct Instant(_); *)
Module Instant.
  Parameter t : Set.
End Instant.

(* pub struct SystemTime(_); *)
Module SystemTime.
  Parameter t : Set.
End SystemTime.

(* pub struct SystemTimeError(_); *)
Module SystemTimeError.
  Parameter t : Set.
End SystemTimeError.

(* pub struct TryFromFloatSecsError { /* private fields */ } *)
Module TryFromFloatSecsError.
  Parameter t : Set.
End TryFromFloatSecsError.

(* ********CONSTANTS******** *)
(* 
[ ] UNIX_EPOCH
*)