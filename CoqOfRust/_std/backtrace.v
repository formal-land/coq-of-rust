Require Import CoqOfRust.lib.lib.

(* ********STRUCTS******** *)
(*
[x] BacktraceFrame
[x] Backtrace
*)
(* pub struct BacktraceFrame { /* private fields */ } *)
Module BacktraceFrame.
  Record t : Set := { }.
End BacktraceFrame.
Definition BacktraceFrame := BacktraceFrame.t.

(* pub struct Backtrace { /* private fields */ } *)
Module Backtrace.
  Record t : Set := { }.
End Backtrace.
Definition Backtrace := Backtrace.t.

(* ********ENUMS******** *)
(*
[x] BacktraceStatus
*)
(* 
#[non_exhaustive]
pub enum BacktraceStatus {
    Unsupported,
    Disabled,
    Captured,
}
*)
Module BacktraceStatus.
  Inductive t : Set := 
  | Unsupported
  | Disabled
  | Captured
  .
End BacktraceStatus.
Definition BacktraceStatus := BacktraceStatus.t.
