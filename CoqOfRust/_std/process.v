Require Import CoqOfRust.lib.lib.

Require Import CoqOfRust.core.option.
Require Import CoqOfRust.alloc.vec.

(* ********STRUCTS******** *)
(* 
[x] ExitStatusErrorE
[x] Child
[x] ChildStderr
[x] ChildStdin
[x] ChildStdout
[x] Command
[x] CommandArgs
[x] CommandEnvs
[x] ExitCode
[x] ExitStatus
[x] Output
[x] Stdio 
*)

(* pub struct ExitStatusError(_); *)
Module ExitStatusError.
  Parameter t : Set.
End ExitStatusError.
Definition ExitStatusError := ExitStatusError.t.

(* pub struct ChildStdin { /* private fields */ } *)
Module ChildStdin.
  Parameter t : Set.
End ChildStdin.
Definition ChildStdin := ChildStdin.t.

(* pub struct ChildStdout { /* private fields */ } *)
Module ChildStdout.
  Parameter t : Set.
End ChildStdout.
Definition ChildStdout := ChildStdout.t.

(* pub struct ChildStderr { /* private fields */ } *)
Module ChildStderr.
  Parameter t : Set.
End ChildStderr.
Definition ChildStderr := ChildStderr.t.

(* 
pub struct Child {
    pub stdin: Option<ChildStdin>,
    pub stdout: Option<ChildStdout>,
    pub stderr: Option<ChildStderr>,
    /* private fields */
}
*)
Module Child.
  Record t : Set := { 
    stdin : Option ChildStdin;
    stdout : Option ChildStdout;
    stderr : Option ChildStderr;
  }.
End Child.
Definition Child := Child.t.

(* pub struct ExitCode(_); *)
Module ExitCode.
  Parameter t : Set.
End ExitCode.
Definition ExitCode := ExitCode.t.

(* pub struct Command { /* private fields */ } *)
Module Command.
  Parameter t : Set.
End Command.
Definition Command := Command.t.

(* pub struct CommandArgs<'a> { /* private fields */ } *)
Module CommandArgs.
  Parameter t : Set.
End CommandArgs.
Definition CommandArgs := CommandArgs.t.

(* pub struct CommandEnvs<'a> { /* private fields */ } *)
Module CommandEnvs.
  Parameter t : Set.
End CommandEnvs.
Definition CommandEnvs := CommandEnvs.t.

(* pub struct ExitStatus(_); *)
Module ExitStatus.
  Parameter t : Set.
End ExitStatus.
Definition ExitStatus := ExitStatus.t.

(* 
pub struct Output {
    pub status: ExitStatus,
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
}
*)
Module Output.
  Record t : Set := { 
    status : ExitStatus;
    stdout : Vec u8;
    stderr : Vec u8;
  }.
End Output.
Definition Output := Output.t.

(* pub struct Stdio(_); *)
Module Stdio.
  Parameter t : Set.
End Stdio.
Definition Stdio := Stdio.t.
 

(* ********TRAITS******** *)
(* [x] Termination *)

(* 
pub trait Termination {
  // Required method
  fn report(self) -> ExitCode;
}
*)
Module Termination.
  Class Trait (Self : Set) : Set := { 
    report : Self -> ExitCode;
  }.
End Termination.

