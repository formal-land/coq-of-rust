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

(* pub struct ChildStdin { /* private fields */ } *)
Module ChildStdin.
  Parameter t : Set.
End ChildStdin.

(* pub struct ChildStdout { /* private fields */ } *)
Module ChildStdout.
  Parameter t : Set.
End ChildStdout.

(* pub struct ChildStderr { /* private fields */ } *)
Module ChildStderr.
  Parameter t : Set.
End ChildStderr.

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
    stdin : Option.t ChildStdin.t;
    stdout : Option.t ChildStdout.t;
    stderr : Option.t ChildStderr.t;
  }.
End Child.

(* pub struct ExitCode(_); *)
Module ExitCode.
  Parameter t : Set.
End ExitCode.

(* pub struct Command { /* private fields */ } *)
Module Command.
  Parameter t : Set.
End Command.

(* pub struct CommandArgs<'a> { /* private fields */ } *)
Module CommandArgs.
  Parameter t : Set.
End CommandArgs.

(* pub struct CommandEnvs<'a> { /* private fields */ } *)
Module CommandEnvs.
  Parameter t : Set.
End CommandEnvs.

(* pub struct ExitStatus(_); *)
Module ExitStatus.
  Parameter t : Set.
End ExitStatus.

(* 
pub struct Output {
    pub status: ExitStatus,
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
}
*)
Module Output.
  Record t : Set := {
    status : ExitStatus.t;
    stdout : Vec u8.t Vec.Default.A;
    stderr : Vec u8.t Vec.Default.A;
  }.
End Output.

(* pub struct Stdio(_); *)
Module Stdio.
  Parameter t : Set.
End Stdio.
 

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
    report : M.Val Self -> M (M.Val ExitCode.t);
  }.
End Termination.

