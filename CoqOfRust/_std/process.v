Require Import CoqOfRust.lib.lib.

Require CoqOfRust.alloc.vec.
Require CoqOfRust.core.option.
Require CoqOfRust._std.io.

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

(* pub struct ExitStatus(_); *)
Module ExitStatus.
  Parameter t : Set.
End ExitStatus.

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
    stdin : option.Option.t ChildStdin.t;
    stdout : option.Option.t ChildStdout.t;
    stderr : option.Option.t ChildStderr.t;
  }.

  Module Impl.
    Definition Self : Set := t.

    (* pub fn wait(&mut self) -> Result<ExitStatus> *)
    Parameter wait : mut_ref Self -> M (_std.io.Result ExitStatus.t).

    Global Instance AF_wait :
      Notations.DoubleColon Self "wait" := {
      Notations.double_colon := wait;
    }.
  End Impl.
End Child.

(* pub struct ExitCode(_); *)
Module ExitCode.
  Parameter t : Set.
End ExitCode.

(* pub struct Command { /* private fields */ } *)
Module Command.
  Parameter t : Set.

  Module Impl.
    Definition Self : Set := t.

    (* pub fn arg<S: AsRef<OsStr>>(&mut self, arg: S) -> &mut Command *)
    Parameter arg : forall {S : Set}, mut_ref Self -> S -> M (mut_ref t).

    Global Instance AF_arg {S : Set} :
      Notations.DoubleColon Self "arg" := {
      Notations.double_colon := arg (S := S);
    }.

    (* pub fn new<S: AsRef<OsStr>>(program: S) -> Command *)
    Parameter new : forall {S : Set}, S -> M t.

    Global Instance AF_new {S : Set} :
      Notations.DoubleColon Self "new" := {
      Notations.double_colon := new (S := S);
    }.

    (* pub fn spawn(&mut self) -> Result<Child> *)
    Parameter spawn : mut_ref Self -> M (_std.io.Result Child.t).

    Global Instance AF_spawn :
      Notations.DoubleColon Self "spawn" := {
      Notations.double_colon := spawn;
    }.
  End Impl.
End Command.

(* pub struct CommandArgs<'a> { /* private fields */ } *)
Module CommandArgs.
  Parameter t : Set.
End CommandArgs.

(* pub struct CommandEnvs<'a> { /* private fields */ } *)
Module CommandEnvs.
  Parameter t : Set.
End CommandEnvs.

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
    stdout : vec.Vec u8.t vec.Vec.Default.A;
    stderr : vec.Vec u8.t vec.Vec.Default.A;
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
    report : Self -> M ExitCode.t;
  }.
End Termination.

