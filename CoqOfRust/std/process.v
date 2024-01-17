Require Import CoqOfRust.lib.lib.

Require CoqOfRust.alloc.vec.
Require CoqOfRust.core.option.
Require CoqOfRust.std.io.

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

  Module Impl.
    Definition Self : Set := t.

    (* pub fn success(&self) -> bool *)
    Parameter success : ref Self -> M bool.

    Global Instance AF_success :
      Notations.DoubleColon Self "success" := {
      Notations.double_colon := success;
    }.
  End Impl.
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

  Definition Get_stdin :=
    Ref.map (fun α => Some α.(stdin)) (fun β α => Some (α <| stdin := β |>)).
  Definition Get_stdout :=
    Ref.map (fun α => Some α.(stdout)) (fun β α => Some (α <| stdout := β |>)).
  Definition Get_stderr :=
    Ref.map (fun α => Some α.(stderr)) (fun β α => Some (α <| stderr := β |>)).

  Module Impl.
    Definition Self : Set := t.

    (* pub fn wait(&mut self) -> Result<ExitStatus> *)
    Parameter wait : mut_ref Self -> M (std.io.Result ExitStatus.t).

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

  Definition Get_status :=
    Ref.map (fun α => Some α.(status)) (fun β α => Some (α <| status := β |>)).
  Definition Get_stdout :=
    Ref.map (fun α => Some α.(stdout)) (fun β α => Some (α <| stdout := β |>)).
  Definition Get_stderr :=
    Ref.map (fun α => Some α.(stderr)) (fun β α => Some (α <| stderr := β |>)).
End Output.

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
    Parameter spawn : mut_ref Self -> M (std.io.Result Child.t).

    Global Instance AF_spawn :
      Notations.DoubleColon Self "spawn" := {
      Notations.double_colon := spawn;
    }.

    (* pub fn stdin<T: Into<Stdio>>(&mut self, cfg: T) -> &mut Command *)
    Parameter stdin : forall {T : Set}, mut_ref Self -> T -> M (mut_ref t).

    Global Instance AF_stdin {T : Set} :
      Notations.DoubleColon Self "stdin" := {
      Notations.double_colon := stdin (T := T);
    }.

    (* pub fn stdout<T: Into<Stdio>>(&mut self, cfg: T) -> &mut Command *)
    Parameter stdout : forall {T : Set}, mut_ref Self -> T -> M (mut_ref t).

    Global Instance AF_stdout {T : Set} :
      Notations.DoubleColon Self "stdout" := {
      Notations.double_colon := stdout (T := T);
    }.

    (* pub fn output(&mut self) -> Result<Output> *)
    Parameter output : mut_ref Self -> M (std.io.Result Output.t).

    Global Instance AF_output :
      Notations.DoubleColon Self "output" := {
      Notations.double_colon := output;
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

(* pub struct Stdio(_); *)
Module Stdio.
  Parameter t : Set.

  Module Impl.
    Definition Self : Set := t.

    (* pub fn piped() -> Stdio *)
    Parameter piped : M t.

    Global Instance AF_piped :
      Notations.DoubleColon Self "piped" := {
      Notations.double_colon := piped;
    }.
  End Impl.
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

