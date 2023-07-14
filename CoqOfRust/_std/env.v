Require Import CoqOfRust.lib.lib.
Require Import CoqOfRust._std.ffi.

(* ********MODULES******** *)
(*
[x] consts
*)
Module consts.
  (* ********CONSTANTS******** *)
  (*
  [ ] ARCH
  [ ] DLL_EXTENSION
  [ ] DLL_PREFIX
  [ ] DLL_SUFFIX
  [ ] EXE_EXTENSION
  [ ] EXE_SUFFIX
  [ ] FAMILY
  [ ] OS
  *)
End consts.


(* ********STRUCTS******** *)
(*
[x] Args
[x] ArgsOs
[x] JoinPathsError
[x] SplitPaths
[x] Vars
[x] VarsOs
*)

(* pub struct Args { /* private fields */ } *)
Module Args.
  Parameter t : Set.
End Args.
Definition Args := Args.t.

(* pub struct ArgsOs { /* private fields */ } *)
Module ArgsOs.
  Parameter t : Set.
End ArgsOs.
Definition ArgsOs := ArgsOs.t.

(* pub struct JoinPathsError { /* private fields */ } *)
Module JoinPathsError.
  Parameter t : Set.
End JoinPathsError.
Definition JoinPathsError := JoinPathsError.t.

(* pub struct SplitPaths<'a> { /* private fields */ } *)
Module SplitPaths.
  Parameter t : Set.
End SplitPaths.
Definition SplitPaths := SplitPaths.t.

(* pub struct Vars { /* private fields */ } *)
Module Vars.
  Parameter t : Set.
End Vars.
Definition Vars := Vars.t.

(* pub struct VarsOs { /* private fields */ } *)
Module VarsOs.
  Parameter t : Set.
End VarsOs.
Definition VarsOs := VarsOs.t.

(* ********ENUMS******** *)
(*
[x] VarError
*)

(* 
pub enum VarError {
    NotPresent,
    NotUnicode(OsString),
}
*)
Module VarError.
  Inductive t : Set := 
  | NotPresent : t
  | NotUnicode : OsString -> t
  .
End VarError.
Definition VarError := VarError.t.
