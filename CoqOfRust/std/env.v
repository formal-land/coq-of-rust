Require Import CoqOfRust.lib.lib.
Require CoqOfRust.std.ffi.

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

(* pub struct ArgsOs { /* private fields */ } *)
Module ArgsOs.
  Parameter t : Set.
End ArgsOs.

(* pub struct JoinPathsError { /* private fields */ } *)
Module JoinPathsError.
  Parameter t : Set.
End JoinPathsError.

(* pub struct SplitPaths<'a> { /* private fields */ } *)
Module SplitPaths.
  Parameter t : Set.
End SplitPaths.

(* pub struct Vars { /* private fields */ } *)
Module Vars.
  Parameter t : Set.
End Vars.

(* pub struct VarsOs { /* private fields */ } *)
Module VarsOs.
  Parameter t : Set.
End VarsOs.

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
  | NotUnicode : ffi.os_str.OsString -> t
  .
End VarError.

(* pub fn args() -> Args *)
Parameter args : M Args.t.
