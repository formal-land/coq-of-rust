Require Import CoqOfRust.lib.lib.
(* Require Import CoqOfRust.std.ffi. *)


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
  Record t : Set := { }.
End Args.
Definition Args := Args.t.

(* pub struct ArgsOs { /* private fields */ } *)
Module ArgsOs.
  Record t : Set := { }.
End ArgsOs.
Definition ArgsOs := ArgsOs.t.

(* pub struct JoinPathsError { /* private fields */ } *)
Module JoinPathsError.
  Record t : Set := { }.
End JoinPathsError.
Definition JoinPathsError := JoinPathsError.t.

(* pub struct SplitPaths<'a> { /* private fields */ } *)
Module SplitPaths.
  Record t : Set := { }.
End SplitPaths.
Definition SplitPaths := SplitPaths.t.

(* pub struct Vars { /* private fields */ } *)
Module Vars.
  Record t : Set := { }.
End Vars.
Definition Vars := Vars.t.

(* pub struct VarsOs { /* private fields */ } *)
Module VarsOs.
  Record t : Set := { }.
End VarsOs.
Definition VarsOs := VarsOs.t.

(* ********ENUMS******** *)
(*
[ ] VarError
*)
(* 
pub enum VarError {
    NotPresent,
    NotUnicode(OsString),
}
*)
(* BUGGED: How to translate NotUnicode? *)