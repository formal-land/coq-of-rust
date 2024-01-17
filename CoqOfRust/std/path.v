Require Import CoqOfRust.lib.lib.

Require Import CoqOfRust.std.ffi.
Require CoqOfRust.core.option.

(* ********STRUCTS******** *)
(*
[x] Ancestors
[x] Components
[x] Display
[x] Iter
[x] Path
[x] PathBuf
[x] PrefixComponent
[x] StripPrefixError
*)

(* pub struct Ancestors<'a> { /* private fields */ } *)
Module Ancestors.
  Parameter t : Set.
End Ancestors.

(* pub struct Components<'a> { /* private fields */ } *)
Module Components.
  Parameter t : Set.
End Components.

(* pub struct Display<'a> { /* private fields */ } *)
Module Display.
  Parameter t : Set.
End Display.

(* pub struct Iter<'a> { /* private fields */ } *)
Module Iter.
  Parameter t : Set.
End Iter.

(* pub struct PathBuf { /* private fields */ } *)
Module PathBuf.
  Parameter t : Set.

  Module Impl.
    Definition Self : Set := t.

    (* pub fn push<P: AsRef<Path>>(&mut self, path: P) *)
    Parameter push : forall {P : Set}, mut_ref Self -> P -> M unit.

    Global Instance AF_push {P : Set} : Notations.DoubleColon Self "push" := {
      Notations.double_colon := push (P := P);
    }.

    (* pub fn set_file_name<S: AsRef<OsStr>>(&mut self, file_name: S) *)
    Parameter set_file_name : forall {S : Set}, mut_ref Self -> S -> M unit.

    Global Instance AF_set_file_name {S : Set} :
        Notations.DoubleColon Self "set_file_name" := {
      Notations.double_colon := set_file_name (S := S);
    }.
  End Impl.
End PathBuf.

(* pub struct Path { /* private fields */ } *)
Module Path.
  Parameter t : Set.

  Module Impl.
    Definition Self : Set := t.

    (* pub fn new<S: AsRef<OsStr> + ?Sized>(s: &S) -> &Path *)
    Parameter new : forall {S : Set}, ref S -> M (ref t).

    Global Instance AF_new {S : Set} : Notations.DoubleColon Self "new" := {
      Notations.double_colon := new (S := S);
    }.

    (* pub fn display(&self) -> Display<'_> *)
    Parameter display : ref Self -> M Display.t.

    Global Instance AF_display : Notations.DoubleColon Self "display" := {
      Notations.double_colon := display;
    }.

    (* pub fn join<P: AsRef<Path>>(&self, path: P) -> PathBuf *)
    Parameter join : forall {P : Set}, ref Self -> P -> M PathBuf.t.

    Global Instance AF_join {P : Set} : Notations.DoubleColon Self "join" := {
      Notations.double_colon := join (P := P);
    }.

    (* pub fn to_str(&self) -> Option<&str> *)
    Parameter to_str : ref Self -> M (option.Option.t (ref str.t)).

    Global Instance AF_to_str : Notations.DoubleColon Self "to_str" := {
      Notations.double_colon := to_str;
    }.
  End Impl.
End Path.

(* pub struct PrefixComponent<'a> { /* private fields */ } *)
Module PrefixComponent.
  Parameter t : Set.
End PrefixComponent.

(* pub struct StripPrefixError(_); *)
Module StripPrefixError.
  Parameter t : Set.
End StripPrefixError.


(* ********ENUMS******** *)
(*
[x] Component
[x] Prefix
*)

(* 
pub enum Component<'a> {
    Prefix(PrefixComponent<'a>),
    RootDir,
    CurDir,
    ParentDir,
    Normal(&'a OsStr),
}
*)
Module Component.
  Inductive t : Set := 
  | Prefix : PrefixComponent.t -> t
  | RootDir : t
  | CurDir : t
  | ParentDir : t
  | Normal : ref OsStr -> t
  .
End Component.

(* 
pub enum Prefix<'a> {
    Verbatim(&'a OsStr),
    VerbatimUNC(&'a OsStr, &'a OsStr),
    VerbatimDisk(u8),
    DeviceNS(&'a OsStr),
    UNC(&'a OsStr, &'a OsStr),
    Disk(u8),
}
*)
Module Prefix.
  Inductive t : Set := 
  | Verbatim : ref OsStr -> t
  | VerbatimUNC : ref OsStr -> ref OsStr -> t
  | VerbatimDisk : u8.t -> t
  | DeviceNS : ref OsStr -> t
  | UNC : ref OsStr -> ref OsStr -> t
  | Disk : u8.t -> t
  .
End Prefix.

(* ********CONSTANTS******** *)
(*
[ ] MAIN_SEPARATOR
[ ] MAIN_SEPARATOR_STR
*)

(* ********FUNCTIONS******** *)
(*
[ ] absolute
[ ] is_separator
*)
