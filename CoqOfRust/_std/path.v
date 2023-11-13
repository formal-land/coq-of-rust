Require Import CoqOfRust.lib.lib.

Require Import CoqOfRust._std.ffi.

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

(* pub struct Path { /* private fields */ } *)
Module Path.
  Parameter t : Set.
End Path.

(* pub struct PathBuf { /* private fields */ } *)
Module PathBuf.
  Parameter t : Set.
End PathBuf.

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
