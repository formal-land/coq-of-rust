Require Import CoqOfRust.lib.lib.

Require Import CoqOfRust.std.ffi.

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
  Record t : Set := { }.
End Ancestors.
Definition Ancestors := Ancestors.t.

(* pub struct Components<'a> { /* private fields */ } *)
Module Components.
  Record t : Set := { }.
End Components.
Definition Components := Components.t.

(* pub struct Display<'a> { /* private fields */ } *)
Module Display.
  Record t : Set := { }.
End Display.
Definition Display := Display.t.

(* pub struct Iter<'a> { /* private fields */ } *)
Module Iter.
  Record t : Set := { }.
End Iter.
Definition Iter := Iter.t.

(* pub struct Path { /* private fields */ } *)
Module Path.
  Record t : Set := { }.
End Path.
Definition Path := Path.t.

(* pub struct PathBuf { /* private fields */ } *)
Module PathBuf.
  Record t : Set := { }.
End PathBuf.
Definition PathBuf := PathBuf.t.

(* pub struct PrefixComponent<'a> { /* private fields */ } *)
Module PrefixComponent.
  Record t : Set := { }.
End PrefixComponent.
Definition PrefixComponent := PrefixComponent.t.

(* pub struct StripPrefixError(_); *)
Module StripPrefixError.
  Record t : Set := { }.
End StripPrefixError.
Definition StripPrefixError := StripPrefixError.t.


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
  | Prefix : PrefixComponent -> t
  | RootDir : t
  | CurDir : t
  | ParentDir : t
  | Normal : ref OsStr -> t
  .
End Component.
Definition Component := Component.t.

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
  | VerbatimDisk : u8 -> t
  | DeviceNS : ref OsStr -> t
  | UNC : ref OsStr -> ref OsStr -> t
  | Disk : u8 -> t
  .
End Prefix.
Definition Prefix := Prefix.t.

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
