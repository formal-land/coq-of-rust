Require Import CoqOfRust.lib.lib.

(* ********STRUCTS******** *)
(*
[x] FileTimes
[x] DirBuilder
[x] DirEntry
[x] File
[x] FileType
[x] Metadata
[x] OpenOptions
[x] Permissions
[x] ReadDir
*)

(* pub struct FileTimes(_); *)
Module FileTimes.
  Parameter t : Set.
End FileTimes.
Definition FileTimes := FileTimes.t.

(* pub struct DirBuilder { /* private fields */ } *)
Module DirBuilder.
  Parameter t : Set.
End DirBuilder.
Definition DirBuilder := DirBuilder.t.

(* pub struct DirEntry(_); *)
Module DirEntry.
  Parameter t : Set.
End DirEntry.
Definition DirEntry := DirEntry.t.

(* pub struct File { /* private fields */ } *)
Module File.
  Parameter t : Set.
End File.
Definition File := File.t.

(* pub struct FileType(_); *)
Module FileType.
  Parameter t : Set.
End FileType.
Definition FileType := FileType.t.

(* pub struct Metadata(_); *)
Module Metadata.
  Parameter t : Set.
End Metadata.
Definition Metadata := Metadata.t.

(* pub struct OpenOptions(_); *)
Module OpenOptions.
  Parameter t : Set.
End OpenOptions.
Definition t : Set := OpenOptions.t.

(* pub struct Permissions(_); *)
Module Permissions.
  Parameter t : Set.
End Permissions.
Definition Permissions := Permissions.t.

(* pub struct ReadDir(_); *)
Module ReadDir.
  Parameter t : Set.
End ReadDir.
Definition ReadDir := ReadDir.t.

(* ********FUNCTIONS******** *)
(*
[ ] try_exists
[ ] canonicalize
[ ] copy
[ ] create_dir
[ ] create_dir_all
[ ] hard_link
[ ] metadata
[ ] read
[ ] read_dir
[ ] read_link
[ ] read_to_string
[ ] remove_dir
[ ] remove_dir_all
[ ] remove_file
[ ] rename
[ ] set_permissions
[x] soft_link(Deprecated)
[ ] symlink_metadata
[ ] write
*)
