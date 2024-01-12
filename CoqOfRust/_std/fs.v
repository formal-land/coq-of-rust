Require Import CoqOfRust.lib.lib.
Require CoqOfRust.core.convert.
Require CoqOfRust._std.io.
Require CoqOfRust._std.path.

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

(* pub struct DirBuilder { /* private fields */ } *)
Module DirBuilder.
  Parameter t : Set.
End DirBuilder.

(* pub struct DirEntry(_); *)
Module DirEntry.
  Parameter t : Set.
End DirEntry.

(* pub struct File { /* private fields */ } *)
Module File.
  Parameter t : Set.
End File.

Module Impl_Write_for_File.
  Global Instance I : _std.io.Write.Trait File.t.
  Admitted.
End Impl_Write_for_File.

(* pub struct FileType(_); *)
Module FileType.
  Parameter t : Set.
End FileType.

(* pub struct Metadata(_); *)
Module Metadata.
  Parameter t : Set.
End Metadata.

(* pub struct OpenOptions(_); *)
Module OpenOptions.
  Parameter t : Set.
End OpenOptions.

Module Impl_OpenOptions.
  Definition Self := OpenOptions.t.

  Parameter new : M Self.

  Global Instance AssociatedFunction_new :
    Notations.DoubleColon Self "new" := {
    Notations.double_colon := new;
  }.

  Parameter read :
    mut_ref Self -> bool -> M (mut_ref Self).

  Parameter write :
    mut_ref Self -> bool -> M (mut_ref Self).

  Parameter append :
    mut_ref Self -> bool -> M (mut_ref Self).

  Parameter truncate :
    mut_ref Self -> bool -> M (mut_ref Self).

  Parameter create :
    mut_ref Self -> bool -> M (mut_ref Self).

  Parameter create_new :
    mut_ref Self -> bool -> M (mut_ref Self).

  Parameter open :
    forall {P : Set} (*`{core.convert.AsRef.Trait P _std.path.Path}*),
    ref Self -> P -> M (_std.io.Result File.t).
End Impl_OpenOptions.

(* pub struct Permissions(_); *)
Module Permissions.
  Parameter t : Set.
End Permissions.

(* pub struct ReadDir(_); *)
Module ReadDir.
  Parameter t : Set.
End ReadDir.

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
