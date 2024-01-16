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

  Module Impl.
    Definition Self : Set := t.

    (* pub fn create<P: AsRef<Path>>(path: P) -> Result<File> *)
    Parameter create :
      forall {P : Set},
      P -> M (_std.io.Result t).

    Global Instance AF_create {P : Set} :
      Notations.DoubleColon Self "create" := {
      Notations.double_colon := create (P := P);
    }.

    (* pub fn open<P: AsRef<Path>>(path: P) -> Result<File> *)
    Parameter open :
      forall {P : Set},
      P -> M (_std.io.Result t).

    Global Instance AF_open {P : Set} :
      Notations.DoubleColon Self "open" := {
      Notations.double_colon := open (P := P);
    }.

    Global Instance I_Write : _std.io.Write.Trait Self.
    Admitted.
  End Impl.
End File.

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

  Global Instance AF_new :
    Notations.DoubleColon Self "new" := {
    Notations.double_colon := new;
  }.

  Parameter read :
    mut_ref Self -> bool -> M (mut_ref Self).

  Global Instance AF_read :
    Notations.DoubleColon Self "read" := {
    Notations.double_colon := read;
  }.

  Parameter write :
    mut_ref Self -> bool -> M (mut_ref Self).

  Global Instance AF_write :
    Notations.DoubleColon Self "write" := {
    Notations.double_colon := write;
  }.

  Parameter append :
    mut_ref Self -> bool -> M (mut_ref Self).

  Global Instance AF_append :
    Notations.DoubleColon Self "append" := {
    Notations.double_colon := append;
  }.

  Parameter truncate :
    mut_ref Self -> bool -> M (mut_ref Self).

  Global Instance AF_truncate :
    Notations.DoubleColon Self "truncate" := {
    Notations.double_colon := truncate;
  }.

  Parameter create :
    mut_ref Self -> bool -> M (mut_ref Self).

  Global Instance AF_create :
    Notations.DoubleColon Self "create" := {
    Notations.double_colon := create;
  }.

  Parameter create_new :
    mut_ref Self -> bool -> M (mut_ref Self).

  Global Instance AF_create_new :
    Notations.DoubleColon Self "create_new" := {
    Notations.double_colon := create_new;
  }.

  Parameter open :
    forall {P : Set} (*`{core.convert.AsRef.Trait P _std.path.Path}*),
    ref Self -> P -> M (_std.io.Result File.t).

  Global Instance AF_open {P : Set} :
    Notations.DoubleColon Self "open" := {
    Notations.double_colon := open (P := P);
  }.
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
