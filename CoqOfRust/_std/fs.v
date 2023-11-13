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

Module Impl_Write_for_File.
  Global Instance I : _std.io.Write.Trait File.
  Admitted.
End Impl_Write_for_File.

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
Definition OpenOptions : Set := OpenOptions.t.

Module Impl_OpenOptions.
  Definition Self := OpenOptions.

  Parameter new : M Self.

  Global Instance AssociatedFunction_new :
    Notations.DoubleColon Self "new" := {
    Notations.double_colon := new;
  }.

  Parameter read :
    mut_ref Self -> bool -> M (mut_ref Self).

  Global Instance Method_read :
    Notations.Dot "read" := {
    Notations.dot := read;
  }.

  Parameter write :
    mut_ref Self -> bool -> M (mut_ref Self).

  Global Instance Method_write :
    Notations.Dot "write" := {
    Notations.dot := write;
  }.

  Parameter append :
    mut_ref Self -> bool -> M (mut_ref Self).

  Global Instance Method_append :
    Notations.Dot "append" := {
    Notations.dot := append;
  }.

  Parameter truncate :
    mut_ref Self -> bool -> M (mut_ref Self).

  Global Instance Method_truncate :
    Notations.Dot "truncate" := {
    Notations.dot := truncate;
  }.

  Parameter create :
    mut_ref Self -> bool -> M (mut_ref Self).

  Global Instance Method_create :
    Notations.Dot "create" := {
    Notations.dot := create;
  }.

  Parameter create_new :
    mut_ref Self -> bool -> M (mut_ref Self).

  Global Instance Method_create_new :
    Notations.Dot "create_new" := {
    Notations.dot := create_new;
  }.

  Parameter open :
    forall {P : Set} (*`{core.convert.AsRef.Trait P _std.path.Path}*),
    ref Self -> P -> M (_std.io.Result File).

  Global Instance Method_open {P : Set}
      (*`{core.convert.AsRef.Trait P _std.path.Path}*) :
    Notations.Dot "open" := {
    Notations.dot := open (P := P);
  }.
End Impl_OpenOptions.

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
