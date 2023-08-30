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

  Parameter new : forall `{H : State.Trait}, M (H := H) Self.

  Global Instance AssociatedFunction_new `{H : State.Trait} :
    Notation.DoubleColon Self "new" := {
    Notation.double_colon := new;
  }.

  Parameter read :
    forall `{H : State.Trait},
    mut_ref Self -> bool -> M (H := H) (mut_ref Self).

  Global Instance Method_read `{H : State.Trait} :
    Notation.Dot "read" := {
    Notation.dot := read;
  }.

  Parameter write :
    forall `{H : State.Trait},
    mut_ref Self -> bool -> M (H := H) (mut_ref Self).

  Global Instance Method_write `{H : State.Trait} :
    Notation.Dot "write" := {
    Notation.dot := write;
  }.

  Parameter append :
    forall `{H : State.Trait},
    mut_ref Self -> bool -> M (H := H) (mut_ref Self).

  Global Instance Method_append `{H : State.Trait} :
    Notation.Dot "append" := {
    Notation.dot := append;
  }.

  Parameter truncate :
    forall `{H : State.Trait},
    mut_ref Self -> bool -> M (H := H) (mut_ref Self).

  Global Instance Method_truncate `{H : State.Trait} :
    Notation.Dot "truncate" := {
    Notation.dot := truncate;
  }.

  Parameter create :
    forall `{H : State.Trait},
    mut_ref Self -> bool -> M (H := H) (mut_ref Self).

  Global Instance Method_create `{H : State.Trait} :
    Notation.Dot "create" := {
    Notation.dot := create;
  }.

  Parameter create_new :
    forall `{H : State.Trait},
    mut_ref Self -> bool -> M (H := H) (mut_ref Self).

  Global Instance Method_create_new `{H : State.Trait} :
    Notation.Dot "create_new" := {
    Notation.dot := create_new;
  }.

  Parameter open :
    forall `{H : State.Trait}
      {P : Set} (*`{core.convert.AsRef.Trait P _std.path.Path}*),
    ref Self -> P -> M (H := H) (_std.io.Result File).

  Global Instance Method_open `{H : State.Trait}
      {P : Set} (*`{core.convert.AsRef.Trait P _std.path.Path}*) :
    Notation.Dot "open" := {
    Notation.dot := open (P := P);
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
