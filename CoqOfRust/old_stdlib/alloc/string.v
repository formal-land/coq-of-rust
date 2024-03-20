Require Import CoqOfRust.lib.lib.

Require CoqOfRust.alloc.borrow.
Require CoqOfRust.core.convert.
Require CoqOfRust.core.fmt.

(* ********TYPE DEFS******** *)
(* 
[ ] ParseError
*)
(* Notations ParseError := Infallible. *)

(* ********STRUCTS******** *)
(* 
[x] Drain
[x] FromUtf8Error
[x] FromUtf16Error
[x] String 
*)

(* pub struct Drain<'a> { /* private fields */ } *)
Module Drain.
  Parameter t : Set.
End Drain.

(* pub struct FromUtf8Error { /* private fields */ } *)
Module FromUtf8Error.
  Parameter t : Set.
End FromUtf8Error.

(* pub struct FromUtf16Error(_); *)
Module FromUtf16Error.
  Parameter t : Set.
End FromUtf16Error.

(* pub struct String { /* private fields */ } *)
Module String.
  Definition t : Set := str.t.

  Module Impl.
    Definition Self : Set := t.

    (* pub const fn new() -> String *)
    Parameter new : M t.

    Global Instance AF_new : Notations.DoubleColon Self "new" := {
      Notations.double_colon := new;
    }.

    (* pub fn len(&self) -> usize *)
    Parameter len : ref Self -> M usize.t.

    Global Instance AF_len : Notations.DoubleColon Self "len" := {
      Notations.double_colon := len;
    }.

    (* pub fn push(&mut self, ch: char) *)
    Parameter push : ref Self -> char.t -> M unit.

    Global Instance AF_push : Notations.DoubleColon Self "push" := {
      Notations.double_colon := push;
    }.

    (* pub fn push_str(&mut self, string: &str) *)
    Parameter push_str : ref Self -> ref str.t -> M unit.

    Global Instance AF_push_str : Notations.DoubleColon Self "push_str" := {
      Notations.double_colon := push_str;
    }.

    (* pub fn from_utf8_lossy(v: &[u8]) -> Cow<'_, str> *)
    Parameter from_utf8_lossy : ref (slice u8.t) -> M (borrow.Cow.t str.t).

    Global Instance AF_from_utf8_lossy :
        Notations.DoubleColon Self "from_utf8_lossy" := {
      Notations.double_colon := from_utf8_lossy;
    }.
  End Impl.
End String.

(* ********TRAITS******** *)
(* 
[x] ToString 
*)

Module ToString.
  Class Trait (Self : Set) : Set := {
    to_string : ref Self -> M String.t;
  }.
End ToString.

(* The String type (Struct std::string::String) and it's methods  *)
Module StringType.
  Definition from (str_from : str.t) : M str.t :=
    M.pure str_from.

  (* The String type (Struct std::string::String) and it's methods  *)
  (* Converts a &str into a String. *)
  Global Instance From_for_str :
      core.convert.From.Trait str.t (T := str.t) := {
    from := from;
  }.

  Global Instance Method_from :
      Notations.DoubleColon String "from" := {
    Notations.double_colon := from;
  }.

 (* @TODO add more methods from (Struct std::string::String) *)
End StringType.

Global Instance Default_for_String :
  core.default.Default.Trait alloc.string.String.t.
Admitted.
