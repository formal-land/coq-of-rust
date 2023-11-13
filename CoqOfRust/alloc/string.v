Require Import CoqOfRust.lib.lib.
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
End String.

(* ********TRAITS******** *)
(* 
[x] ToString 
*)

Module ToString.
  Class Trait (Self : Set) : Set := {
    to_string : M.Val (ref Self) -> M (M.Val String.t);
  }.

  Global Instance Method_to_string `(Trait) :
    Notations.Dot "to_string" := {
    Notations.dot := to_string;
  }.
End ToString.

(* The String type (Struct std::string::String) and it's methods  *)
Module StringType.
  Definition from (str_from : M.Val str.t) : M (M.Val str.t) :=
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
