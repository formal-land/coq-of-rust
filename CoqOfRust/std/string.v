Require Import CoqOfRust.lib.lib.
Require Import CoqOfRust.std.convert.

(* ********TYPE DEFS******** *)
(* 
[ ] ParseError
*)
(* Notation ParseError := Infallible. *)

(* ********STRUCTS******** *)
(* 
[x] Drain
[x] FromUtf8Error
[x] FromUtf16Error
[x] String 
*)

(* pub struct Drain<'a> { /* private fields */ } *)
Module Drain.
  Record t : Set := { }.
End Drain.
Definition Drain := Drain.t.

(* pub struct FromUtf8Error { /* private fields */ } *)
Module FromUtf8Error.
  Record t : Set := { }.
End FromUtf8Error.
Definition FromUtf8Error := FromUtf8Error.t.

(* pub struct FromUtf16Error(_); *)
Module FromUtf16Error.
  Record t (underscore : Set): Set := { }.
End FromUtf16Error.
Definition FromUtf16Error := FromUtf16Error.t.

(* pub struct String { /* private fields */ } *)
Module String.
  Definition t : Set := str.
End String.
Definition String := String.t.

(* ********TRAITS******** *)
(* 
[x] ToString 
*)

Module ToString.
  Class Trait (Self : Set) : Set := {
    to_string : ref Self -> String;
  }.

  Global Instance Method_to_string `(Trait) : Notation.Dot "to_string" := {
    Notation.dot := to_string;
  }.
End ToString.

(* The String type (Struct std::string::String) and it's methods  *)
Module StringType.
  Definition from (str_from: str) : String := str_from.

  (* The String type (Struct std::string::String) and it's methods  *)
  (* Converts a &str into a String. *)
  Global Instance FromStr : From.Trait str String := {
    from := from;
  }.

 Global Instance Method_from : Notation.DoubleColon String "from" := {
    Notation.double_colon := from;
  }.

 (* @TODO add more methods from (Struct std::string::String) *)
 
End StringType.
