Require Import CoqOfRust.lib.lib.

(* ********TYPE DEFS******** *)
(* ParseError:	A type alias for Infallible. *)
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
  Record t : Set := { }.
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
