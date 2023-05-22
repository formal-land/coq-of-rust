Require Import CoqOfRust.lib.lib.
Require Import CoqOfRust.std.convert.

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
  Global Instance FromStr : From str String := {
    from := from;
  }.

 Global Instance Method_from : Notation.DoubleColon String "from" := {
    Notation.double_colon := from;
  }.

 (* @TODO add more methods from (Struct std::string::String) *)
 
End StringType.
