Require Import CoqOfRust.lib.lib.

(* ********STRUCTS******** *)
(* 
[x] EscapeDefault
*)

(* pub struct EscapeDefault { /* private fields */ } *)
Module EscapeDefault.
End EscapeDefault.

(* ********TRAITS******** *)
(* 
[x] AsciiExt
*)

(* 
pub trait AsciiExt {
    type Owned;

    // Required methods
    fn is_ascii(&self) -> bool;
    fn to_ascii_uppercase(&self) -> Self::Owned;
    fn to_ascii_lowercase(&self) -> Self::Owned;
    fn eq_ignore_ascii_case(&self, other: &Self) -> bool;
    fn make_ascii_uppercase(&mut self);
    fn make_ascii_lowercase(&mut self);
}
*)
Module AsciiExt.
  Class Trait (Self : Set) (Owned : Set): Set := {
    is_ascii : ref Self -> bool;
    to_ascii_uppercase : ref Self -> Owned;
    to_ascii_lowercase : ref Self -> Owned;
    eq_ignore_ascii_case : ref Self -> ref Self -> bool;
    make_ascii_uppercase : mut_ref Self -> unit;
    make_ascii_lowercase : mut_ref Self -> unit;
  }.
End AsciiExt.