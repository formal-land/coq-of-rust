Require Import CoqOfRust.lib.lib.
(* Require Import CoqOfRust._std.iter. *)


(* ********STRUCTS******** *)
(* 
[x] CharTryFromError
[?] DecodeUtf16
[x] DecodeUtf16Error
[x] EscapeDebug
[x] EscapeDefault
[x] EscapeUnicode
[x] ParseCharError
[x] ToLowercase
[x] ToUppercase
[x] TryFromCharError
*)

(* pub struct CharTryFromError(_); *)
Module CharTryFromError.
  Record t : Set := { }.
End CharTryFromError.
Definition CharTryFromError := CharTryFromError.t.

(* BUGGED: Iterator dependency *)
(* 
pub struct DecodeUtf16<I>
where
    I: Iterator<Item = u16>,
{ /* private fields */ }
*)
Module DecodeUtf16.
  Record t (I : Set) : Set := { }.
End DecodeUtf16.
Definition DecodeUtf16 := DecodeUtf16.t.

(* pub struct DecodeUtf16Error { /* private fields */ } *)
Module DecodeUtf16Error.
  Record t : Set := { }.
End DecodeUtf16Error.
Definition DecodeUtf16Error := DecodeUtf16Error.t.

(* pub struct EscapeDebug(_); *)
Module EscapeDebug.
  Record t : Set := { }.
End EscapeDebug.
Definition EscapeDebug := EscapeDebug.t.

(* pub struct EscapeDefault { /* private fields */ } *)
Module EscapeDefault.
  Record t : Set := { }.
End EscapeDefault.
Definition EscapeDefault := EscapeDefault.t.

(* pub struct EscapeUnicode { /* private fields */ } *)
Module EscapeUnicode.
  Record t : Set := { }.
End EscapeUnicode.
Definition EscapeUnicode := EscapeUnicode.t.

(* pub struct ParseCharError { /* private fields */ } *)
Module ParseCharError.
  Record t : Set := { }.
End ParseCharError.
Definition ParseCharError := ParseCharError.t.

(* pub struct ToLowercase(_); *)
Module ToLowercase.
  Record t : Set := { }.
End ToLowercase.
Definition ToLowercase := ToLowercase.t.

(* pub struct ToUppercase(_); *)
Module ToUppercase.
  Record t : Set := { }.
End ToUppercase.
Definition ToUppercase := ToUppercase.t.

(* pub struct TryFromCharError(_); *)
Module TryFromCharError.
  Record t : Set := { }.
End TryFromCharError.
Definition TryFromCharError := TryFromCharError.t.

(* ********CONSTANTS******** *)
(* 
[ ] MAX
[ ] REPLACEMENT_CHARACTER
[ ] UNICODE_VERSION
*)

(* ********FUNCTIONS******** *)
(* 
[ ] decode_utf16
[ ] from_digit
[ ] from_u32
[ ] from_u32_unchecked
*)

