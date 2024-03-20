Require Import CoqOfRust.lib.lib.
(* Require Import CoqOfRust.std.iter. *)


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
  Parameter t : Set.
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
  Parameter t : Set -> Set.
End DecodeUtf16.
Definition DecodeUtf16 := DecodeUtf16.t.

(* pub struct DecodeUtf16Error { /* private fields */ } *)
Module DecodeUtf16Error.
  Parameter t : Set.
End DecodeUtf16Error.
Definition DecodeUtf16Error := DecodeUtf16Error.t.

(* pub struct EscapeDebug(_); *)
Module EscapeDebug.
  Parameter t : Set.
End EscapeDebug.
Definition EscapeDebug := EscapeDebug.t.

(* pub struct EscapeDefault { /* private fields */ } *)
Module EscapeDefault.
  Parameter t : Set.
End EscapeDefault.
Definition EscapeDefault := EscapeDefault.t.

(* pub struct EscapeUnicode { /* private fields */ } *)
Module EscapeUnicode.
  Parameter t : Set.
End EscapeUnicode.
Definition EscapeUnicode := EscapeUnicode.t.

(* pub struct ParseCharError { /* private fields */ } *)
Module ParseCharError.
  Parameter t : Set.
End ParseCharError.
Definition ParseCharError := ParseCharError.t.

(* pub struct ToLowercase(_); *)
Module ToLowercase.
  Parameter t : Set.
End ToLowercase.
Definition ToLowercase := ToLowercase.t.

(* pub struct ToUppercase(_); *)
Module ToUppercase.
  Parameter t : Set.
End ToUppercase.
Definition ToUppercase := ToUppercase.t.

(* pub struct TryFromCharError(_); *)
Module TryFromCharError.
  Parameter t : Set.
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

