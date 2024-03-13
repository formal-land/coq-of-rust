Require Import CoqOfRust.lib.lib.
Require CoqOfRust.core.result.

Module error.
  Module ParseBoolError.
    Parameter t : Set.
  End ParseBoolError.

  Module Utf8Error.
    Parameter t : Set.
  End Utf8Error.
End error.

Module converts.
  (* pub const fn from_utf8(v: &[u8]) -> Result<&str, Utf8Error> *)
  Parameter from_utf8 :
    ref (slice u8.t) ->
    M (result.Result.t (ref str.t) error.Utf8Error.t).
End converts.

Module iter.
  (* pub struct SplitWhitespace<'a> { /* private fields */ } *)
  Module SplitWhitespace.
    Parameter t : Set.
  End SplitWhitespace.

  (* pub struct Chars<'a> { /* private fields */ } *)
  Module Chars.
    Parameter t : Set.
  End Chars.
End iter.

Module Impl.
  Definition Self := str.t.

  (* pub const fn as_bytes(&self) -> &[u8] *)
  Parameter as_bytes : ref Self -> M (ref (slice u8.t)).

  Global Instance AF_as_bytes :
    Notations.DoubleColon Self "as_bytes" := {|
    Notations.double_colon := as_bytes;
  |}.

  (* pub fn chars(&self) -> Chars<'_> *)
  Parameter chars : ref Self -> M (iter.Chars.t).

  Global Instance AF_chars :
    Notations.DoubleColon Self "chars" := {|
    Notations.double_colon := chars;
  |}.

  (* pub fn trim(&self) -> &str *)
  Parameter trim : ref Self -> M (ref Self).

  Global Instance AF_trim :
    Notations.DoubleColon Self "trim" := {|
    Notations.double_colon := trim;
  |}.
End Impl.
