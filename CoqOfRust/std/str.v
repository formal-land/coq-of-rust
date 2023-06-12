Require Import CoqOfRust.lib.lib.

Require Import CoqOfRust.std.option.
Require Import CoqOfRust.std.result.

(* ********MODULES******** *)
(*
[x] pattern
*)
Module pattern.
  (* ********STRUCTS******** *)
  (*
  [x] CharArrayRefSearcher
  [?] CharArraySearcher
  [x] CharPredicateSearcher
  [x] CharSearcher
  [x] CharSliceSearcher
  [x] StrSearcher
  *)

  (* pub struct CharArraySearcher<'a, const N: usize>(_); *)
  Module CharArraySearcher.
    Record t (N : usize) : Set := { }.
  End CharArraySearcher.
  Definition CharArraySearcher := CharArraySearcher.t.

  (* BUGGED: monad function dependency *)
  (* 
  pub struct CharPredicateSearcher<'a, F>(_)
  where
          F: FnMut(char) -> bool;
  *)
  Module CharPredicateSearcher.
    Record t (F : Set) : Set := { }.
  End CharPredicateSearcher.
  Definition CharPredicateSearcher := CharPredicateSearcher.t.
  
  (* pub struct CharSearcher<'a> { /* private fields */ } *)
  Module CharSearcher.
    Record t : Set := { }.
  End CharSearcher.
  Definition CharSearcher := CharSearcher.t.

  (* pub struct CharSliceSearcher<'a, 'b>(_); *)
  Module CharSliceSearcher.
    Record t : Set := { }.
  End CharSliceSearcher.
  Definition CharSliceSearcher := CharSliceSearcher.t.
  
  (* pub struct StrSearcher<'a, 'b> { /* private fields */ } *)
  Module StrSearcher.
    Record t : Set := { }.
  End StrSearcher.
  Definition StrSearcher := StrSearcher.t.
  
  
  (* ********ENUMS******** *)
  (*
  [x] SearchStep
  *)

  (* 
  pub enum SearchStep {
    Match(usize, usize),
    Reject(usize, usize),
    Done,
  }
  *)
  Module SearchStep.
    Inductive t : Set := 
    | Match: usize -> usize -> t
    | Reject: usize -> usize -> t
    | Done : t
    .
  End SearchStep.
  Definition SearchStep := SearchStep.t.

  (* ********TRAITS******** *)
  (*
  [x] DoubleEndedSearcher
  [x] Pattern
  [x] ReverseSearcher
  [x] Searcher
  *)

  (* 
  pub unsafe trait Searcher<'a> {
    // Required methods
    fn haystack(&self) -> &'a str;
    fn next(&mut self) -> SearchStep;

    // Provided methods
    fn next_match(&mut self) -> Option<(usize, usize)> { ... }
    fn next_reject(&mut self) -> Option<(usize, usize)> { ... }
  }
  *)
  Module Searcher.
    Class Trait (Self : Set) : Set := { 
      haystack : ref Self -> ref str;
      next : mut_ref Self -> SearchStep;
      next_match : mut_ref Self -> Option (usize * usize);
      next_reject : mut_ref Self -> Option (usize * usize);
    }.
  End Searcher.

  (* 
  pub unsafe trait ReverseSearcher<'a>: Searcher<'a> {
    // Required method
    fn next_back(&mut self) -> SearchStep;

    // Provided methods
    fn next_match_back(&mut self) -> Option<(usize, usize)> { ... }
    fn next_reject_back(&mut self) -> Option<(usize, usize)> { ... }
  }
  *)
  Module ReverseSearcher.
    Class Trait (Self : Set) 
      `{Searcher.Trait Self} : Set := { 
        next_back : mut_ref Self -> SearchStep;
        next_match_back : mut_ref Self -> Option (usize * usize);
        next_reject_back : mut_ref Self -> Option (usize * usize);
      }.
  End ReverseSearcher.
  
  (* BUGGED: type with type definition *)
  (* 
  pub trait Pattern<'a>: Sized {
    type Searcher: Searcher<'a>;

    // Required method
    fn into_searcher(self, haystack: &'a str) -> Self::Searcher;

    // Provided methods
    fn is_contained_in(self, haystack: &'a str) -> bool { ... }
    fn is_prefix_of(self, haystack: &'a str) -> bool { ... }
    fn is_suffix_of(self, haystack: &'a str) -> bool
       where Self::Searcher: ReverseSearcher<'a> { ... }
    fn strip_prefix_of(self, haystack: &'a str) -> Option<&'a str> { ... }
    fn strip_suffix_of(self, haystack: &'a str) -> Option<&'a str>
       where Self::Searcher: ReverseSearcher<'a> { ... }
  }
  *)
  Module Pattern.
    Class Trait (Self Searcher : Set) : Set := { 
      Searcher := Searcher;

      into_searcher : Self -> ref str -> Searcher;
      is_contained_in : Self -> ref str -> bool;
      is_prefix_of : Self -> ref str -> bool;
      is_suffix_of `{ReverseSearcher.Trait Searcher} : Self -> ref str -> bool;
      strip_prefix_of : Self -> ref str -> Option (ref str);
      strip_suffix_of `{ReverseSearcher.Trait Searcher} : Self -> ref str -> Option (ref str);
    }.
  End Pattern.

  (* pub trait DoubleEndedSearcher<'a>: ReverseSearcher<'a> { } *)
  Module DoubleEndedSearcher.
    Class Trait (Self : Set) `{ReverseSearcher.Trait Self} : Set := { }.
  End DoubleEndedSearcher.
  
End pattern.

Import pattern.

(* ********STRUCTS******** *)
(*
[x] Utf8Chunk
[x] Utf8Chunks
[x] Bytes
[x] CharIndices
[x] Chars
[x] EncodeUtf16
[x] EscapeDebug
[x] EscapeDefault
[x] EscapeUnicode
[x] Lines
[x] LinesAny(Deprecated)
[x] MatchIndices
[x] Matches
[x] ParseBoolError
[x] RMatchIndices
[x] RMatches
[x] RSplit
[x] RSplitN
[x] RSplitTerminator
[x] Split
[x] SplitAsciiWhitespace
[x] SplitInclusive
[x] SplitN
[x] SplitTerminator
[x] SplitWhitespace
[x] Utf8Error
*)

(* pub struct Utf8Chunk<'a> { /* private fields */ } *)
Module Utf8Chunk.
  Record t : Set := { }.
End Utf8Chunk.
Definition Utf8Chunk := Utf8Chunk.t.

(* pub struct Utf8Chunks<'a> { /* private fields */ } *)
Module Utf8Chunks.
  Record t : Set := { }.
End Utf8Chunks.
Definition Utf8Chunks := Utf8Chunks.t.

(* pub struct Bytes<'a>(_); *)
Module Bytes.
  Record t : Set := { }.
End Bytes.
Definition Bytes := Bytes.t.

(* pub struct CharIndices<'a> { /* private fields */ } *)
Module CharIndices.
  Record t : Set := { }.
End CharIndices.
Definition CharIndices := CharIndices.t.

(* pub struct Chars<'a> { /* private fields */ } *)
Module Chars.
  Record t : Set := { }.
End Chars.
Definition Chars := Chars.t.

(* pub struct EncodeUtf16<'a> { /* private fields */ } *)
Module EncodeUtf16.
  Record t : Set := { }.
End EncodeUtf16.
Definition EncodeUtf16 := EncodeUtf16.t.

(* pub struct EscapeDebug<'a> { /* private fields */ } *)
Module EscapeDebug.
  Record t : Set := { }.
End EscapeDebug.
Definition EscapeDebug := EscapeDebug.t.

(* pub struct EscapeDefault<'a> { /* private fields */ } *)
Module EscapeDefault.
  Record t : Set := { }.
End EscapeDefault.
Definition EscapeDefault := EscapeDefault.t.

(* pub struct EscapeUnicode<'a> { /* private fields */ } *)
Module EscapeUnicode.
  Record t : Set := { }.
End EscapeUnicode.
Definition EscapeUnicode := EscapeUnicode.t.

(* pub struct Lines<'a>(_); *)
Module Lines.
  Record t : Set := { }.
End Lines.
Definition Lines := Lines.t.

(* NOTE: LinesAny deprecated *)

(* 
pub struct MatchIndices<'a, P>(_)
where
         P: Pattern<'a>;
*)
Module MatchIndices.
  Record t (P : Set) `{Pattern.Trait P} : Set := { }.
End MatchIndices.
Definition MatchIndices := MatchIndices.t.

(* 
pub struct Matches<'a, P>(_)
where
         P: Pattern<'a>;
*)
Module Matches.
  Record t (P : Set) `{Pattern.Trait P} : Set := { }.
End Matches.
Definition Matches := Matches.t.

(* pub struct ParseBoolError; *)
Module ParseBoolError.
  Record t : Set := { }.
End ParseBoolError.
Definition ParseBoolError := ParseBoolError.t.

(* 
pub struct RMatchIndices<'a, P>(_)
where
         P: Pattern<'a>;
*)
Module RMatchIndices.
  Record t (P : Set) `{Pattern.Trait P} : Set := { }.
End RMatchIndices.
Definition RMatchIndices := RMatchIndices.t.

(* 
pub struct RMatches<'a, P>(_)
where
         P: Pattern<'a>;
*)
Module RMatches.
  Record t (P : Set) `{Pattern.Trait P} : Set := { }.
End RMatches.
Definition RMatches := RMatches.t.

(* 
pub struct RSplit<'a, P>(_)
where
         P: Pattern<'a>;
*)
Module RSplit.
  Record t (P : Set) `{Pattern.Trait P} : Set := { }.
End RSplit.
Definition RSplit := RSplit.t.

(* 
pub struct RSplitN<'a, P>(_)
where
         P: Pattern<'a>;
*)
Module RSplitN.
  Record t (P : Set) `{Pattern.Trait P} : Set := { }.
End RSplitN.
Definition RSplitN := RSplitN.t.

(* 
pub struct RSplitTerminator<'a, P>(_)
where
         P: Pattern<'a>;
*)
Module RSplitTerminator.
  Record t (P : Set) `{Pattern.Trait P} : Set := { }.
End RSplitTerminator.
Definition RSplitTerminator := RSplitTerminator.t.

(* 
pub struct Split<'a, P>(_)
where
         P: Pattern<'a>;
*)
Module Split.
  Record t (P : Set) `{Pattern.Trait P} : Set := { }.
End Split.
Definition Split := Split.t.

(* pub struct SplitAsciiWhitespace<'a> { /* private fields */ } *)
Module SplitAsciiWhitespace.
  Record t : Set := { }.
End SplitAsciiWhitespace.
Definition SplitAsciiWhitespace := SplitAsciiWhitespace.t.

(* 
pub struct SplitInclusive<'a, P>(_)
where
         P: Pattern<'a>;
*)
Module SplitInclusive.
  Record t (P : Set) `{Pattern.Trait P} : Set := { }.
End SplitInclusive.
Definition SplitInclusive := SplitInclusive.t.

(* 
pub struct SplitN<'a, P>(_)
where
         P: Pattern<'a>;
*)
Module SplitN.
  Record t (P : Set) `{Pattern.Trait P} : Set := { }.
End SplitN.
Definition SplitN := SplitN.t.


(* 
pub struct SplitTerminator<'a, P>(_)
where
         P: Pattern<'a>;
*)
Module SplitTerminator.
  Record t (P : Set) `{Pattern.Trait P} : Set := { }.
End SplitTerminator.
Definition SplitTerminator := SplitTerminator.t.


(* pub struct SplitWhitespace<'a> { /* private fields */ } *)
Module SplitWhitespace.
  Record t : Set := { }.
End SplitWhitespace.
Definition SplitWhitespace := SplitWhitespace.t.

(* pub struct Utf8Error { /* private fields */ } *)
Module Utf8Error.
  Record t : Set := { }.
End Utf8Error.
Definition Utf8Error := Utf8Error.t.

(* ********TRAITS******** *)
(*
[x] FromStr
*)
(* 
pub trait FromStr: Sized {
    type Err;

    // Required method
    fn from_str(s: &str) -> Result<Self, Self::Err>;
}
*)
Module FromStr.
  Class Trait (Self Err : Set) : Set := { 
    Err := Err;
    from_str : ref str -> Result Self Err;
  }.
End FromStr.


(* ********FUNCTIONS******** *)
(*
[ ] from_boxed_utf8_unchecked
[ ] from_utf8
[ ] from_utf8_mut
[ ] from_utf8_unchecked
[ ] from_utf8_unchecked_mut
*)
