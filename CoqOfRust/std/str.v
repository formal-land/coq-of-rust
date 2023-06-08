Require Import CoqOfRust.lib.lib.
Require Import CoqOfRust.std.option.


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
  [ ] DoubleEndedSearcher
  [ ] Pattern
  [ ] ReverseSearcher
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
  

  (* BUGGED: type with type definition *)
  (* NOTE: Sized trait ignored *)
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

  (* 
  pub unsafe trait ReverseSearcher<'a>: Searcher<'a> {
    // Required method
    fn next_back(&mut self) -> SearchStep;

    // Provided methods
    fn next_match_back(&mut self) -> Option<(usize, usize)> { ... }
    fn next_reject_back(&mut self) -> Option<(usize, usize)> { ... }
  }
  *)

  (* pub trait DoubleEndedSearcher<'a>: ReverseSearcher<'a> { } *)
  Module DoubleEndedSearcher.
    Class Trait (Self : Set) `{ReverseSearcher.Trait Self} : Set := { }.
  End DoubleEndedSearcher.
  
End pattern.

(* ********STRUCTS******** *)
(*
[ ] Utf8Chunk
[ ] Utf8Chunks
[ ] Bytes
[ ] CharIndices
[ ] Chars
[ ] EncodeUtf16
[ ] EscapeDebug
[ ] EscapeDefault
[ ] EscapeUnicode
[ ] Lines
[x] LinesAny(Deprecated)
[ ] MatchIndices
[ ] Matches
[ ] ParseBoolError
[ ] RMatchIndices
[ ] RMatches
[ ] RSplit
[ ] RSplitN
[ ] RSplitTerminator
[ ] Split
[ ] SplitAsciiWhitespace
[ ] SplitInclusive
[ ] SplitN
[ ] SplitTerminator
[ ] SplitWhitespace
[ ] Utf8Error
*)

(* ********TRAITS******** *)
(*
[ ] FromStr
*)

(* ********FUNCTIONS******** *)
(*
[ ] from_boxed_utf8_unchecked
[ ] from_utf8
[ ] from_utf8_mut
[ ] from_utf8_unchecked
[ ] from_utf8_unchecked_mut
*)
