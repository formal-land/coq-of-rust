Require Import CoqOfRust.lib.lib.
Require CoqOfRust.core.option.
Require CoqOfRust.core.result.
Require CoqOfRust.core.str.

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
    Parameter t : Z -> Set.
  End CharArraySearcher.
  Definition CharArraySearcher := CharArraySearcher.t.

  (* BUGGED: monad function dependency *)
  (* 
  pub struct CharPredicateSearcher<'a, F>(_)
  where
          F: FnMut(char) -> bool;
  *)
  Module CharPredicateSearcher.
    Parameter t : Set -> Set.
  End CharPredicateSearcher.
  Definition CharPredicateSearcher := CharPredicateSearcher.t.
  
  (* pub struct CharSearcher<'a> { /* private fields */ } *)
  Module CharSearcher.
    Parameter t : Set.
  End CharSearcher.
  Definition CharSearcher := CharSearcher.t.

  (* pub struct CharSliceSearcher<'a, 'b>(_); *)
  Module CharSliceSearcher.
    Parameter t : Set.
  End CharSliceSearcher.
  Definition CharSliceSearcher := CharSliceSearcher.t.
  
  (* pub struct StrSearcher<'a, 'b> { /* private fields */ } *)
  Module StrSearcher.
    Parameter t : Set.
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
    | Match: usize.t -> usize.t -> t
    | Reject: usize.t -> usize.t -> t
    | Done : t
    .
  End SearchStep.

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
      haystack :
        M.Val (ref Self) ->
        M (M.Val (ref str.t));
      next :
        M.Val (mut_ref Self) ->
        M (M.Val SearchStep.t);
      next_match :
        M.Val (mut_ref Self) ->
        M (M.Val (option.Option.t (usize.t * usize.t)));
      next_reject :
        M.Val (mut_ref Self) ->
        M (M.Val (option.Option.t (usize.t * usize.t)));
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
        next_back : mut_ref Self -> SearchStep.t;
        next_match_back : mut_ref Self -> option.Option.t (usize.t * usize.t);
        next_reject_back : mut_ref Self -> option.Option.t (usize.t * usize.t);
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

      into_searcher : Self -> ref str.t -> Searcher;
      is_contained_in : Self -> ref str.t -> bool;
      is_prefix_of : Self -> ref str.t -> bool;
      is_suffix_of `{ReverseSearcher.Trait Searcher} : Self -> ref str.t -> bool;
      strip_prefix_of : Self -> ref str.t -> option.Option.t (ref str.t);
      strip_suffix_of `{ReverseSearcher.Trait Searcher} : Self -> ref str.t -> option.Option.t (ref str.t);
    }.
  End Pattern.

  (* pub trait DoubleEndedSearcher<'a>: ReverseSearcher<'a> { } *)
  Module DoubleEndedSearcher.
    Unset Primitive Projections.
    Class Trait (Self : Set) `{ReverseSearcher.Trait Self} : Set := { }.
    Set Primitive Projections.
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
  Parameter t : Set.
End Utf8Chunk.

(* pub struct Utf8Chunks<'a> { /* private fields */ } *)
Module Utf8Chunks.
  Parameter t : Set.
End Utf8Chunks.

(* pub struct Bytes<'a>(_); *)
Module Bytes.
  Parameter t : Set.
End Bytes.

(* pub struct CharIndices<'a> { /* private fields */ } *)
Module CharIndices.
  Parameter t : Set.
End CharIndices.

(* pub struct Chars<'a> { /* private fields */ } *)
Module Chars.
  Parameter t : Set.
End Chars.

(* pub struct EncodeUtf16<'a> { /* private fields */ } *)
Module EncodeUtf16.
  Parameter t : Set.
End EncodeUtf16.

(* pub struct EscapeDebug<'a> { /* private fields */ } *)
Module EscapeDebug.
  Parameter t : Set.
End EscapeDebug.

(* pub struct EscapeDefault<'a> { /* private fields */ } *)
Module EscapeDefault.
  Parameter t : Set.
End EscapeDefault.

(* pub struct EscapeUnicode<'a> { /* private fields */ } *)
Module EscapeUnicode.
  Parameter t : Set.
End EscapeUnicode.

(* pub struct Lines<'a>(_); *)
Module Lines.
  Parameter t : Set.
End Lines.

(* NOTE: LinesAny deprecated *)

(* 
pub struct MatchIndices<'a, P>(_)
where
         P: Pattern<'a>;
*)
Module MatchIndices.
  Parameter t : forall (P : Set) `{Pattern.Trait P}, Set.
End MatchIndices.

(* 
pub struct Matches<'a, P>(_)
where
         P: Pattern<'a>;
*)
Module Matches.
  Parameter t : forall (P : Set) `{Pattern.Trait P}, Set.
End Matches.

(* 
pub struct RMatchIndices<'a, P>(_)
where
         P: Pattern<'a>;
*)
Module RMatchIndices.
  Parameter t : forall (P : Set) `{Pattern.Trait P}, Set.
End RMatchIndices.

(* 
pub struct RMatches<'a, P>(_)
where
         P: Pattern<'a>;
*)
Module RMatches.
  Parameter t : forall (P : Set) `{Pattern.Trait P}, Set.
End RMatches.

(* 
pub struct RSplit<'a, P>(_)
where
         P: Pattern<'a>;
*)
Module RSplit.
  Parameter t : forall (P : Set) `{Pattern.Trait P}, Set.
End RSplit.

(* 
pub struct RSplitN<'a, P>(_)
where
         P: Pattern<'a>;
*)
Module RSplitN.
  Parameter t : forall (P : Set) `{Pattern.Trait P}, Set.
End RSplitN.

(* 
pub struct RSplitTerminator<'a, P>(_)
where
         P: Pattern<'a>;
*)
Module RSplitTerminator.
  Parameter t : forall (P : Set) `{Pattern.Trait P}, Set.
End RSplitTerminator.

(* 
pub struct Split<'a, P>(_)
where
         P: Pattern<'a>;
*)
Module Split.
  Parameter t : forall (P : Set) `{Pattern.Trait P}, Set.
End Split.

(* pub struct SplitAsciiWhitespace<'a> { /* private fields */ } *)
Module SplitAsciiWhitespace.
  Parameter t : Set.
End SplitAsciiWhitespace.

(* 
pub struct SplitInclusive<'a, P>(_)
where
         P: Pattern<'a>;
*)
Module SplitInclusive.
  Parameter t : forall (P : Set) `{Pattern.Trait P}, Set.
End SplitInclusive.

(* 
pub struct SplitN<'a, P>(_)
where
         P: Pattern<'a>;
*)
Module SplitN.
  Parameter t : forall (P : Set) `{Pattern.Trait P}, Set.
End SplitN.

(* 
pub struct SplitTerminator<'a, P>(_)
where
         P: Pattern<'a>;
*)
Module SplitTerminator.
  Parameter t : forall (P : Set) `{Pattern.Trait P}, Set.
End SplitTerminator.


(* pub struct SplitWhitespace<'a> { /* private fields */ } *)
Module SplitWhitespace.
  Parameter t : Set.
End SplitWhitespace.

(* pub struct Utf8Error { /* private fields */ } *)
Module Utf8Error.
  Parameter t : Set.
End Utf8Error.

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
  Class Trait (Self : Set) : Type := { 
    Err : Set;
    from_str :
      ref str.t ->
      M (result.Result.t Self Err);
  }.
End FromStr.

Module FromStr_instances.
  #[refine]
  Global Instance for_bool : FromStr.Trait bool := {
    Err := str.error.ParseBoolError;
  }.
    all: destruct (axiom "FromStr_instances" : Empty_set).
  Defined.

  Global Instance for_char : FromStr.Trait char.t.
  Admitted.

  Global Instance for_f32 : FromStr.Trait f32.t.
  Admitted.

  Global Instance for_f64 : FromStr.Trait f64.t.
  Admitted.

  Global Instance for_i8 : FromStr.Trait i8.t.
  Admitted.

  Global Instance for_i16 : FromStr.Trait i16.t.
  Admitted.

  Global Instance for_i32 : FromStr.Trait i32.t.
  Admitted.

  Global Instance for_i64 : FromStr.Trait i64.t.
  Admitted.

  Global Instance for_i128 : FromStr.Trait i128.t.
  Admitted.

  Global Instance for_isize : FromStr.Trait isize.t.
  Admitted.

  Global Instance for_u8 : FromStr.Trait u8.t.
  Admitted.

  Global Instance for_u16 : FromStr.Trait u16.t.
  Admitted.

  Global Instance for_u32 : FromStr.Trait u32.t.
  Admitted.

  Global Instance for_u64 : FromStr.Trait u64.t.
  Admitted.

  Global Instance for_u128 : FromStr.Trait u128.t.
  Admitted.

  Global Instance for_usize : FromStr.Trait usize.t.
  Admitted.
End FromStr_instances.

(* ********FUNCTIONS******** *)
(*
[ ] from_boxed_utf8_unchecked
[ ] from_utf8
[ ] from_utf8_mut
[ ] from_utf8_unchecked
[ ] from_utf8_unchecked_mut
*)

Module Impl_str.
  Definition Self : Set := str.t.

  Parameter parse :
    forall {F : Set} {H0 : FromStr.Trait F},
    ref Self ->
    M (core.result.Result.t F (FromStr.Err (Trait := H0))).

  Global Instance AssociatedFunction_parse {F : Set} {H0 : FromStr.Trait F} :
    Notations.DoubleColon Self "parse" := {
    Notations.double_colon := parse (F := F);
  }.
End Impl_str.
