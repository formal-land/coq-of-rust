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
    Inductive t `{ℋ : State.Trait} : Set := 
    | Match: usize -> usize -> t
    | Reject: usize -> usize -> t
    | Done : t
    .
  End SearchStep.
  Definition SearchStep `{ℋ : State.Trait} : Set :=
    M.Val SearchStep.t.

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
    Class Trait `{ℋ : State.Trait} (Self : Set) : Set := { 
      haystack : ref Self -> ref str;
      next : mut_ref Self -> SearchStep;
      next_match : mut_ref Self -> option.Option (usize * usize);
      next_reject : mut_ref Self -> option.Option (usize * usize);
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
    Class Trait `{ℋ : State.Trait} (Self : Set) 
      `{Searcher.Trait Self} : Set := { 
        next_back : mut_ref Self -> SearchStep;
        next_match_back : mut_ref Self -> option.Option (usize * usize);
        next_reject_back : mut_ref Self -> option.Option (usize * usize);
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
    Class Trait `{ℋ : State.Trait} (Self Searcher : Set) : Set := { 
      Searcher := Searcher;

      into_searcher : Self -> ref str -> Searcher;
      is_contained_in : Self -> ref str -> bool;
      is_prefix_of : Self -> ref str -> bool;
      is_suffix_of `{ReverseSearcher.Trait Searcher} : Self -> ref str -> bool;
      strip_prefix_of : Self -> ref str -> option.Option (ref str);
      strip_suffix_of `{ReverseSearcher.Trait Searcher} : Self -> ref str -> option.Option (ref str);
    }.
  End Pattern.

  (* pub trait DoubleEndedSearcher<'a>: ReverseSearcher<'a> { } *)
  Module DoubleEndedSearcher.
    Unset Primitive Projections.
    Class Trait `{ℋ : State.Trait} (Self : Set) `{ReverseSearcher.Trait Self} : Set := { }.
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
Definition Utf8Chunk := Utf8Chunk.t.

(* pub struct Utf8Chunks<'a> { /* private fields */ } *)
Module Utf8Chunks.
  Parameter t : Set.
End Utf8Chunks.
Definition Utf8Chunks := Utf8Chunks.t.

(* pub struct Bytes<'a>(_); *)
Module Bytes.
  Parameter t : Set.
End Bytes.
Definition Bytes := Bytes.t.

(* pub struct CharIndices<'a> { /* private fields */ } *)
Module CharIndices.
  Parameter t : Set.
End CharIndices.
Definition CharIndices := CharIndices.t.

(* pub struct Chars<'a> { /* private fields */ } *)
Module Chars.
  Parameter t : Set.
End Chars.
Definition Chars := Chars.t.

(* pub struct EncodeUtf16<'a> { /* private fields */ } *)
Module EncodeUtf16.
  Parameter t : Set.
End EncodeUtf16.
Definition EncodeUtf16 := EncodeUtf16.t.

(* pub struct EscapeDebug<'a> { /* private fields */ } *)
Module EscapeDebug.
  Parameter t : Set.
End EscapeDebug.
Definition EscapeDebug := EscapeDebug.t.

(* pub struct EscapeDefault<'a> { /* private fields */ } *)
Module EscapeDefault.
  Parameter t : Set.
End EscapeDefault.
Definition EscapeDefault := EscapeDefault.t.

(* pub struct EscapeUnicode<'a> { /* private fields */ } *)
Module EscapeUnicode.
  Parameter t : Set.
End EscapeUnicode.
Definition EscapeUnicode := EscapeUnicode.t.

(* pub struct Lines<'a>(_); *)
Module Lines.
  Parameter t : Set.
End Lines.
Definition Lines := Lines.t.

(* NOTE: LinesAny deprecated *)

(* 
pub struct MatchIndices<'a, P>(_)
where
         P: Pattern<'a>;
*)
Module MatchIndices.
  Parameter t : forall (P : Set) `{Pattern.Trait P}, Set.
End MatchIndices.
Definition MatchIndices := MatchIndices.t.

(* 
pub struct Matches<'a, P>(_)
where
         P: Pattern<'a>;
*)
Module Matches.
  Parameter t : forall (P : Set) `{Pattern.Trait P}, Set.
End Matches.
Definition Matches := Matches.t.

(* 
pub struct RMatchIndices<'a, P>(_)
where
         P: Pattern<'a>;
*)
Module RMatchIndices.
  Parameter t : forall (P : Set) `{Pattern.Trait P}, Set.
End RMatchIndices.
Definition RMatchIndices := RMatchIndices.t.

(* 
pub struct RMatches<'a, P>(_)
where
         P: Pattern<'a>;
*)
Module RMatches.
  Parameter t : forall (P : Set) `{Pattern.Trait P}, Set.
End RMatches.
Definition RMatches := RMatches.t.

(* 
pub struct RSplit<'a, P>(_)
where
         P: Pattern<'a>;
*)
Module RSplit.
  Parameter t : forall (P : Set) `{Pattern.Trait P}, Set.
End RSplit.
Definition RSplit := RSplit.t.

(* 
pub struct RSplitN<'a, P>(_)
where
         P: Pattern<'a>;
*)
Module RSplitN.
  Parameter t : forall (P : Set) `{Pattern.Trait P}, Set.
End RSplitN.
Definition RSplitN := RSplitN.t.

(* 
pub struct RSplitTerminator<'a, P>(_)
where
         P: Pattern<'a>;
*)
Module RSplitTerminator.
  Parameter t : forall (P : Set) `{Pattern.Trait P}, Set.
End RSplitTerminator.
Definition RSplitTerminator := RSplitTerminator.t.

(* 
pub struct Split<'a, P>(_)
where
         P: Pattern<'a>;
*)
Module Split.
  Parameter t : forall (P : Set) `{Pattern.Trait P}, Set.
End Split.
Definition Split := Split.t.

(* pub struct SplitAsciiWhitespace<'a> { /* private fields */ } *)
Module SplitAsciiWhitespace.
  Parameter t : Set.
End SplitAsciiWhitespace.
Definition SplitAsciiWhitespace := SplitAsciiWhitespace.t.

(* 
pub struct SplitInclusive<'a, P>(_)
where
         P: Pattern<'a>;
*)
Module SplitInclusive.
  Parameter t : forall (P : Set) `{Pattern.Trait P}, Set.
End SplitInclusive.
Definition SplitInclusive := SplitInclusive.t.

(* 
pub struct SplitN<'a, P>(_)
where
         P: Pattern<'a>;
*)
Module SplitN.
  Parameter t : forall (P : Set) `{Pattern.Trait P}, Set.
End SplitN.
Definition SplitN := SplitN.t.


(* 
pub struct SplitTerminator<'a, P>(_)
where
         P: Pattern<'a>;
*)
Module SplitTerminator.
  Parameter t : forall (P : Set) `{Pattern.Trait P}, Set.
End SplitTerminator.
Definition SplitTerminator := SplitTerminator.t.


(* pub struct SplitWhitespace<'a> { /* private fields */ } *)
Module SplitWhitespace.
  Parameter t : Set.
End SplitWhitespace.
Definition SplitWhitespace := SplitWhitespace.t.

(* pub struct Utf8Error { /* private fields */ } *)
Module Utf8Error.
  Parameter t : Set.
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
  Class Trait `{ℋ : State.Trait} (Self : Set) : Type := { 
    Err : Set;
    from_str : ref str -> result.Result Self Err;
  }.
End FromStr.

Module FromStr_instances.
  #[refine]
  Global Instance for_bool `{ℋ : State.Trait} : FromStr.Trait bool := {
    Err := str.error.ParseBoolError;
  }.
    all: destruct (axiom "FromStr_instances" : Empty_set).
  Defined.

  Global Instance for_char `{ℋ : State.Trait} : FromStr.Trait char.
  Admitted.

  Global Instance for_f32 `{ℋ : State.Trait} : FromStr.Trait f32.
  Admitted.

  Global Instance for_f64 `{ℋ : State.Trait} : FromStr.Trait f64.
  Admitted.

  Global Instance for_i8 `{ℋ : State.Trait} : FromStr.Trait i8.
  Admitted.

  Global Instance for_i16 `{ℋ : State.Trait} : FromStr.Trait i16.
  Admitted.

  Global Instance for_i32 `{ℋ : State.Trait} : FromStr.Trait i32.
  Admitted.

  Global Instance for_i64 `{ℋ : State.Trait} : FromStr.Trait i64.
  Admitted.

  Global Instance for_i128 `{ℋ : State.Trait} : FromStr.Trait i128.
  Admitted.

  Global Instance for_isize `{ℋ : State.Trait} : FromStr.Trait isize.
  Admitted.

  Global Instance for_u8 `{ℋ : State.Trait} : FromStr.Trait u8.
  Admitted.

  Global Instance for_u16 `{ℋ : State.Trait} : FromStr.Trait u16.
  Admitted.

  Global Instance for_u32 `{ℋ : State.Trait} : FromStr.Trait u32.
  Admitted.

  Global Instance for_u64 `{ℋ : State.Trait} : FromStr.Trait u64.
  Admitted.

  Global Instance for_u128 `{ℋ : State.Trait} : FromStr.Trait u128.
  Admitted.

  Global Instance for_usize `{ℋ : State.Trait} : FromStr.Trait usize.
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

Module Impl_str. Section Impl_str.
  Context `{ℋ : State.Trait}.

  Definition Self : Set := str.

  Parameter parse :
    forall `{ℋ : State.Trait} {F : Set}
      {H0 : FromStr.Trait F},
    ref Self ->
    M (core.result.Result F (FromStr.Err (Trait := H0))).

  Global Instance AssociatedFunction_parse {F : Set} {H0 : FromStr.Trait F} :
    Notation.DoubleColon Self "parse" := {
    Notation.double_colon := parse (F := F);
  }.
End Impl_str. End Impl_str.
