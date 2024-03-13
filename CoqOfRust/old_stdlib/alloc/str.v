Require Import CoqOfRust.lib.lib.

Require CoqOfRust.alloc.string.
Require CoqOfRust.core.str.

Module Impl.
  Definition Self : Set := str.t.

  (*
  pub fn replace<'a, P>(&'a self, from: P, to: &str) -> String
  where
      P: Pattern<'a>,
  *)
  Parameter replace :
    forall {P : Set},
    ref Self -> P -> ref str.t -> M string.String.t.

  Global Instance AF_replace {P : Set} :
      Notations.DoubleColon Self "replace" := {
    Notations.double_colon := replace (P := P);
  }.

  (*
  pub fn trim_matches<'a, P>(&'a self, pat: P) -> &'a str
  where
      P: Pattern<'a>,
      <P as Pattern<'a>>::Searcher: DoubleEndedSearcher<'a>,
  *)
  Parameter trim_matches :
    forall {P : Set},
    ref Self -> P -> M (ref Self).

  Global Instance AF_trim_matches {P : Set} :
      Notations.DoubleColon Self "trim_matches" := {
    Notations.double_colon := trim_matches (P := P);
  }.

  (* pub fn split_whitespace(&self) -> SplitWhitespace<'_> *)
  Parameter split_whitespace :
    ref Self -> M (str.iter.SplitWhitespace.t).

  Global Instance AF_split_whitespace :
      Notations.DoubleColon Self "split_whitespace" := {
    Notations.double_colon := split_whitespace;
  }.
End Impl.
