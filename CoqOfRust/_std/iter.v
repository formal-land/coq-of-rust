Require Import CoqOfRust.lib.lib.

Require Import CoqOfRust._std.iter_type.

(* NOTE: This file is for completing the definitions for provided methods in the Iterator trait.
   This is because there's a mutual reference issue in the iter trait, so we divide the file 
   into two parts. *)

(* fn next_chunk<const N: usize>(
    &mut self
) -> Result<[Self::Item; N], IntoIter<Self::Item, N>>
    where Self: Sized { ... } *)

Parameter Self : Set.

Parameter next_chunk (N : usize) : mut_ref Self -> Result (slice Item) (IntoIter Item N).

(* fn size_hint(&self) -> (usize, Option<usize>) { ... } *)
Parameter size_hint : mut_ref Self -> usize * (Option usize).

(* fn count(self) -> usize
    where Self: Sized { ... } *)
Parameter count : Self -> usize.

(* fn last(self) -> Option<Self::Item>
    where Self: Sized { ... } *)
Parameter last : Self -> Option Item.

(* fn advance_by(&mut self, n: usize) -> Result<(), usize> { ... } *)
Parameter advance_by : mut_ref Self -> usize -> Result unit usize.

(* fn nth(&mut self, n: usize) -> Option<Self::Item> { ... } *)
Parameter nth : mut_ref Self -> usize -> Option Item.

(* TODO: implement StepBy struct in iter.v *)
(* fn step_by(self, step: usize) -> StepBy<Self>
    where Self: Sized { ... } *)
Parameter step_by : Self -> usize -> StepBy Self.

(* fn chain<U>(self, other: U) -> Chain<Self, <U as IntoIterator>::IntoIter>
    where Self: Sized,
          U: IntoIterator<Item = Self::Item> { ... } *)
  chain {U : Set} 
    `{IntoIterator.Trait U (Some Item)} :
    Chain Self U.((IntoIterator.Trait).IntoIter);

(* fn zip<U>(self, other: U) -> Zip<Self, <U as IntoIterator>::IntoIter>
    where Self: Sized,
          U: IntoIterator { ... } *)
(* NOTE: Wrong translation? *)
Parameter zip {U : Set} 
  `{IntoIterator.Trait U}
: Self -> U -> Zip Self U.((IntoIterator.Trait).IntoIter).

(* fn intersperse(self, separator: Self::Item) -> Intersperse<Self>
    where Self: Sized,
          Self::Item: Clone { ... } *)
Parameter intersperse : Self -> Self.Item -> Intersperse Self.

(* fn intersperse_with<G>(self, separator: G) -> IntersperseWith<Self, G>
    where Self: Sized,
          G: FnMut() -> Self::Item { ... } *)
(* fn map<B, F>(self, f: F) -> Map<Self, F>
    where Self: Sized,
          F: FnMut(Self::Item) -> B { ... } *)
(* fn for_each<F>(self, f: F)
    where Self: Sized,
          F: FnMut(Self::Item) { ... } *)
(* fn filter<P>(self, predicate: P) -> Filter<Self, P>
    where Self: Sized,
          P: FnMut(&Self::Item) -> bool { ... } *)