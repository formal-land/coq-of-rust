Require Import CoqOfRust.lib.lib.

(* Require CoqOfRust.std.marker.Sized. *)
Require Import CoqOfRust.std.option.

Require Import CoqOfRust.std.result.

(* TODO: After the following file is implemented, check all occurences of IntoIter in this file. *)
Require Import CoqOfRust.std.array.
Require Import CoqOfRust.std.marker.

(* (!: Tested; x: Complete; ?: Bugged; empty: Unfinished) *)
(* ********STRUCTS******** *)
(*
[ ] ArrayChunks
[ ] ByRefSized
[ ] Intersperse
[ ] IntersperseWith
[ ] Chain
[ ] Cloned
[ ] Copied
[ ] Cycle
[ ] Empty
[ ] Enumerate
[ ] Filter
[ ] FilterMap
[ ] FlatMap
[ ] Flatten
[ ] FromFn
[ ] Fuse
[ ] Inspect
[ ] Map
[ ] MapWhile
[ ] Once
[ ] OnceWith
[ ] Peekable
[ ] Repeat
[ ] RepeatWith
[ ] Rev
[ ] Scan
[ ] Skip
[ ] SkipWhile
[ ] StepBy
[ ] Successors
[ ] Take
[ ] TakeWhile
[ ] Zip
*)

(* ********TRAITS******** *)
(* 
[ ] Step(Experimental)
[x] TrustedLen(Experimental)
[x] TrustedStep(Experimental)
[x] DoubleEndedIterator
[x] ExactSizeIterator
[x] Extend
[x] FromIterator
[x] FusedIterator
[x] IntoIterator
[ ] Iterator
[x] Product
[x] Sum 
*)

(* TODO: implement the structs then come back to this trait, since many of the 
functions here requires the corresponded structs *)
Module Iterator.
  Class Trait (Self : Set) (Item : Set) := {
    (* TODO: Add the translation for all the functions... *)

    (* fn next(&mut self) -> Option<Self::Item>; *)
    next : mut_ref Self -> Option Item;

    (* fn next_chunk<const N: usize>(
        &mut self
    ) -> Result<[Self::Item; N], IntoIter<Self::Item, N>>
       where Self: Sized { ... } *)
    next_chunk (N : usize) : mut_ref Self -> Result (slice Item) (IntoIter Item N);

    (* NOTE: tuple not implemented yet *)
    (* fn size_hint(&self) -> (usize, Option<usize>) { ... } *)
    size_hint : mut_ref Self -> usize * (Option usize);

    (* fn count(self) -> usize
       where Self: Sized { ... } *)
    count `{Sized.Trait Self} : Self -> usize;

    (* fn last(self) -> Option<Self::Item>
       where Self: Sized { ... } *)
    last `{Sized.Trait Self} : Self -> Option Item;

    (* fn advance_by(&mut self, n: usize) -> Result<(), usize> { ... } *)
    advance_by : mut_ref Self -> usize -> Result unit usize;

    (* fn nth(&mut self, n: usize) -> Option<Self::Item> { ... } *)
    nth : mut_ref Self -> usize -> Option Item;
    
    (* TODO: implement StepBy struct in iter.v *)
    (* fn step_by(self, step: usize) -> StepBy<Self>
       where Self: Sized { ... } *)
    (* step_by `{Sized.Trait Self} : Self -> usize -> StepBy Self; *)
    
    (* fn chain<U>(self, other: U) -> Chain<Self, <U as IntoIterator>::IntoIter>
       where Self: Sized,
             U: IntoIterator<Item = Self::Item> { ... } *)
    (* chain {U : Set} 
      `{Sized.Trait Self} 
      `{IntoIterator.Trait U (Some Item)} :
      Chain Self (?); *)

    (* fn zip<U>(self, other: U) -> Zip<Self, <U as IntoIterator>::IntoIter>
        where Self: Sized,
              U: IntoIterator { ... } *)
    (* zip {U : Set} 
      `{Sized.Trait Self}
      `{IntoIterator.Trait U}
    : Self -> U -> Zip Self (?); *)

    (* fn intersperse(self, separator: Self::Item) -> Intersperse<Self>
        where Self: Sized,
              Self::Item: Clone { ... } *)
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

  }.
End Iterator.

(* pub trait IntoIterator {
    type Item;
    type IntoIter: Iterator<Item = Self::Item>;

    // Required method
    fn into_iter(self) -> Self::IntoIter;
} *)
Module IntoIterator.
  Class Trait (Self Item IntoIter : Set) `{Iterator.Trait IntoIter Item} : Set := {
    Item := Item;
    IntoIter := IntoIter;
    into_iter : Self -> IntoIter;
  }.
End IntoIterator.

(* 
pub trait FromIterator<A>: Sized {
    // Required method
    fn from_iter<T>(iter: T) -> Self
       where T: IntoIterator<Item = A>;
}
*)
Module FromIterator.
  Class Trait (Self : Set) (A : Set) : Set := {
    from_iter {T : Set} `{IntoIterator.Trait T A} : T -> Self;
  }.
End FromIterator.

(* pub trait FusedIterator: Iterator { } *)
Module FusedIterator.
  Class Trait (Self : Set) : Set := { }.
End FusedIterator.

(* 
pub trait Extend<A> {
    // Required method
    fn extend<T>(&mut self, iter: T)
       where T: IntoIterator<Item = A>;

    // Provided methods
    fn extend_one(&mut self, item: A) { ... }
    fn extend_reserve(&mut self, additional: usize) { ... }
}
*)
Module Extend.
  Class Trait (Self : Set) (A : Set) : Set := {
  (* NOTE: Important for reference *)
    extend {T : Set} `{IntoIterator.Trait T A} : mut_ref Self -> T -> unit;
    extend_one : mut_ref Self -> A -> unit;
    extend_reserve : mut_ref Self -> usize -> unit;
  }.
End Extend.

(* 
pub trait ExactSizeIterator: Iterator {
    // Provided methods
    fn len(&self) -> usize { ... }
    fn is_empty(&self) -> bool { ... }
}
*)
Module ExactSizeIterator.
  Class Trait (Self : Set) (A : Set) : Set := {
    len : ref Self -> usize;
    is_empty : ref Self -> bool;
  }.
End ExactSizeIterator.

(* 
pub trait DoubleEndedIterator: Iterator {
    // Required method
    fn next_back(&mut self) -> Option<Self::Item>;

    // Provided methods
    fn advance_back_by(&mut self, n: usize) -> Result<(), usize> { ... }
    fn nth_back(&mut self, n: usize) -> Option<Self::Item> { ... }
    fn try_rfold<B, F, R>(&mut self, init: B, f: F) -> R
       where Self: Sized,
             F: FnMut(B, Self::Item) -> R,
             R: Try<Output = B> { ... }
    fn rfold<B, F>(self, init: B, f: F) -> B
       where Self: Sized,
             F: FnMut(B, Self::Item) -> B { ... }
    fn rfind<P>(&mut self, predicate: P) -> Option<Self::Item>
       where Self: Sized,
             P: FnMut(&Self::Item) -> bool { ... }
}
*)
Module DoubleEndedIterator.
  Class Trait (Self : Set) (A : Set) (Item : Set): Set := {
    Item := Item;
    next_back : mut_ref Self -> Option Item;
    advance_back_by : mut_ref Self -> usize -> Result unit usize;
    nth_back : mut_ref Self -> usize -> Option Item;
    try_nfold {B F R : Set} : mut_ref Self -> B -> F -> R;
    rfold {B F : Set} : Self -> B -> F -> B;
    rfind {P : Set} : mut_ref Self -> P -> Option Item;
  }.
End DoubleEndedIterator.


(* 
pub trait Product<A = Self>: Sized {
    // Required method
    fn product<I>(iter: I) -> Self
       where I: Iterator<Item = A>;
}
*)
Module Product.
  Class Trait (Self : Set) (A : option Set) : Set := {
    A := defaultType A Self;
    (* Issue: Here, I is required to have type of Iterator<Item=A>. But current definition 
      for Iterator.Trait requires more parameters. *)
    product {I : Set} `{Iterator.Trait A I} : I -> Self;
  }.
End Product.

Module Sum.
  Class Trait (Self : Set) (A : option Set) : Set := {
    A := defaultType A Self;
    sum {I : Set} `{Iterator.Trait A I} : I -> Self;
  }.
End Sum.

(* 
pub trait Step: Clone + PartialOrd<Self> + Sized {
    // Required methods
    fn steps_between(start: &Self, end: &Self) -> Option<usize>;
    fn forward_checked(start: Self, count: usize) -> Option<Self>;
    fn backward_checked(start: Self, count: usize) -> Option<Self>;

    // Provided methods
    fn forward(start: Self, count: usize) -> Self { ... }
    unsafe fn forward_unchecked(start: Self, count: usize) -> Self { ... }
    fn backward(start: Self, count: usize) -> Self { ... }
    unsafe fn backward_unchecked(start: Self, count: usize) -> Self { ... }
}
*)
Module Step.
  Class Trait (Self : Set) 
    `{Clone.Trait Self}
    `{PartialOrd.Trait Self (Some Self)}
    `{Sized.Trait Self}
  : Set := {
    steps_between : ref Self -> ref Self -> Option usize;
    forward_checked : Self -> usize -> Option Self;
    backward_checked : Self -> usize -> Self;
    backward_unchecked : Self -> usize -> Self;
  }.
End Step.

(* 
pub unsafe trait TrustedLen: Iterator { }
*)
Module TrustedLen.
  Class Trait (Self : Set) : Set := { }.
End TrustedLen.

(* 
pub unsafe trait TrustedStep: Step { }
*)
Module TrustedStep.
  Class Trait (Self : Set) : Set := { }.
End TrustedStep.
