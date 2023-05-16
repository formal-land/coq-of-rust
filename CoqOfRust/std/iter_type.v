Require Import CoqOfRust.lib.lib.

Require Import CoqOfRust.std.option.

Require Import CoqOfRust.std.result.

(* TODO: After the following file is implemented, check all occurences of IntoIter in this file. *)
Require Import CoqOfRust.std.array.
Require Import CoqOfRust.std.marker.
Require Import CoqOfRust.std.clone.
Require Import CoqOfRust.std.cmp.


(* ********TRAITS******** *)

(* 
[x] Step(Experimental)
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

(* NOTE: The Iterator trait has to be put at the first place because most structs depend on this trait. *)
Module Iterator.
  Class Trait (Self : Set) (Item : Set) := {
    Item := Item;

    (* fn next(&mut self) -> Option<Self::Item>; *)
    next : mut_ref Self -> Option Item;
  }.
End Iterator.


(* pub trait IntoIterator {
    type Item;
    type IntoIter: Iterator<Item = Self::Item>;

    // Required method
    fn into_iter(self) -> Self::IntoIter;
} 
*)
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

(* ********STRUCTS******** *)
(*
[x] ArrayChunks
[x] ByRefSized
[x] Intersperse
[x] IntersperseWith
[x] Chain
[x] Cloned
[x] Copied
[x] Cycle
[x] Empty
[x] Enumerate
[x] Filter
[x] FilterMap
[x] FlatMap
[x] Flatten
[x] FromFn
[x] Fuse
[x] Inspect
[x] Map
[x] MapWhile
[x] Once
[x] OnceWith
[x] Peekable
[x] Repeat
[x] RepeatWith
[x] Rev
[x] Scan
[x] Skip
[x] SkipWhile
[x] StepBy
[x] Successors
[x] Take
[x] TakeWhile
[x] Zip
*)

(* 
pub struct ArrayChunks<I, const N: usize>
where
    I: Iterator,
{ /* private fields */ }
*)
Module ArrayChunks.
  Record t (I : Set) `{Iterator.Trait I} (N : usize) : Set := { }.
End ArrayChunks.
Definition ArrayChunks := ArrayChunks.t.

(* 
pub struct ByRefSized<'a, I>(pub &'a mut I);
*)
Module ByRefSized.
  Record t (I : Set) : Set := { }.
End ByRefSized.
Definition ByRefSized := ByRefSized.t.

(* 
pub struct Intersperse<I>
where
    I: Iterator,
    <I as Iterator>::Item : Clone,
{ /* private fields */ }
*)
Module Intersperse.
  Record t (I : Set) 
    `{Clone.Trait I.(Iterator.Item)}
  : Set := { }.
End Intersperse.
Definition Intersperse := Intersperse.t.

(* 
pub struct IntersperseWith<I, G>
where
    I: Iterator,
{ /* private fields */ }
*)
Module IntersperseWith.
  Record t (I G : Set) `{Iterator.Trait I} : Set := { }.
End IntersperseWith.
Definition IntersperseWith := IntersperseWith.t.

(* 
pub struct Chain<A, B> { /* private fields */ }
*)
Module Chain.
  Record t (A B : Set) : Set := { }.
End Chain.
Definition Chain := Chain.t.

(* 
pub struct Cloned<I> { /* private fields */ }
*)
Module Cloned.
  Record t (I : Set): Set := { }.
End Cloned.
Definition Cloned := Cloned.t.

(* pub struct Copied<I> { /* private fields */ } *)
Module Copied.
  Record t (I : Set) : Set := { }.
End Copied.
Definition Copied := Copied.t.

(* pub struct Cycle<I> { /* private fields */ } *)
Module Cycle.
  Record t (I : Set) : Set := { }.
End Cycle.
Definition Cycle := Cycle.t.

(* pub struct Empty<T>(_); *)
Module Empty.
  Record t (T : Set) : Set := { }.
End Empty.
Definition Empty := Empty.t.

(* pub struct Enumerate<I> { /* private fields */ } *)
Module Enumerate.
  Record t (I : Set) : Set := { }.
End Enumerate.
Definition Enumerate := Enumerate.t.

(* pub struct Filter<I, P> { /* private fields */ } *)
Module Filter.
  Record t (I P : Set) : Set := { }.
End Filter.
Definition Filter := Filter.t.

(* pub struct FilterMap<I, F> { /* private fields */ } *)
Module FilterMap.
  Record t (I F : Set) : Set := { }.
End FilterMap.
Definition FilterMap := FilterMap.t.

(* 
pub struct FlatMap<I, U, F>
where
    U: IntoIterator,
{ /* private fields */ }
*)
Module FlatMap.
  Record t (I U F : Set) 
    `{IntoIterator.Trait U} : Set := { }.
End FlatMap.
Definition FlatMap := FlatMap.t.

(* 
pub struct Flatten<I>
where
    I: Iterator,
    <I as Iterator>::Item: IntoIterator,
{ /* private fields */ }
*)
Module Flatten.
  Record t (I : Set)
    `{Iterator.Trait I}
    `{IntoIterator.Trait I.(Iterator.Item)}
  : Set := { }.
End Flatten.
Definition Flatten := Flatten.t.

(* pub struct FromFn<F>(_); *)
Module FromFn.
  Record t (F : Set) : Set := { }.
End FromFn.
Definition FromFn := FromFn.t.

(* pub struct Fuse<I> { /* private fields */ } *)
Module Fuse.
  Record t (I : Set) : Set := { }.
End Fuse.
Definition Fuse := Fuse.t.

(* pub struct Inspect<I, F> { /* private fields */ } *)
Module Inspect.
  Record t (I F : Set) : Set := { }.
End Inspect.
Definition Inspect := Inspect.t.

(* pub struct Map<I, F> { /* private fields */ } *)
Module Map.
  Record t (I F : Set) : Set := { }.
End Map.
Definition Map := Map.t.

(* pub struct MapWhile<I, P> { /* private fields */ } *)
Module MapWhile.
  Record t (I P : Set) : Set := { }.
End MapWhile.
Definition MapWhile := MapWhile.t.

(* pub struct Once<T> { /* private fields */ } *)
Module Once.
  Record t (T : Set) : Set := { }.
End Once.
Definition Once := Once.t.

(* pub struct OnceWith<F> { /* private fields */ } *)
Module OnceWith.
  Record t (F : Set) : Set := { }.
End OnceWith.
Definition OnceWith := OnceWith.t.

(* 
pub struct Peekable<I>
where
    I: Iterator,
{ /* private fields */ }
*)
Module Peekable.
  Record t (I : Set)
  `{Iterator.Trait I}
  : Set := { }.
End Peekable.
Definition Peekable := Peekable.t.

(* pub struct Repeat<A> { /* private fields */ } *)
Module Repeat.
  Record t (A : Set) : Set := { }.
End Repeat.
Definition Repeat := Repeat.t.

(* pub struct RepeatWith<F> { /* private fields */ } *)
Module RepeatWith.
  Record t (F : Set) : Set := { }.
End RepeatWith.
Definition RepeatWith := RepeatWith.t.

(* pub struct Rev<T> { /* private fields */ } *)
Module Rev.
  Record t (T : Set) : Set := { }.
End Rev.
Definition Rev := Rev.t.

(* pub struct Scan<I, St, F> { /* private fields */ } *)
Module Scan.
  Record t (I St F : Set) : Set := { }.
End Scan.
Definition Scan := Scan.t.

(* pub struct Skip<I> { /* private fields */ } *)
Module Skip.
  Record t (I) : Set := { }.
End Skip.
Definition Skip := Skip.t.

(* pub struct SkipWhile<I, P> { /* private fields */ } *)
Module SkipWhile.
  Record t (I P : Set) : Set := { }.
End SkipWhile.
Definition SkipWhile := SkipWhile.t.

(* pub struct StepBy<I> { /* private fields */ } *)
Module StepBy.
  Record t (I) : Set := { }.
End StepBy.
Definition StepBy := StepBy.t.

(* pub struct Successors<T, F> { /* private fields */ } *)
Module Successors.
  Record t (T F : Set) : Set := { }.
End Successors.
Definition Successors := Successors.t.

(* pub struct Take<I> { /* private fields */ } *)
Module Take.
  Record t (I : Set) : Set := { }.
End Take.
Definition Take := Take.t.

(* pub struct TakeWhile<I, P> { /* private fields */ } *)
Module TakeWhile.
  Record t (I P : Set) : Set := { }.
End TakeWhile.
Definition TakeWhile := TakeWhile.t.

(* pub struct Zip<A, B> { /* private fields */ } *)
Module Zip.
  Record t (A B : Set) : Set := { }.
End Zip.
Definition Zip := Zip.t.