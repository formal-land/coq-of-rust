Require Import CoqOfRust.lib.lib.

(* Require CoqOfRust.std.marker.Sized. *)
(* Require CoqOfRust.std.option.Option. *)

(* ********STRUCTS******** *)
(* TODO: Complete the translation for structs *)

(* ********TRAITS******** *)
(* 
(!: Tested; x: Complete; ?: Bugged; empty: Unfinished)
[ ] Step(Experimental)
[x] TrustedLen(Experimental)
[x] TrustedStep(Experimental)
[ ] DoubleEndedIterator
[x] ExactSizeIterator
[ ] Extend
[?] FromIterator
[?] FusedIterator
[?] IntoIterator
[ ] Iterator
[?] Product
[?] Sum 
*)

Module Iterator.
  Class Trait (Self : Set) (Item : Set) := {
    (* TODO: Add the translation for all the functions... *)

    (* fn next(&mut self) -> Option<Self::Item>; *)
    next : deref Self -> Option Item;

    (* fn next_chunk<const N: usize>(
        &mut self
    ) -> Result<[Self::Item; N], IntoIter<Self::Item, N>>
       where Self: Sized { ... } *)
       next_chunk : usize -> deref_mut self -> Result (?);
  }.
End Iterator.

(* pub trait IntoIterator {
    type Item;
    type IntoIter: Iterator<Item = Self::Item>;

    // Required method
    fn into_iter(self) -> Self::IntoIter;
} *)
Module IntoIterator.
  type Item;
  type IntoIter : Iterator Item;

  Class Trait (Self : Set) (A : option Set) : Set := {
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
  Class Trait (Self : Set) (A : option Set) : Set := {
    from_iter : (T : Set) -> T -> Self.
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
(* These functions only provide parameters but don't specify the type for return value? *)
Module Extend.
  Class Trait (Self : Set) (A : option Set) : Set := {
    extend : T -> deref_mut Self -> T;
    (* ... *)
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
  Class Trait (Self : Set) (A : option Set) : Set := {
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
End DoubleEndedIterator.

Module Product.
  Class Trait (Self : Set) (A : option Set) : Set := {
    A := defaultType A Self;
    (* Issue: Here, I is required to have type of Iterator<Item=A>. But current definition 
      for Iterator.Trait requires more parameters. *)
    product : {(Iterator.trait A) I} -> I -> Self;
  }.
End Product.

Module Sum.
  Class Trait (Self : Set) (A : option Set) : Set := {
    A := defaultType A Self;
    (* Same as above *)
    sum : {(Iterator.trait A) I} -> I -> Self;
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