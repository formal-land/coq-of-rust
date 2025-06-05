Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.array.links.iter_IntoIter.
Require Import core.iter.adapters.links.map_Map.
Require Import core.iter.traits.iterator.
Require Import core.links.array.
Require Import core.links.option.
Require Import core.links.result.
Require Import core.num.links.nonzero.
Require Import core.ops.links.function.

(* pub trait Iterator *)
Module Iterator.
  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("core::iter::traits::iterator::Iterator", [], [], Φ Self).

  (* fn next(&mut self) -> Option<Self::Item>; *)
  Definition Run_next
      (Self : Set) `{Link Self}
      (Item : Set) `{Link Item} :
      Set :=
    TraitMethod.C (trait Self) "next" (fun method =>
      forall (self : Ref.t Pointer.Kind.MutRef Self),
      Run.Trait method [] [] [φ self] (option Item)
    ).

  (*
  fn next_chunk<const N: usize>(
      &mut self,
  ) -> Result<[Self::Item; N], IntoIter<Self::Item, N>>
  *)
  Definition Run_next_chunk
      (Self : Set) `{Link Self}
      (Item : Set) `{Link Item} :
      Set :=
    TraitMethod.C (trait Self) "next_chunk" (fun method =>
      forall
        (N : Usize.t)
        (self : Ref.t Pointer.Kind.MutRef Self),
      Run.Trait method [] [] [φ self] (Result.t (array.t Item N) (IntoIter.t Item N))
    ).

  (* fn size_hint(&self) -> (usize, Option<usize>) { ... } *)
  Definition Run_size_hint
      (Self : Set) `{Link Self} :
      Set :=
    TraitMethod.C (trait Self) "size_hint" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [φ self] (Usize.t * option Usize.t)
    ).

  (* fn count(self) -> usize *)
  Definition Run_count
      (Self : Set) `{Link Self} :
      Set :=
    TraitMethod.C (trait Self) "count" (fun method =>
      forall (self : Self),
      Run.Trait method [] [] [φ self] Usize.t
    ).

  (* fn last(self) -> Option<Self::Item> *)
  Definition Run_last
      (Self : Set) `{Link Self}
      (Item : Set) `{Link Item} :
      Set :=
    TraitMethod.C (trait Self) "last" (fun method =>
      forall (self : Self),
      Run.Trait method [] [] [φ self] (option Item)
    ).

  (* fn advance_by(&mut self, n: usize) -> Result<(), NonZero<usize>> *)
  Definition Run_advance_by
      (Self : Set) `{Link Self} :
      Set :=
    TraitMethod.C (trait Self) "advance_by" (fun method =>
      forall
         (self : Ref.t Pointer.Kind.MutRef Self)
         (n : Usize.t),
      Run.Trait method [] [] [φ self; φ n] (Result.t unit (NonZero.t Usize.t))
    ).

  (*
    fn nth(&mut self, n: usize) -> Option<Self::Item> { ... }
    fn step_by(self, step: usize) -> StepBy<Self> ⓘ
       where Self: Sized { ... }
    fn chain<U>(self, other: U) -> Chain<Self, U::IntoIter> ⓘ
       where Self: Sized,
             U: IntoIterator<Item = Self::Item> { ... }
    fn zip<U>(self, other: U) -> Zip<Self, U::IntoIter> ⓘ
       where Self: Sized,
             U: IntoIterator { ... }
    fn intersperse(self, separator: Self::Item) -> Intersperse<Self> ⓘ
       where Self: Sized,
             Self::Item: Clone { ... }
    fn intersperse_with<G>(self, separator: G) -> IntersperseWith<Self, G> ⓘ
       where Self: Sized,
             G: FnMut() -> Self::Item { ... }
   *)

    (*
      fn map<B, F>(self, f: F) -> Map<Self, F> ⓘ
         where Self: Sized,
               F: FnMut(Self::Item) -> B { ... }
   *)
   Definition Run_map
      (Self : Set) `{Link Self}
      (Item : Set) `{Link Item} :
      Set :=
    TraitMethod.C (trait Self) "map" (fun method =>
      forall (B F : Set) `(Link B) `(Link F)
        (self : Self)
        (f : F),
      Run.Trait method [] [Φ B; Φ F] [φ self; φ f] (Map.t Self F)
    ).

   (*
    fn for_each<F>(self, f: F)
       where Self: Sized,
             F: FnMut(Self::Item) { ... }
    fn filter<P>(self, predicate: P) -> Filter<Self, P> ⓘ
       where Self: Sized,
             P: FnMut(&Self::Item) -> bool { ... }
    fn filter_map<B, F>(self, f: F) -> FilterMap<Self, F> ⓘ
       where Self: Sized,
             F: FnMut(Self::Item) -> Option<B> { ... }
    fn enumerate(self) -> Enumerate<Self> ⓘ
       where Self: Sized { ... }
    fn peekable(self) -> Peekable<Self> ⓘ
       where Self: Sized { ... }
    fn skip_while<P>(self, predicate: P) -> SkipWhile<Self, P> ⓘ
       where Self: Sized,
             P: FnMut(&Self::Item) -> bool { ... }
    fn take_while<P>(self, predicate: P) -> TakeWhile<Self, P> ⓘ
       where Self: Sized,
             P: FnMut(&Self::Item) -> bool { ... }
    fn map_while<B, P>(self, predicate: P) -> MapWhile<Self, P> ⓘ
       where Self: Sized,
             P: FnMut(Self::Item) -> Option<B> { ... }
    fn skip(self, n: usize) -> Skip<Self> ⓘ
       where Self: Sized { ... }
    fn take(self, n: usize) -> Take<Self> ⓘ
       where Self: Sized { ... }
    fn scan<St, B, F>(self, initial_state: St, f: F) -> Scan<Self, St, F> ⓘ
       where Self: Sized,
             F: FnMut(&mut St, Self::Item) -> Option<B> { ... }
    fn flat_map<U, F>(self, f: F) -> FlatMap<Self, U, F> ⓘ
       where Self: Sized,
             U: IntoIterator,
             F: FnMut(Self::Item) -> U { ... }
    fn flatten(self) -> Flatten<Self> ⓘ
       where Self: Sized,
             Self::Item: IntoIterator { ... }
    fn map_windows<F, R, const N: usize>(self, f: F) -> MapWindows<Self, F, N> ⓘ
       where Self: Sized,
             F: FnMut(&[Self::Item; N]) -> R { ... }
    fn fuse(self) -> Fuse<Self> ⓘ
       where Self: Sized { ... }
    fn inspect<F>(self, f: F) -> Inspect<Self, F> ⓘ
       where Self: Sized,
             F: FnMut(&Self::Item) { ... }
    fn by_ref(&mut self) -> &mut Self
       where Self: Sized { ... }
    *)

    (*
    fn collect<B: FromIterator<Self::Item>>(self) -> B
       where Self: Sized { ... }
    *)
    Definition Run_collect
      (Self : Set) `{Link Self}
      (Item : Set) `{Link Item} :
      Set :=
    TraitMethod.C (trait Self) "collect" (fun method =>
      forall (B : Set) `(Link B) (self : Self),
      Run.Trait method [] [Φ B] [φ self] B
    ).

    (*
    fn try_collect<B>(
        &mut self,
    ) -> <Self::Item::Residual as Residual<B>>::TryType
       where Self: Sized,
             Self::Item: Try<Residual: Residual<B>>,
             B: FromIterator<<Self::Item as Try>::Output> { ... }
    fn collect_into<E: Extend<Self::Item>>(self, collection: &mut E) -> &mut E
       where Self: Sized { ... }
    fn partition<B, F>(self, f: F) -> (B, B)
       where Self: Sized,
             B: Default + Extend<Self::Item>,
             F: FnMut(&Self::Item) -> bool { ... }
    fn partition_in_place<'a, T: 'a, P>(self, predicate: P) -> usize
       where Self: Sized + DoubleEndedIterator<Item = &'a mut T>,
             P: FnMut(&T) -> bool { ... }
    fn is_partitioned<P>(self, predicate: P) -> bool
       where Self: Sized,
             P: FnMut(Self::Item) -> bool { ... }
    fn try_fold<B, F, R>(&mut self, init: B, f: F) -> R
       where Self: Sized,
             F: FnMut(B, Self::Item) -> R,
             R: Try<Output = B> { ... }
    fn try_for_each<F, R>(&mut self, f: F) -> R
       where Self: Sized,
             F: FnMut(Self::Item) -> R,
             R: Try<Output = ()> { ... }
    fn fold<B, F>(self, init: B, f: F) -> B
       where Self: Sized,
             F: FnMut(B, Self::Item) -> B { ... }
    fn reduce<F>(self, f: F) -> Option<Self::Item>
       where Self: Sized,
             F: FnMut(Self::Item, Self::Item) -> Self::Item { ... }
    fn try_reduce<R>(
        &mut self,
        f: impl FnMut(Self::Item, Self::Item) -> R,
    ) -> <R::Residual as Residual<Option<R::Output>>>::TryType
       where Self: Sized,
             R: Try<Output = Self::Item, Residual: Residual<Option<Self::Item>>> { ... }
    fn all<F>(&mut self, f: F) -> bool
       where Self: Sized,
             F: FnMut(Self::Item) -> bool { ... }
  *)

  (*
  fn any<F>(&mut self, f: F) -> bool
      where Self: Sized,
            F: FnMut(Self::Item) -> bool { ... }
  *)
  Definition Run_any
      (Self : Set) `{Link Self}
      (Item : Set) `{Link Item} :
      Set :=
    TraitMethod.C (trait Self) "any" (fun method =>
      forall
         (F : Set) `(Link F)
         (self : Ref.t Pointer.Kind.MutRef Self)
         (f : F)
         `(FnMut.Run F Item bool),
      Run.Trait method [] [Φ F] [φ self; φ f] bool
    ).

  (*
    fn find<P>(&mut self, predicate: P) -> Option<Self::Item>
       where Self: Sized,
             P: FnMut(&Self::Item) -> bool { ... }
    fn find_map<B, F>(&mut self, f: F) -> Option<B>
       where Self: Sized,
             F: FnMut(Self::Item) -> Option<B> { ... }
    fn try_find<R>(
        &mut self,
        f: impl FnMut(&Self::Item) -> R,
    ) -> <R::Residual as Residual<Option<Self::Item>>>::TryType
       where Self: Sized,
             R: Try<Output = bool, Residual: Residual<Option<Self::Item>>> { ... }
    fn position<P>(&mut self, predicate: P) -> Option<usize>
       where Self: Sized,
             P: FnMut(Self::Item) -> bool { ... }
    fn rposition<P>(&mut self, predicate: P) -> Option<usize>
       where P: FnMut(Self::Item) -> bool,
             Self: Sized + ExactSizeIterator + DoubleEndedIterator { ... }
    fn max(self) -> Option<Self::Item>
       where Self: Sized,
             Self::Item: Ord { ... }
    fn min(self) -> Option<Self::Item>
       where Self: Sized,
             Self::Item: Ord { ... }
    fn max_by_key<B: Ord, F>(self, f: F) -> Option<Self::Item>
       where Self: Sized,
             F: FnMut(&Self::Item) -> B { ... }
    fn max_by<F>(self, compare: F) -> Option<Self::Item>
       where Self: Sized,
             F: FnMut(&Self::Item, &Self::Item) -> Ordering { ... }
    fn min_by_key<B: Ord, F>(self, f: F) -> Option<Self::Item>
       where Self: Sized,
             F: FnMut(&Self::Item) -> B { ... }
    fn min_by<F>(self, compare: F) -> Option<Self::Item>
       where Self: Sized,
             F: FnMut(&Self::Item, &Self::Item) -> Ordering { ... }
    fn rev(self) -> Rev<Self> ⓘ
       where Self: Sized + DoubleEndedIterator { ... }
    fn unzip<A, B, FromA, FromB>(self) -> (FromA, FromB)
       where FromA: Default + Extend<A>,
             FromB: Default + Extend<B>,
             Self: Sized + Iterator<Item = (A, B)> { ... }
    fn copied<'a, T>(self) -> Copied<Self> ⓘ
       where Self: Sized + Iterator<Item = &'a T>,
             T: Copy + 'a { ... }
    fn cloned<'a, T>(self) -> Cloned<Self> ⓘ
       where Self: Sized + Iterator<Item = &'a T>,
             T: Clone + 'a { ... }
    fn cycle(self) -> Cycle<Self> ⓘ
       where Self: Sized + Clone { ... }
    fn array_chunks<const N: usize>(self) -> ArrayChunks<Self, N> ⓘ
       where Self: Sized { ... }
    fn sum<S>(self) -> S
       where Self: Sized,
             S: Sum<Self::Item> { ... }
    fn product<P>(self) -> P
       where Self: Sized,
             P: Product<Self::Item> { ... }
    fn cmp<I>(self, other: I) -> Ordering
       where I: IntoIterator<Item = Self::Item>,
             Self::Item: Ord,
             Self: Sized { ... }
    fn cmp_by<I, F>(self, other: I, cmp: F) -> Ordering
       where Self: Sized,
             I: IntoIterator,
             F: FnMut(Self::Item, I::Item) -> Ordering { ... }
    fn partial_cmp<I>(self, other: I) -> Option<Ordering>
       where I: IntoIterator,
             Self::Item: PartialOrd<I::Item>,
             Self: Sized { ... }
    fn partial_cmp_by<I, F>(self, other: I, partial_cmp: F) -> Option<Ordering>
       where Self: Sized,
             I: IntoIterator,
             F: FnMut(Self::Item, I::Item) -> Option<Ordering> { ... }
    fn eq<I>(self, other: I) -> bool
       where I: IntoIterator,
             Self::Item: PartialEq<I::Item>,
             Self: Sized { ... }
    fn eq_by<I, F>(self, other: I, eq: F) -> bool
       where Self: Sized,
             I: IntoIterator,
             F: FnMut(Self::Item, I::Item) -> bool { ... }
    fn ne<I>(self, other: I) -> bool
       where I: IntoIterator,
             Self::Item: PartialEq<I::Item>,
             Self: Sized { ... }
    fn lt<I>(self, other: I) -> bool
       where I: IntoIterator,
             Self::Item: PartialOrd<I::Item>,
             Self: Sized { ... }
    fn le<I>(self, other: I) -> bool
       where I: IntoIterator,
             Self::Item: PartialOrd<I::Item>,
             Self: Sized { ... }
    fn gt<I>(self, other: I) -> bool
       where I: IntoIterator,
             Self::Item: PartialOrd<I::Item>,
             Self: Sized { ... }
    fn ge<I>(self, other: I) -> bool
       where I: IntoIterator,
             Self::Item: PartialOrd<I::Item>,
             Self: Sized { ... }
    fn is_sorted(self) -> bool
       where Self: Sized,
             Self::Item: PartialOrd { ... }
    fn is_sorted_by<F>(self, compare: F) -> bool
       where Self: Sized,
             F: FnMut(&Self::Item, &Self::Item) -> bool { ... }
    fn is_sorted_by_key<F, K>(self, f: F) -> bool
       where Self: Sized,
             F: FnMut(Self::Item) -> K,
             K: PartialOrd { ... }
  *)

  Class Run
      (Self : Set) `{Link Self}
      (Item : Set) `{Link Item} :
      Set := {
   (* type Item; *)
    Item_IsAssociated :
      IsTraitAssociatedType
        "core::iter::traits::iterator::Iterator" [] [] (Φ Self)
        "Item" (Φ Item);
    next : Run_next Self Item;
    next_chunk : Run_next_chunk Self Item;
    size_hint : Run_size_hint Self;
    count : Run_count Self;
    last : Run_last Self Item;
    advance_by : Run_advance_by Self;
    map : Run_map Self Item;
    collect : Run_collect Self Item;
    any : Run_any Self Item;
  }.
End Iterator.
