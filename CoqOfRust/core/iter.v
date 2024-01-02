Require Import CoqOfRust.lib.lib.

Require CoqOfRust.alloc.vec.
Require CoqOfRust.core.alloc.
Require CoqOfRust.core.array.
Require CoqOfRust.core.num.
Require CoqOfRust.core.option.
Require CoqOfRust.core.result.
Require CoqOfRust.core.slice.

Module adapters.
  Module chain.
    (* pub struct Chain<A, B> { /* private fields */ } *)
    Module Chain.
      Parameter t : Set -> Set -> Set.
    End Chain.
  End chain.

  Module step_by.
    (* pub struct StepBy<I> { /* private fields */ } *)
    Module StepBy.
      Parameter t : Set -> Set.
    End StepBy.
  End step_by.

  Module zip.
    (* pub struct Zip<A, B> { /* private fields */ } *)
    Module Zip.
      Parameter t : Set -> Set -> Set.
    End Zip.
  End zip.
End adapters.

Module traits.
  Module iterator.
    (*
    pub trait Iterator {
        type Item;

        // Required method
        fn next(&mut self) -> Option<Self::Item>;

        // Provided methods
        fn next_chunk<const N: usize>(
            &mut self
        ) -> Result<[Self::Item; N], IntoIter<Self::Item, N>>
          where Self: Sized { ... }
        fn size_hint(&self) -> (usize, Option<usize>) { ... }
        fn count(self) -> usize
          where Self: Sized { ... }
        fn last(self) -> Option<Self::Item>
          where Self: Sized { ... }
        fn advance_by(&mut self, n: usize) -> Result<(), NonZeroUsize> { ... }
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
        fn map<B, F>(self, f: F) -> Map<Self, F> ⓘ
          where Self: Sized,
                F: FnMut(Self::Item) -> B { ... }
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
        fn collect<B: FromIterator<Self::Item>>(self) -> B
          where Self: Sized { ... }
        fn try_collect<B>(
            &mut self
        ) -> <<Self::Item as Try>::Residual as Residual<B>>::TryType
          where Self: Sized,
                <Self as Iterator>::Item: Try,
                <<Self as Iterator>::Item as Try>::Residual: Residual<B>,
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
        fn try_reduce<F, R>(
            &mut self,
            f: F
        ) -> <<R as Try>::Residual as Residual<Option<R::Output>>>::TryType
          where Self: Sized,
                F: FnMut(Self::Item, Self::Item) -> R,
                R: Try<Output = Self::Item>,
                R::Residual: Residual<Option<Self::Item>> { ... }
        fn all<F>(&mut self, f: F) -> bool
          where Self: Sized,
                F: FnMut(Self::Item) -> bool { ... }
        fn any<F>(&mut self, f: F) -> bool
          where Self: Sized,
                F: FnMut(Self::Item) -> bool { ... }
        fn find<P>(&mut self, predicate: P) -> Option<Self::Item>
          where Self: Sized,
                P: FnMut(&Self::Item) -> bool { ... }
        fn find_map<B, F>(&mut self, f: F) -> Option<B>
          where Self: Sized,
                F: FnMut(Self::Item) -> Option<B> { ... }
        fn try_find<F, R>(
            &mut self,
            f: F
        ) -> <<R as Try>::Residual as Residual<Option<Self::Item>>>::TryType
          where Self: Sized,
                F: FnMut(&Self::Item) -> R,
                R: Try<Output = bool>,
                R::Residual: Residual<Option<Self::Item>> { ... }
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
                F: FnMut(&Self::Item, &Self::Item) -> Option<Ordering> { ... }
        fn is_sorted_by_key<F, K>(self, f: F) -> bool
          where Self: Sized,
                F: FnMut(Self::Item) -> K,
                K: PartialOrd { ... }
    }
    *)
    Module Iterator.
      Module Required.
        Class Trait (Self : Set) {Item : Set} : Set := {
          Item := Item;
          next : mut_ref Self -> M (option.Option.t Item);
          (* Provided *)
          next_chunk {N : nat} : option (
            mut_ref Self ->
            M (result.Result.t (array Item) (array.IntoIter.t Item))
          );
          size_hint : option (
            ref Self -> M (usize.t * option.Option.t usize.t)
          );
          count : option (Self -> M usize.t);
          last : option (Self -> M (option.Option.t Item));
          advance_by : option (
            mut_ref Self -> usize.t ->
            M (result.Result.t unit num.NonZeroUsize.t)
          );
          nth : option (
            mut_ref Self -> usize.t ->
            M (option.Option.t Item)
          );
          step_by : option (
            Self -> usize.t -> M (adapters.step_by.StepBy.t Self)
          );
          (* Here, we do not make explicit the [IntoIterator] trait to avoid a
             circular dependency. When implementing this method in
             the [Provided] module, we should use a special axiom to request an
             implementation of the corresponding trait at runtime. *)
          chain {U U_IntoIter : Set} : option (
            Self -> U ->
            M (adapters.chain.Chain.t Self U_IntoIter)
          );
          zip {U U_IntoIter : Set} : option (
            Self -> U ->
            M (adapters.zip.Zip.t Self U_IntoIter)
          );
          position : option (
            mut_ref Self -> (Item -> M bool) -> M (option.Option.t usize.t)
          );
          (* TODO: add other fields *)
        }.
      End Required.

      Module  Provided.
      Section Provided.
        Context {Self Item : Set}.
        Context {H0 : Required.Trait Self (Item := Item)}.

        Parameter next_chunk :
          forall {N : nat},
          mut_ref Self ->
          M (result.Result.t (array Item) (array.IntoIter.t Item)).

        Parameter size_hint : ref Self -> M (usize.t * option.Option.t usize.t).

        Parameter count : Self -> M usize.t.

        Parameter last : Self -> M (option.Option.t Item).

        Parameter advance_by :
          mut_ref Self -> usize.t ->
          M (result.Result.t unit num.NonZeroUsize.t).

        Parameter nth : mut_ref Self -> usize.t -> M (option.Option.t Item).

        Parameter step_by :
          Self -> usize.t -> M (adapters.step_by.StepBy.t Self).

        Parameter chain :
          forall {U U_IntoIter : Set},
          Self -> U ->
          M (adapters.chain.Chain.t Self U_IntoIter).

        Parameter zip :
          forall {U U_IntoIter : Set},
          Self -> U ->
          M (adapters.zip.Zip.t Self U_IntoIter).

        Parameter position :
          mut_ref Self -> (Item -> M bool) -> M (option.Option.t usize.t).
      End Provided.
      End Provided.

      Class Trait (Self : Set) {Item : Set} : Set := {
        Item := Item;
        next : mut_ref Self -> M (option.Option.t Item);
        (* Provided *)
        next_chunk {N : nat} :
          mut_ref Self ->
          M (result.Result.t (array Item) (array.IntoIter.t Item));
        size_hint : ref Self -> M (usize.t * option.Option.t usize.t);
        count : Self -> M usize.t;
        last : Self -> M (option.Option.t Item);
        advance_by :
          mut_ref Self -> usize.t ->
          M (result.Result.t unit num.NonZeroUsize.t);
        nth : mut_ref Self -> usize.t -> M (option.Option.t Item);
        step_by : Self -> usize.t -> M (adapters.step_by.StepBy.t Self);
        chain {U U_IntoIter : Set} :
          Self -> U ->
          M (adapters.chain.Chain.t Self U_IntoIter);
        zip {U U_IntoIter : Set} :
          Self -> U ->
          M (adapters.zip.Zip.t Self U_IntoIter);
        position :
          mut_ref Self -> (Item -> M bool) -> M (option.Option.t usize.t);
      }.

      Global Instance From_Required (Self Item : Set)
          {H0 : Required.Trait Self (Item := Item)} :
          Trait Self (Item := Item) := {
        next := Required.next;
        (* Provided *)
        next_chunk {N : nat} := Provided.next_chunk (N := N);
        size_hint := Provided.size_hint;
        count := Provided.count;
        last := Provided.last;
        advance_by := Provided.advance_by;
        nth := Provided.nth;
        step_by := Provided.step_by;
        chain {U U_IntoIter : Set} :=
          Provided.chain (U := U) (U_IntoIter := U_IntoIter);
        zip {U U_IntoIter : Set} :=
          Provided.zip (U := U) (U_IntoIter := U_IntoIter);
        position := Provided.position;
      }.

      Module Impl.
        (*
        impl<'a, T> Iterator for Iter<'a, T>
        *)
        Global Instance Iter {T : Set} :
          traits.iterator.Iterator.Trait (slice.iter.Iter.t T) (Item := ref T).
        Admitted.

        (*
        impl<A, B> Iterator for Zip<A, B>where
          A: Iterator,
          B: Iterator,
        *)
        Global Instance Zip {A B Item_A Item_B : Set}
          (H0 : traits.iterator.Iterator.Trait A (Item := Item_A))
          (H1 : traits.iterator.Iterator.Trait B (Item := Item_B)) :
          traits.iterator.Iterator.Trait
            (adapters.zip.Zip.t A B) (Item := Item_A * Item_B).
        Admitted.
      End Impl.
    End Iterator.
  End iterator.

  Module collect.
    (*
    pub trait IntoIterator {
        type Item;
        type IntoIter: Iterator<Item = Self::Item>;

        // Required method
        fn into_iter(self) -> Self::IntoIter;
    }
    *)
    Module IntoIterator.
      (** We provide as an additional parameter the class for iterators, as
          there is a mutual dependency. *)
      Class Trait (Self : Set)
          {Item IntoIter : Set}
          {H0 : iterator.Iterator.Trait IntoIter (Item := Item)} :
          Set := {
        Item := Item;
        IntoIter := IntoIter;
        into_iter : Self -> M (IntoIter);
      }.
    End IntoIterator.

    Module Impl.
      (*
      impl<'a, T, A: Allocator> IntoIterator for &'a Vec<T, A>
      *)
      Global Instance I_ref_Vec {T A : Set}
          (H0 : core.alloc.Allocator.Trait A) :
          IntoIterator.Trait
            (ref (vec.Vec.t T A))
            (Item := ref T)
            (IntoIter := slice.iter.Iter.t T)
            (H0 := iterator.Iterator.Impl.Iter) := {
        into_iter := axiom "into_iter";
      }.

      (*
      impl<I> IntoIterator for I
      where
          I: Iterator,
      *)
      (* Global Instance I_Iterator {I Item : Set}
          (H0 : iterator.Iterator.Trait I (Item := Item)) :
          IntoIterator.Trait I (Item := Item) (IntoIter := I) := {
        into_iter := axiom "into_iter";
      }. *)

      Global Instance I_slice_Iter {T : Set} :
          IntoIterator.Trait
            (slice.iter.Iter.t T)
            (Item := ref T)
            (IntoIter := slice.iter.Iter.t T)
            (H0 := iterator.Iterator.Impl.Iter) := {
        into_iter := axiom "into_iter";
      }.
    End Impl.
  End collect.
End traits.
