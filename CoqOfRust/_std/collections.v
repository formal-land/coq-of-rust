Require Import CoqOfRust.lib.lib.
Require Import CoqOfRust.core.alloc.
Require Import CoqOfRust.core.clone.
Require Import CoqOfRust.core.cmp.


(* ********MODULES******** *)
(* 
[x] binary_heap
[x] btree_map
[x] btree_set
[x] hash_map
[x] hash_set
[x] linked_list
[x] vec_deque 
*)

Module binary_heap.
  (* ********STRUCTS******** *)
  (* 
  [x] DrainSorted
  [x] IntoIterSorted
  [x] BinaryHeap
  [x] Drain	
  [x] IntoIter
  [x] Iter
  [x] PeekMut
  *)

  (* 
  pub struct DrainSorted<'a, T>
    where
        T: Ord,
    { /* private fields */ }
  *)
  Module DrainSorted.
    Parameter t : Set -> Set.
  End DrainSorted.
  
  (* pub struct IntoIterSorted<T> { /* private fields */ } *)
  Module IntoIterSorted.
    Parameter t : Set -> Set.
  End IntoIterSorted.

  (* 
  pub struct Drain<'a, T>
    where
        T: 'a,
    { /* private fields */ }
  *)
  Module Drain.
    Parameter t : Set -> Set.
  End Drain.

  (* pub struct IntoIter<T> { /* private fields */ } *)
  Module IntoIter.
    Parameter t : Set -> Set.
  End IntoIter.

  (* 
  pub struct Iter<'a, T>
    where
        T: 'a,
    { /* private fields */ }
  *)
  Module Iter.
    Parameter t : Set -> Set.
  End Iter.

  (* 
  pub struct PeekMut<'a, T>
    where
        T: 'a + Ord,
    { /* private fields */ }
  *)
  Module PeekMut.
    Parameter t : Set -> Set.
  End PeekMut.
End binary_heap.

Module btree_set.
  (* ********STRUCTS******** *)
  (* 
  [?] DrainFilter
  [x] BTreeSet
  [x] Difference
  [x] Intersection
  [x] IntoIter
  [x] Iter
  [x] Range
  [x] SymmetricDifference
  [x] Union
  *)
  (* BUGGED: monad dependency *)
  (* 
  pub struct DrainFilter<'a, T, F, A = Global>
  where
      A: Allocator + Clone,
      T: 'a,
      F: 'a + FnMut(&T) -> bool,
  { /* private fields */ }
  *)
  Module DrainFilter.
    Parameter t : forall (T F A : Set) 
      `{Allocator.Trait A}
      `{Clone.Trait A},
      Set.
  End DrainFilter.

  (* 
  pub struct BTreeSet<T, A = Global>
  where
      A: Allocator + Clone,
  { /* private fields */ }
  *)
  Module BTreeSet.
    Parameter t : forall (T A : Set) 
      `{Allocator.Trait A}
      `{Clone.Trait A},
      Set.
  End BTreeSet.

  (* 
  pub struct Difference<'a, T, A = Global>
  where
      T: 'a,
      A: Allocator + Clone,
  { /* private fields */ }
  *)
  Module Difference.
    Parameter t : forall (T A : Set) 
      `{Allocator.Trait A}
      `{Clone.Trait A},
      Set.
  End Difference.

  (* 
  pub struct Intersection<'a, T, A = Global>
  where
      T: 'a,
      A: Allocator + Clone,
  { /* private fields */ }
  *)
  Module Intersection.
    Parameter t : forall (T A : Set) 
      `{Allocator.Trait A}
      `{Clone.Trait A},
      Set.
  End Intersection.

  (* 
  pub struct IntoIter<T, A = Global>
  where
      A: Allocator + Clone,
  { /* private fields */ }
  *)
  Module IntoIter.
    Parameter t : forall (T A : Set) 
      `{Allocator.Trait A}
      `{Clone.Trait A},
      Set.
  End IntoIter.
  
  (* 
  pub struct Iter<'a, T>
  where
      T: 'a,
  { /* private fields */ }
  *)
  Module Iter.
    Parameter t : Set -> Set.
  End Iter.
  
  (* 
  pub struct Range<'a, T>
  where
      T: 'a,
  { /* private fields */ }
  *)
  Module Range.
    Parameter t : Set -> Set.
  End Range.
  
  (* 
  pub struct SymmetricDifference<'a, T>(_)
  where
          T: 'a;
  *)
  Module SymmetricDifference.
    Parameter t : Set -> Set.
  End SymmetricDifference.
  
  (* 
  pub struct Union<'a, T>(_)
  where
          T: 'a;
  *)
  Module Union.
    Parameter t : Set -> Set.
  End Union.
End btree_set.

Module hash.
Module map.
  (* ********STRUCTS******** *)
  (* 
  [?] DrainFilter
  [x] OccupiedError
  [x] RawEntryBuilder
  [x] RawEntryBuilderMut
  [x] RawOccupiedEntryMut
  [x] RawVacantEntryMut
  [x] DefaultHasher
  [x] Drain
  [x] HashMap
  [x] IntoIter
  [x] IntoKeys
  [x] IntoValues
  [x] Iter
  [x] IterMut
  [x] Keys
  [x] OccupiedEntry
  [x] RandomState
  [x] VacantEntry
  [x] Values
  [x] ValuesMut
  *)

  (* BUGGED: monad function dependency *)
  (* 
  pub struct DrainFilter<'a, K, V, F>
  where
      F: FnMut(&K, &mut V) -> bool,
  { /* private fields */ }
  *)
  Module DrainFilter.
    Parameter t  : Set -> Set -> Set -> Set.
  End DrainFilter.

  (* pub struct OccupiedEntry<'a, K: 'a, V: 'a> { /* private fields */ } *)
  Module OccupiedEntry.
    Parameter t : Set -> Set -> Set.
  End OccupiedEntry.

  (* 
  pub struct OccupiedError<'a, K: 'a, V: 'a> {
      pub entry: OccupiedEntry<'a, K, V>,
      pub value: V,
  }
  *)
  Module OccupiedError.
    Record t (K V : Set) : Set := { 
      entry : OccupiedEntry.t K V;
      value : V;
    }.
  End OccupiedError.

  (* pub struct RawEntryBuilder<'a, K: 'a, V: 'a, S: 'a> { /* private fields */ } *)
  Module RawEntryBuilder.
    Parameter t : Set -> Set -> Set -> Set.
  End RawEntryBuilder.
  
  (* pub struct RawEntryBuilderMut<'a, K: 'a, V: 'a, S: 'a> { /* private fields */ } *)
  Module RawEntryBuilderMut.
    Parameter t : Set -> Set -> Set -> Set.
  End RawEntryBuilderMut.

  (* pub struct RawOccupiedEntryMut<'a, K: 'a, V: 'a, S: 'a> { /* private fields */ } *)
  Module RawOccupiedEntryMut.
    Parameter t : Set -> Set -> Set -> Set.
  End RawOccupiedEntryMut.
  
  (* pub struct RawVacantEntryMut<'a, K: 'a, V: 'a, S: 'a> { /* private fields */ } *)
  Module RawVacantEntryMut.
    Parameter t : Set -> Set -> Set -> Set.
  End RawVacantEntryMut.

  (* pub struct DefaultHasher(_); *)
  Module DefaultHasher.
    Parameter t : Set.
    Definition new (_ : unit) : M t. Admitted.

    Global Instance DefaultHasher_new :
      Notations.DoubleColon t "new" := {
      Notations.double_colon := new
    }.
  End DefaultHasher.

  Definition DefaultHasher := DefaultHasher.t.
  (* pub struct Drain<'a, K: 'a, V: 'a> { /* private fields */ } *)
  Module Drain.
    Parameter t : Set -> Set -> Set.
  End Drain.
  
  (* pub struct RandomState { /* private fields */ } *)
  Module RandomState.
    Parameter t : Set.
  End RandomState.

  (* pub struct HashMap<K, V, S = RandomState> { /* private fields */ } *)
  Module HashMap.
    Parameter t : Set -> Set -> Set -> Set.

    Module Default.
      Definition S : Set := RandomState.t.
    End Default.
  End HashMap.

  (* pub struct IntoIter<K, V> { /* private fields */ } *)
  Module IntoIter.
    Parameter t : Set -> Set -> Set.
  End IntoIter.
  
  (* pub struct IntoKeys<K, V> { /* private fields */ } *)
  Module IntoKeys.
    Parameter t : Set -> Set -> Set.
  End IntoKeys.
  
  (* pub struct IntoValues<K, V> { /* private fields */ } *)
  Module IntoValues.
    Parameter t : Set -> Set -> Set.
  End IntoValues.
  
  (* pub struct Iter<'a, K: 'a, V: 'a> { /* private fields */ } *)
  Module Iter.
    Parameter t : Set -> Set -> Set.
  End Iter.

  (* pub struct IterMut<'a, K: 'a, V: 'a> { /* private fields */ } *)
  Module IterMut.
    Parameter t : Set -> Set -> Set.
  End IterMut.
  
  (* pub struct Keys<'a, K: 'a, V: 'a> { /* private fields */ } *)
  Module Keys.
    Parameter t : Set -> Set -> Set.
  End Keys.
  
  (* pub struct VacantEntry<'a, K: 'a, V: 'a> { /* private fields */ } *)
  Module VacantEntry.
    Parameter t : Set -> Set -> Set.
  End VacantEntry.
  
  (* pub struct Values<'a, K: 'a, V: 'a> { /* private fields */ } *)
  Module Values.
    Parameter t : Set -> Set -> Set.
  End Values.
  
  (* pub struct ValuesMut<'a, K: 'a, V: 'a> { /* private fields */ } *)
  Module ValuesMut.
    Parameter t : Set -> Set -> Set.
  End ValuesMut.

  (* ********ENUMS******** *)
  (* 
  [?] RawEntryMut
  [?] Entry
  *)

  (* BUGGED: enum with param *)
  (* 
  pub enum RawEntryMut<'a, K: 'a, V: 'a, S: 'a> {
      Occupied(RawOccupiedEntryMut<'a, K, V, S>),
      Vacant(RawVacantEntryMut<'a, K, V, S>),
  }
  *)
  Module RawEntryMut.
    Inductive t (K V S : Set) : Set := 
    | Occupied 
    | Vacant
    .
  End RawEntryMut.

  (* 
  pub enum Entry<'a, K: 'a, V: 'a> {
      Occupied(OccupiedEntry<'a, K, V>),
      Vacant(VacantEntry<'a, K, V>),
  }
  *)
  Module Entry.
    Inductive t (K V S : Set) : Set := 
    | Occupied
    | Vacant
    .
  End Entry.
End map.
End hash.

Module hash_set.
  (* ********STRUCTS******** *)
  (*
  [?] DrainFilter
  [x] Difference
  [x] Drain
  [x] HashSet
  [x] Intersection
  [x] IntoIter
  [x] Iter
  [x] SymmetricDifference
  [x] Union
  *)

  (* BUGGED: monad function dependency *)
  (* 
  pub struct DrainFilter<'a, K, F>
  where
      F: FnMut(&K) -> bool,
  { /* private fields */ }
  *)
  Module DrainFilter.
    Parameter t : Set -> Set -> Set.
  End DrainFilter.

  (* pub struct Difference<'a, T: 'a, S: 'a> { /* private fields */ } *)
  Module Difference.
    Parameter t : Set -> Set -> Set.
  End Difference.
  
  (* pub struct Drain<'a, K: 'a> { /* private fields */ } *)
  Module Drain.
    Parameter t : Set -> Set.
  End Drain.

  (* pub struct HashSet<T, S = RandomState> { /* private fields */ } *)
  Module HashSet.
    Parameter t : Set -> Set -> Set.
  End HashSet.

  (* pub struct Intersection<'a, T: 'a, S: 'a> { /* private fields */ } *)
  Module Intersection.
    Parameter t : Set -> Set -> Set.
  End Intersection.
  
  (* pub struct IntoIter<K> { /* private fields */ } *)
  Module IntoIter.
    Parameter t : Set -> Set.
  End IntoIter.
  
  (* pub struct Iter<'a, K: 'a> { /* private fields */ } *)
  Module Iter.
    Parameter t : Set -> Set.
  End Iter.
  
  (* pub struct SymmetricDifference<'a, T: 'a, S: 'a> { /* private fields */ } *)
  Module SymmetricDifference.
    Parameter t : Set -> Set -> Set.
  End SymmetricDifference.
  
  (* pub struct Union<'a, T: 'a, S: 'a> { /* private fields */ } *)
  Module Union.
    Parameter t : Set -> Set -> Set.
  End Union.
End hash_set.

Module linked_list.
  (* ********STRUCTS******** *)
  (*
  [x] Cursor
  [x] CursorMut
  [?] DrainFilter
  [x] IntoIter
  [x] Iter
  [x] IterMut
  [x] LinkedList
  *)

  (* 
  pub struct Cursor<'a, T>
  where
      T: 'a,
  { /* private fields */ }
  *)
  Module Cursor.
    Parameter t : Set -> Set.
  End Cursor.
  
  (* 
  pub struct CursorMut<'a, T>
  where
      T: 'a,
  { /* private fields */ }
  *)
  Module CursorMut.
    Parameter t : Set -> Set.
  End CursorMut.
  
  (* BUGGED: monad function dependency *)
  (* 
  pub struct DrainFilter<'a, T, F>
  where
      T: 'a,
      F: 'a + FnMut(&mut T) -> bool,
  { /* private fields */ }
  *)
  Module DrainFilter.
    Parameter t : forall (T F : Set), Set.
  End DrainFilter.

  (* pub struct IntoIter<T> { /* private fields */ } *)
  Module IntoIter.
    Parameter t : Set -> Set.
  End IntoIter.
  
  (* 
  pub struct Iter<'a, T>
  where
      T: 'a,
  { /* private fields */ }
  *)
  Module Iter.
    Parameter t : Set -> Set.
  End Iter.

  (* 
  pub struct IterMut<'a, T>
  where
      T: 'a,
  { /* private fields */ }
  *)
  Module IterMut.
    Parameter t : Set -> Set.
  End IterMut.
  
  (* pub struct LinkedList<T> { /* private fields */ } *)
  Module LinkedList.
    Parameter t : Set -> Set.
  End LinkedList.
End linked_list.

Module vec_deque.
  (* ********STRUCTS******** *)
  (*
  [x] Drain
  [x] IntoIter
  [x] Iter
  [x] IterMut
  [x] VecDeque
  *)

  (* 
  pub struct Drain<'a, T, A = Global>
  where
      T: 'a,
      A: Allocator,
  { /* private fields */ }
  *)
  Module Drain.
    Parameter t : forall (T A : Set) `{Allocator.Trait A}, Set.
  End Drain.

  (* 
  pub struct IntoIter<T, A = Global>
  where
      A: Allocator,
  { /* private fields */ }
  *)
  Module IntoIter.
    Parameter t : forall (T A : Set) `{Allocator.Trait A}, Set.
  End IntoIter.

  (* 
  pub struct Iter<'a, T>
  where
      T: 'a,
  { /* private fields */ }
  *)
  Module Iter.
    Parameter t : Set -> Set.
  End Iter.
  
  (* 
  pub struct IterMut<'a, T>
  where
      T: 'a,
  { /* private fields */ }
  *)
  Module IterMut.
    Parameter t : Set -> Set.
  End IterMut.
  
  (* 
  pub struct VecDeque<T, A = Global>
  where
      A: Allocator,
  { /* private fields */ }
  *)
  Module VecDeque.
    Parameter t : forall (T A : Set) `{Allocator.Trait A}, Set.
  End VecDeque.
End vec_deque.

(* ********STRUCTS******** *)
(* 
[x] BTreeMap
[x] BTreeSet
[x] BinaryHeap
[x] HashMap
[x] HashSet
[x] LinkedList
[x] TryReserveError
[x] VecDeque 
*)

(* 
pub struct BTreeMap<K, V, A = Global>
where
    A: Allocator + Clone,
{ /* private fields */ }
*)
Module BTreeMap.
  Parameter t : forall (K V A : Set)
    `{Allocator.Trait A}
    `{Clone.Trait A},
    Set.
End BTreeMap.

(* 
pub struct BTreeSet<T, A = Global>
where
    A: Allocator + Clone,
{ /* private fields */ }
*)
Module BTreeSet.
  Parameter t : forall (T A : Set)
    `{Allocator.Trait A}
    `{Clone.Trait A},
    Set.
End BTreeSet.

(* pub struct BinaryHeap<T> { /* private fields */ } *)
Module BinaryHeap.
  Parameter t : Set -> Set.
End BinaryHeap.
Definition BinaryHeap := BinaryHeap.t.

(* pub struct HashSet<T, S = RandomState> { /* private fields */ } *)
Definition HashSet (T : Set) (S : Set) : Set :=
  hash_set.HashSet.t T S.

(* pub struct LinkedList<T> { /* private fields */ } *)
Module LinkedList.
  Parameter t : Set -> Set.
End LinkedList.

Module TryReserveError.
  Parameter t : Set.
End TryReserveError.

Module VecDeque.
  Parameter t : Set.
End VecDeque.

(* ********ENUMS******** *)
(*
[?] TryReserveErrorKind
*)

(* BUGGED: unfamiliar enum *)
(* 
pub enum TryReserveErrorKind {
    CapacityOverflow,
    AllocError {
        layout: Layout,
        /* private fields */
    },
}
*)
