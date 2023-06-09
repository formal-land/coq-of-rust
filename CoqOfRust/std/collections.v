Require Import CoqOfRust.lib.lib.
Require Import CoqOfRust.std.alloc.
Require Import CoqOfRust.std.clone.
Require Import CoqOfRust.std.cmp.


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
    Record t (T : Set) : Set := { }.
  End DrainSorted.
  Definition DrainSorted := DrainSorted.t.
  
  (* pub struct IntoIterSorted<T> { /* private fields */ } *)
  Module IntoIterSorted.
    Record t (T : Set) : Set := { }.
  End IntoIterSorted.
  Definition IntoIterSorted := IntoIterSorted.t.

  (* 
  pub struct Drain<'a, T>
    where
        T: 'a,
    { /* private fields */ }
  *)
  Module Drain.
    Record t (T : Set) : Set := { }.
  End Drain.
  Definition Drain := Drain.t.

  (* pub struct IntoIter<T> { /* private fields */ } *)
  Module IntoIter.
    Record t (T : Set) : Set := { }.
  End IntoIter.
  Definition IntoIter := IntoIter.t.

  (* 
  pub struct Iter<'a, T>
    where
        T: 'a,
    { /* private fields */ }
  *)
  Module Iter.
    Record t (T : Set): Set := { }.
  End Iter.
  Definition Iter := Iter.t.

  (* 
  pub struct PeekMut<'a, T>
    where
        T: 'a + Ord,
    { /* private fields */ }
  *)
  Module PeekMut.
    Record t (T : Set) : Set := { }.
  End PeekMut.
  Definition PeekMut (T : Set) `{Ord.Trait T} := PeekMut.t.

End binary_heap.

Module btree_map.
  (* ********STRUCTS******** *)
  (* 
  [x] Cursor
  [x] CursorMut
  [?] DrainFilter
  [?] OccupiedError
  [?] BTreeMap
  [?] IntoIter
  [?] IntoKeys
  [?] IntoValues
  [x] Iter
  [x] IterMut
  [x] Keys
  [?] OccupiedEntry
  [x] Range	
  [x] RangeMut
  [?] VacantEntry
  [x] Values
  [x] ValuesMut
  *)

  (* 
  pub struct Cursor<'a, K, V>
  where
      K: 'a,
      V: 'a,
  { /* private fields */ } 
  *)
  Module Cursor.
    Record t (K V : Set) : Set := { }.
  End Cursor.
  Definition Cursor := Cursor.t.

  (* 
  pub struct CursorMut<'a, K, V, A = Global>
  where
      K: 'a,
      V: 'a,
  { /* private fields */ }
  *)
  Module CursorMut.
    Record t (K V A) : Set := { }.
  End CursorMut.
  Definition CursorMut (K V : Set) (A : option Set) := 
    CursorMut.t K V (defaultType A Global).

  (* BUGGED: defaultType with `where` clause *)
  (* 
  pub struct DrainFilter<'a, K, V, F, A = Global>
  where
      A: Allocator + Clone,
      F: 'a + FnMut(&K, &mut V) -> bool,
  { /* private fields */ }
  *)
  Module DrainFilter.
    Record t (K V F A : Set) : Set := { }.
  End DrainFilter.
  Definition DrainFilter (K V F : Set) (A : option Set) := DrainFilter.t K V F (defaultType A Global).
  
  (* BUGGED: same as above *)
  (* 
  pub struct OccupiedError<'a, K, V, A = Global>
  where
      K: 'a,
      V: 'a,
      A: Allocator + Clone,
  {
      pub entry: OccupiedEntry<'a, K, V, A>,
      pub value: V,
  }
  *)
  Module OccupiedError.
    Record t (K V A : Set) : Set := { 
      entry : OccupiedEntry K V (Some A);
      value : V;
    }.
  End OccupiedError.
  Definition OccupiedError (K V : Set) (A : option Set) := 
    OccupiedError.t K V (defaultType A Global).
  
  (* BUGGED: same as above *)
  (* 
  pub struct BTreeMap<K, V, A = Global>
  where
      A: Allocator + Clone,
  { /* private fields */ }
  *)
  Module BTreeMap.
    Record t (K V A : Set) : Set := { }.
  End BTreeMap.
  Definition BTreeMap (K V : Set) (A : option Set) := BTreeMap.t K V (defaultType A Global).

  (* BUGGED: same as above *)
  (* 
  pub struct IntoIter<K, V, A = Global>
  where
      A: Allocator + Clone,
  { /* private fields */ }
  *)
  Module IntoIter.
    Record t (K V A : Set) : Set := { }.
  End IntoIter.
  Definition IntoIter (K V : Set) (A : option Set) := IntoIter.t K V (defaultType A Global).

  (* BUGGED: same as above *)
  (* 
  pub struct IntoKeys<K, V, A = Global>
  where
      A: Allocator + Clone,
  { /* private fields */ }
  *)
  Module IntoKeys.
    Record t (K V A : Set) : Set := { }.
  End IntoKeys.
  Definition IntoKeys (K V : Set) (A : option Set) := IntoKeys.t K V (defaultType A Global).

  (* BUGGED: same as above *)
  (* 
  pub struct IntoValues<K, V, A = Global>
  where
      A: Allocator + Clone,
  { /* private fields */ }
  *)
  Module IntoValues.
    Record t (K V A : Set) : Set := { }.
  End IntoValues.
  Definition IntoValues (K V : Set) (A : option Set) := IntoValues.t K V (defaultType A Global).

  (* 
  pub struct Iter<'a, K, V>
  where
      K: 'a,
      V: 'a,
  { /* private fields */ }
  *)
  Module Iter.
    Record t (K V : Set) : Set := { }.
  End Iter.
  Definition Iter := Iter.t.
  
  (* 
  pub struct IterMut<'a, K, V>
  where
      K: 'a,
      V: 'a,
  { /* private fields */ }
  *)
  Module IterMut.
    Record t (K V : Set) : Set := { }.
  End IterMut.
  Definition IterMut := IterMut.t.
  
  (* pub struct Keys<'a, K, V> { /* private fields */ } *)
  Module Keys.
    Record t (K V : Set) : Set := { }.
  End Keys.
  Definition Keys := Keys.t.

  (* BUGGED: same as above *)
  (* 
  pub struct OccupiedEntry<'a, K, V, A = Global>
  where
      A: Allocator + Clone,
  { /* private fields */ }
  *)
  Module OccupiedEntry.
    Record t (K V A : Set) : Set := { }.
  End OccupiedEntry.
  Definition OccupiedEntry (K V : Set) (A : option Set) := OccupiedEntry.t K V (defaultType A Global).
  
  (* 
  pub struct Range<'a, K, V>
  where
      K: 'a,
      V: 'a,
  { /* private fields */ }
  *)
  Module Range.
    Record t (K V : Set) : Set := { }.
  End Range.
  Definition Range := Range.t.

  (* 
  pub struct RangeMut<'a, K, V>
  where
      K: 'a,
      V: 'a,
  { /* private fields */ }
  *)
  Module RangeMut.
    Record t (K V : Set) : Set := { }.
  End RangeMut.
  Definition RangeMut := RangeMut.t.
  
  (* BUGGED: same as above *)
  (* 
  pub struct VacantEntry<'a, K, V, A = Global>
  where
      A: Allocator + Clone,
  { /* private fields */ }
  *)
  Module VacantEntry.
    Record t (K V A : Set) : Set := { }.
  End VacantEntry.
  Definition VacantEntry (K V : Set) (A : option Set) := VacantEntry.t K V (defaultType A Global).
  
  (* pub struct Values<'a, K, V> { /* private fields */ } *)
  Module Values.
    Record t (K V : Set) : Set := { }.
  End Values.
  Definition Values := Values.t.
  
  (* pub struct ValuesMut<'a, K, V> { /* private fields */ } *)
  Module ValuesMut.
    Record t (K V : Set) : Set := { }.
  End ValuesMut.
  Definition ValuesMut := ValuesMut.t.
  
  
  
  

  (* ********ENUMS******** *)
  (* 
  [ ] Entry
  *)
End btree_map.

Module btree_set.
  (* ********STRUCTS******** *)
  (* 
  [?] DrainFilter
  [?] BTreeSet
  [?] Difference
  [?] Intersection
  [?] IntoIter
  [x] Iter
  [x] Range
  [x] SymmetricDifference
  [x] Union
  *)
  (* BUGGED: defaultType with as, monad dependency *)
  (* 
  pub struct DrainFilter<'a, T, F, A = Global>
  where
      A: Allocator + Clone,
      T: 'a,
      F: 'a + FnMut(&T) -> bool,
  { /* private fields */ }
  *)
  Module DrainFilter.
    Record t (T F A : Set) : Set := { }.
  End DrainFilter.
  Definition DrainFilter (T F : Set) (A : option Set) := DrainFilter.t T F (defaultType A Global).

  (* BUGGED: defaultType with as clause *)
  (* 
  pub struct BTreeSet<T, A = Global>
  where
      A: Allocator + Clone,
  { /* private fields */ }
  *)
  Module BTreeSet.
    Record t (T A : Set) : Set := { }.
  End BTreeSet.
  Definition BTreeSet (T : Set) (A : option Set) := BTreeSet.t T (defaultType A Global).

  (* BUGGED: same as above *)
  (* 
  pub struct Difference<'a, T, A = Global>
  where
      T: 'a,
      A: Allocator + Clone,
  { /* private fields */ }
  *)
  Module Difference.
    Record t (T A : Set) : Set := { }.
  End Difference.
  Definition Difference (T : Set) (A : option Set) := Difference.t T (defaultType A Global).

  (* BUGGED: same as above *)
  (* 
  pub struct Intersection<'a, T, A = Global>
  where
      T: 'a,
      A: Allocator + Clone,
  { /* private fields */ }
  *)
  Module Intersection.
    Record t (T A : Set) : Set := { }.
  End Intersection.
  Definition Intersection (T : Set) (A : option Set) := Intersection.t T (defaultType A Global).

  (* BUGGED: same as above *)
  (* 
  pub struct IntoIter<T, A = Global>
  where
      A: Allocator + Clone,
  { /* private fields */ }
  *)
  Module IntoIter.
    Record t (T A : Set) : Set := { }.
  End IntoIter.
  Definition IntoIter (T : Set) (A : option Set) := IntoIter.t T (defaultType A Global).
  
  (* 
  pub struct Iter<'a, T>
  where
      T: 'a,
  { /* private fields */ }
  *)
  Module Iter.
    Record t (T : Set) : Set := { }.
  End Iter.
  Definition Iter := Iter.t.
  
  (* 
  pub struct Range<'a, T>
  where
      T: 'a,
  { /* private fields */ }
  *)
  Module Range.
    Record t (T : Set) : Set := { }.
  End Range.
  Definition Range := Range.t.
  
  (* 
  pub struct SymmetricDifference<'a, T>(_)
  where
          T: 'a;
  *)
  Module SymmetricDifference.
    Record t (T : Set) : Set := { }.
  End SymmetricDifference.
  Definition SymmetricDifference := SymmetricDifference.t.
  
  (* 
  pub struct Union<'a, T>(_)
  where
          T: 'a;
  *)
  Module Union.
    Record t (T : Set) : Set := { }.
  End Union.
  Definition Union := Union.t.
End btree_set.

Module hash_map.
  (* ********STRUCTS******** *)
  (* 
  [?] DrainFilter
  [?] OccupiedError
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
    Record t (K V F : Set) : Set := { }.
  End DrainFilter.
  Definition DrainFilter := DrainFilter.t.

  (* BUGGED: struct with type *)
  (* 
  pub struct OccupiedError<'a, K: 'a, V: 'a> {
      pub entry: OccupiedEntry<'a, K, V>,
      pub value: V,
  }
  *)
  Module OccupiedError.
    Record t (K V : Set) : Set := { 
      entry : t;
      value : t;
    }.
  End OccupiedError.
  Definition OccupiedError := OccupiedError.t.

  (* pub struct RawEntryBuilder<'a, K: 'a, V: 'a, S: 'a> { /* private fields */ } *)
  Module RawEntryBuilder.
    Record t (K V S : Set) : Set := { }.
  End RawEntryBuilder.
  Definition RawEntryBuilder := RawEntryBuilder.t.
  
  (* pub struct RawEntryBuilderMut<'a, K: 'a, V: 'a, S: 'a> { /* private fields */ } *)
  Module RawEntryBuilderMut.
    Record t (K V S : Set) : Set := { }.
  End RawEntryBuilderMut.
  Definition RawEntryBuilderMut := RawEntryBuilderMut.t.

  (* pub struct RawOccupiedEntryMut<'a, K: 'a, V: 'a, S: 'a> { /* private fields */ } *)
  Module RawOccupiedEntryMut.
    Record t (K V S : Set) : Set := { }.
  End RawOccupiedEntryMut.
  Definition RawOccupiedEntryMut := RawOccupiedEntryMut.t.
  
  (* pub struct RawVacantEntryMut<'a, K: 'a, V: 'a, S: 'a> { /* private fields */ } *)
  Module RawVacantEntryMut.
    Record t (K V S : Set) : Set := { }.
  End RawVacantEntryMut.
  Definition RawVacantEntryMut := RawVacantEntryMut.t.

  (* pub struct DefaultHasher(_); *)
  Module DefaultHasher.
    Record t : Set := { }.
  End DefaultHasher.
  Definition DefaultHasher := DefaultHasher.t.
  
  (* pub struct Drain<'a, K: 'a, V: 'a> { /* private fields */ } *)
  Module Drain.
    Record t (K V : Set) : Set := { }.
  End Drain.
  Definition Drain := Drain.t.
  
  (* pub struct RandomState { /* private fields */ } *)
  Module RandomState.
    Record t : Set := { }.
  End RandomState.
  Definition RandomState := RandomState.t.

  (* pub struct HashMap<K, V, S = RandomState> { /* private fields */ } *)
  Module HashMap.
    Record t (K V S : Set) : Set := { }.
  End HashMap.
  Definition HashMap K V (option S) := 
    HashMap.t K V (defaultType S RandomState).

  (* pub struct IntoIter<K, V> { /* private fields */ } *)
  Module IntoIter.
    Record t (K V : Set) : Set := { }.
  End IntoIter.
  Definition IntoIter := IntoIter.t.
  
  (* pub struct IntoKeys<K, V> { /* private fields */ } *)
  Module IntoKeys.
    Record t (K V : Set) : Set := { }.
  End IntoKeys.
  Definition IntoKeys := IntoKeys.t.
  
  (* pub struct IntoValues<K, V> { /* private fields */ } *)
  Module IntoValues.
    Record t (K V : Set) : Set := { }.
  End IntoValues.
  Definition IntoValues := IntoValues.t.
  
  (* pub struct Iter<'a, K: 'a, V: 'a> { /* private fields */ } *)
  Module Iter.
    Record t (K V : Set) : Set := { }.
  End Iter.
  Definition Iter := Iter.t.

  (* pub struct IterMut<'a, K: 'a, V: 'a> { /* private fields */ } *)
  Module IterMut.
    Record t (K V : Set) : Set := { }.
  End IterMut.
  Definition IterMut := IterMut.t.
  
  (* pub struct Keys<'a, K: 'a, V: 'a> { /* private fields */ } *)
  Module Keys.
    Record t (K V : Set) : Set := { }.
  End Keys.
  Definition Keys := Keys.t.
  
  (* pub struct OccupiedEntry<'a, K: 'a, V: 'a> { /* private fields */ } *)
  Module OccupiedEntry.
    Record t (K V : Set) : Set := { }.
  End OccupiedEntry.
  Definition OccupiedEntry := OccupiedEntry.t.
  
  (* pub struct VacantEntry<'a, K: 'a, V: 'a> { /* private fields */ } *)
  Module VacantEntry.
    Record t (K V : Set) : Set := { }.
  End VacantEntry.
  Definition VacantEntry := VacantEntry.t.
  
  (* pub struct Values<'a, K: 'a, V: 'a> { /* private fields */ } *)
  Module Values.
    Record t (K V : Set) : Set := { }.
  End Values.
  Definition Values := Values.t.
  
  (* pub struct ValuesMut<'a, K: 'a, V: 'a> { /* private fields */ } *)
  Module ValuesMut.
    Record t (K V : Set) : Set := { }.
  End ValuesMut.
  Definition ValuesMut := ValuesMut.t.

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
  Definition RawEntryMut := RawEntryMut.t.

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
  Definition Entry := Entry.t.
  
End hash_map.

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
    Record t (K F : Set) : Set := { }.
  End DrainFilter.
  Definition DrainFilter := DrainFilter.t.

  (* pub struct Difference<'a, T: 'a, S: 'a> { /* private fields */ } *)
  Module Difference.
    Record t (T S : Set) : Set := { }.
  End Difference.
  Definition Difference := Difference.t.
  
  (* pub struct Drain<'a, K: 'a> { /* private fields */ } *)
  Module Drain.
    Record t (K : Set) : Set := { }.
  End Drain.
  Definition Drain := Drain.t.

  (* TODO: refere to RandomState in hash_map *)
  (* pub struct HashSet<T, S = RandomState> { /* private fields */ } *)
  Module HashSet.
    Record t (T S : Set) : Set := { }.
  End HashSet.
  Definition HashSet T (option S) := HashSet.t T (defaultType S RandomState).

  (* pub struct Intersection<'a, T: 'a, S: 'a> { /* private fields */ } *)
  Module Intersection.
    Record t (T S : Set) : Set := { }.
  End Intersection.
  Definition Intersection := Intersection.t.
  
  (* pub struct IntoIter<K> { /* private fields */ } *)
  Module IntoIter.
    Record t (K : Set) : Set := { }.
  End IntoIter.
  Definition IntoIter := IntoIter.t.
  
  (* pub struct Iter<'a, K: 'a> { /* private fields */ } *)
  Module Iter.
    Record t (K : Set) : Set := { }.
  End Iter.
  Definition Iter := Iter.t.
  
  (* pub struct SymmetricDifference<'a, T: 'a, S: 'a> { /* private fields */ } *)
  Module SymmetricDifference.
    Record t (T S : Set) : Set := { }.
  End SymmetricDifference.
  Definition SymmetricDifference := SymmetricDifference.t.
  
  (* pub struct Union<'a, T: 'a, S: 'a> { /* private fields */ } *)
  Module Union.
    Record t (T S : Set) : Set := { }.
  End Union.
  Definition Union := Union.t.

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
    Record t (T : Set) : Set := { }.
  End Cursor.
  Definition Cursor := Cursor.t.
  
  (* 
  pub struct CursorMut<'a, T>
  where
      T: 'a,
  { /* private fields */ }
  *)
  Module CursorMut.
    Record t (T : Set) : Set := { }.
  End CursorMut.
  Definition CursorMut := CursorMut.t.
  
  (* BUGGED: monad function dependency *)
  (* 
  pub struct DrainFilter<'a, T, F>
  where
      T: 'a,
      F: 'a + FnMut(&mut T) -> bool,
  { /* private fields */ }
  *)
  Module DrainFilter.
    Record t (T F : Set) : Set := { }.
  End DrainFilter.
  Definition DrainFilter := DrainFilter.t.

  (* pub struct IntoIter<T> { /* private fields */ } *)
  Module IntoIter.
    Record t (T : Set) : Set := { }.
  End IntoIter.
  Definition IntoIter := IntoIter.t.
  
  (* 
  pub struct Iter<'a, T>
  where
      T: 'a,
  { /* private fields */ }
  *)
  Module Iter.
    Record t (T : Set) : Set := { }.
  End Iter.
  Definition Iter := Iter.t.

  (* 
  pub struct IterMut<'a, T>
  where
      T: 'a,
  { /* private fields */ }
  *)
  Module IterMut.
    Record t (T : Set) : Set := { }.
  End IterMut.
  Definition IterMut := IterMut.t.
  
  (* pub struct LinkedList<T> { /* private fields */ } *)
  Module LinkedList.
    Record t (T : Set) : Set := { }.
  End LinkedList.
  Definition LinkedList := LinkedList.t.
  
End linked_list.

Module vec_deque.
  (* ********STRUCTS******** *)
  (*
  [?] Drain
  [?] IntoIter
  [x] Iter
  [x] IterMut
  [?] VecDeque
  *)

  (* BUGGED: defaultType with where clause *)
  (* 
  pub struct Drain<'a, T, A = Global>
  where
      T: 'a,
      A: Allocator,
  { /* private fields */ }
  *)
  Module Drain.
    Record t (T A : Set) : Set := { }.
  End Drain.
  Definition Drain (T : Set) (A : option Set) := Drain.t T (defaultType A Global).

  (* BUGGED: same as above *)
  (* 
  pub struct IntoIter<T, A = Global>
  where
      A: Allocator,
  { /* private fields */ }
  *)
  Module IntoIter.
    Record t (T A : Set) : Set := { }.
  End IntoIter.
  Definition IntoIter (T : Set) (A : option Set) := IntoIter.t T (defaultType A Global).

  (* 
  pub struct Iter<'a, T>
  where
      T: 'a,
  { /* private fields */ }
  *)
  Module Iter.
    Record t (T : Set) : Set := { }.
  End Iter.
  Definition Iter := Iter.t.
  
  (* 
  pub struct IterMut<'a, T>
  where
      T: 'a,
  { /* private fields */ }
  *)
  Module IterMut.
    Record t (T : Set) : Set := { }.
  End IterMut.
  Definition IterMut := IterMut.t.
  
  (* BUGGED: same as above *)
  (* 
  pub struct VecDeque<T, A = Global>
  where
      A: Allocator,
  { /* private fields */ }
  *)
  Module VecDeque.
    Record t (T A : Set) : Set := { }.
  End VecDeque.
  Definition VecDeque (T : Set) (A : option Set) := VecDeque.t T (defaultType A Global).
  
  
  
  
End vec_deque.

(* ********STRUCTS******** *)
(* 
[x] BTreeMap
[x] BTreeSet
[x] BinaryHeap
[ ] HashMap
[ ] HashSet
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
  Record t (K V A : Set)
    `{Allocator.Trait A}
    `{Clone.Trait A}
    : Set := { }.
End BTreeMap.
Definition BTreeMap (K V : Set) (A : option Set) := 
  BTreeMap.t K V (defaultType A Global).

(* 
pub struct BTreeSet<T, A = Global>
where
    A: Allocator + Clone,
{ /* private fields */ }
*)
Module BTreeSet.
  Record t (T A : Set)
    `{Allocator.Trait A}
    `{Clone.Trait A}
    : Set := { }.
End BTreeSet.
Definition BTreeSet (T : Set) (A : option Set) := BTreeSet.t T (defaultType A Global).

(* pub struct BinaryHeap<T> { /* private fields */ } *)
Module BinaryHeap.
  Record t (T : Set) : Set := { }.
End BinaryHeap.
Definition BinaryHeap := BinaryHeap.t.

(* TODO: Add dependency *)
(* BUGGED: RandomState comes from the hash_map submodule. We have to put submods before these files *)
(* pub struct HashMap<K, V, S = RandomState> { /* private fields */ } *)
Module HashMap.
  Record t (K V S : Set) : Set := { }.
End HashMap.
(* Definition HashMap (K V : Set) (S : option Set) := 
  HashMap.t K V (defaultType S RandomState). *)

(* TODO: Add dependency *)
(* pub struct HashSet<T, S = RandomState> { /* private fields */ } *)
Module HashSet.
  Record t (T : Set) : Set := { }.
End HashSet.
(* Definition HashSet (T : Set) (S : option Set) := 
  HashSet.t T (defaultType S RandomState). *)

(* pub struct LinkedList<T> { /* private fields */ } *)
Module LinkedList.
  Record t (T : Set) : Set := { }.
End LinkedList.
Definition LinkedList := LinkedList.t.

Module TryReserveError.
  Record t : Set := { }.
End TryReserveError.
Definition TryReserveError := TryReserveError.t.

Module VecDeque.
  Record t : Set := { }.
End VecDeque.
Definition VecDeque := VecDeque.t.

(* ********ENUMS******** *)
(*
[ ] TryReserveErrorKind
*)
