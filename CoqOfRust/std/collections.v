Require Import CoqOfRust.lib.lib.
Require Import CoqOfRust.std.alloc.
Require Import CoqOfRust.std.clone.
Require Import CoqOfRust.std.cmp.


(* ********MODULES******** *)
(* 
[x] binary_heap
[x] btree_map
[ ] btree_set
[ ] hash_map
[ ] hash_set
[ ] linked_list
[ ] vec_deque 
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
  [ ] DrainFilter
  [ ] BTreeSet
  [ ] Difference
  [ ] Intersection
  [ ] IntoIter
  [ ] Iter
  [ ] Range
  [ ] SymmetricDifference
  [ ] Union
  *)
End btree_set.

Module hash_map.
  (* ********STRUCTS******** *)
  (* 
  [ ] DrainFilter
  [ ] OccupiedError
  [ ] RawEntryBuilder
  [ ] RawEntryBuilderMut
  [ ] RawOccupiedEntryMut
  [ ] RawVacantEntryMut
  [ ] DefaultHasher
  [ ] Drain
  [ ] HashMap
  [ ] IntoIter
  [ ] IntoKeys
  [ ] IntoValues
  [ ] Iter
  [ ] IterMut
  [ ] Keys
  [ ] OccupiedEntry
  [ ] RandomState
  [ ] VacantEntry
  [ ] Values
  [ ] ValuesMut
  *)

  (* ********ENUMS******** *)
  (* 
  [ ] RawEntryMut
  [ ] Entry
  *)
End hash_map.

Module hash_set.
End hash_set.

Module linked_list.
End linked_list.

Module vec_deque.
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