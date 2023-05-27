Require Import CoqOfRust.lib.lib.
Require Import CoqOfRust.std.alloc.

(* ********STRUCTS******** *)
(* 
[ ] BTreeMap
[ ] BTreeSet
[ ] BinaryHeap
[ ] HashMap
[ ] HashSet
[ ] LinkedList
[ ] TryReserveError
[ ] VecDeque 
*)

(* NOTE: Bugged: how to translate type param with a default type in this case? *)
(* 
pub struct BTreeMap<K, V, A = Global>
where
    A: Allocator + Clone,
{ /* private fields */ }
*)
Module BTreeMap.
  Record t (K V : Set) (A : option Set) 
    `{Allocator.Trait A}
    `{Clone.Trait A}
    : Set := { }.
End BTreeMap.
Definition BTreeMap := BTreeMap.t.

(* 
pub struct BTreeSet<T, A = Global>
where
    A: Allocator + Clone,
{ /* private fields */ }
*)
Module BTreeSet.
  Record t (T : Set) (A : option Set) 
    `{Allocator.Trait A}
    `{Clone.Trait A}
    : Set := { }.
End BTreeSet.
Definition BTreeSet := BTreeSet.t.

Module BinaryHeap.
  Record t : Set := { }.
End BinaryHeap.
Definition BinaryHeap := BinaryHeap.t.

Module HashMap.
  Record t : Set := { }.
End HashMap.
Definition HashMap := HashMap.t.

Module HashSet.
  Record t : Set := { }.
End HashSet.
Definition HashSet := HashSet.t.

Module LinkedList.
  Record t : Set := { }.
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
 

(* ********MODULES******** *)
(* 
[ ] binary_heap
[ ] btree_map
[ ] btree_set
[ ] hash_map
[ ] hash_set
[ ] linked_list
[ ] vec_deque 
*)

Module binary_heap.
End binary_heap.

Module btree_map.
End btree_map.

Module btree_set.
End btree_set.

Module hash_map.
End hash_map.

Module hash_set.
End hash_set.

Module linked_list.
End linked_list.

Module vec_deque.
End vec_deque.
 
