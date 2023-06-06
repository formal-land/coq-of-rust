Require Import CoqOfRust.lib.lib.
Require Import CoqOfRust.std.alloc.
Require Import CoqOfRust.std.clone.

(* ********STRUCTS******** *)
(* 
[ ] BTreeMap
[ ] BTreeSet
[x] BinaryHeap
[ ] HashMap
[ ] HashSet
[x] LinkedList
[x] TryReserveError
[x] VecDeque 
*)

(* TODO: Add dependency for Global *)
(* 
pub struct BTreeMap<K, V, A = Global>
where
    A: Allocator + Clone,
{ /* private fields */ }
*)
Module BTreeMap.
  Record t (K V A : Set)
    (* `{Allocator.Trait A} *)
    (* `{Clone.Trait A} *)
    : Set := { }.
End BTreeMap.
Definition BTreeMap (K V : Set) (A : option Set) := 
  BTreeMap.t K V (defaultType A Global).

(* TODO: Add dependency for Global *)
(* 
pub struct BTreeSet<T, A = Global>
where
    A: Allocator + Clone,
{ /* private fields */ }
*)
Module BTreeSet.
  Record t (T A : Set)
    (* `{Allocator.Trait A} *)
    (* `{Clone.Trait A} *)
    : Set := { }.
End BTreeSet.
Definition BTreeSet (T : Set) (A : option Set) := BTreeSet.t T (defaultType A Global).

(* pub struct BinaryHeap<T> { /* private fields */ } *)
Module BinaryHeap.
  Record t (T : Set) : Set := { }.
End BinaryHeap.
Definition BinaryHeap := BinaryHeap.t.

(* TODO: Add dependency *)
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
 
