Require Import CoqOfRust.lib.lib.
Require CoqOfRust.core.alloc.
Require CoqOfRust.core.clone.

(* ********STRUCTS******** *)
(* 
[x] Cursor
[x] CursorMut
[?] DrainFilter
[x] OccupiedError
[x] BTreeMap
[x] IntoIter
[x] IntoKeys
[x] IntoValues
[x] Iter
[x] IterMut
[x] Keys
[x] OccupiedEntry
[x] Range	
[x] RangeMut
[x] VacantEntry
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
  Parameter t : Set -> Set -> Set.
End Cursor.

(* 
pub struct CursorMut<'a, K, V, A = Global>
where
    K: 'a,
    V: 'a,
{ /* private fields */ }
*)
Module CursorMut.
  Parameter t : Set -> Set -> Set -> Set.
End CursorMut.

(* 
pub struct DrainFilter<'a, K, V, F, A = Global>
where
    A: Allocator + Clone,
    F: 'a + FnMut(&K, &mut V) -> bool,
{ /* private fields */ }
*)
Module DrainFilter.
  Parameter t : forall (K V A : Set) 
    `{alloc.Allocator.Trait A}
    `{core.clone.Clone.Trait A},
    Set.
End DrainFilter.

(* 
pub struct OccupiedEntry<'a, K, V, A = Global>
where
    A: Allocator + Clone,
{ /* private fields */ }
*)
Module OccupiedEntry.
  Parameter t : forall (K V A : Set) 
    `{alloc.Allocator.Trait A}
    `{core.clone.Clone.Trait A},
    Set.
End OccupiedEntry.

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
  Record t (K V A : Set) 
    `{alloc.Allocator.Trait A}
    `{core.clone.Clone.Trait A}
  : Set := { 
    entry : OccupiedEntry.t K V A;
    value : V;
  }.
End OccupiedError.

(* 
pub struct BTreeMap<K, V, A = Global>
where
    A: Allocator + Clone,
{ /* private fields */ }
*)
Module BTreeMap.
  Parameter t : forall (K V A : Set)
    {H0 : alloc.Allocator.Trait A}
    {H1 : core.clone.Clone.Trait A},
    Set.

  Module Default.
    Definition A : Set := alloc.Global.t.
  End Default.
End BTreeMap.

(* 
pub struct IntoIter<K, V, A = Global>
where
    A: Allocator + Clone,
{ /* private fields */ }
*)
Module IntoIter.
  Parameter t : forall (K V A : Set) 
    `{alloc.Allocator.Trait A}
    `{core.clone.Clone.Trait A},
    Set.
End IntoIter.

(* 
pub struct IntoKeys<K, V, A = Global>
where
    A: Allocator + Clone,
{ /* private fields */ }
*)
Module IntoKeys.
  Parameter t : forall (K V A : Set) 
    `{alloc.Allocator.Trait A}
    `{core.clone.Clone.Trait A},
    Set.
End IntoKeys.

(* 
pub struct IntoValues<K, V, A = Global>
where
    A: Allocator + Clone,
{ /* private fields */ }
*)
Module IntoValues.
  Parameter t : forall (K V A : Set) 
    `{alloc.Allocator.Trait A}
    `{core.clone.Clone.Trait A},
    Set.
End IntoValues.

(* 
pub struct Iter<'a, K, V>
where
    K: 'a,
    V: 'a,
{ /* private fields */ }
*)
Module Iter.
  Parameter t : Set -> Set -> Set.
End Iter.

(* 
pub struct IterMut<'a, K, V>
where
    K: 'a,
    V: 'a,
{ /* private fields */ }
*)
Module IterMut.
  Parameter t : Set -> Set -> Set.
End IterMut.

(* pub struct Keys<'a, K, V> { /* private fields */ } *)
Module Keys.
  Parameter t : Set -> Set -> Set.
End Keys.

(* 
pub struct Range<'a, K, V>
where
    K: 'a,
    V: 'a,
{ /* private fields */ }
*)
Module Range.
  Parameter t : Set -> Set -> Set.
End Range.

(* 
pub struct RangeMut<'a, K, V>
where
    K: 'a,
    V: 'a,
{ /* private fields */ }
*)
Module RangeMut.
  Parameter t : Set -> Set -> Set.
End RangeMut.

(* 
pub struct VacantEntry<'a, K, V, A = Global>
where
    A: Allocator + Clone,
{ /* private fields */ }
*)
Module VacantEntry.
  Parameter t : forall (K V A : Set) 
    `{alloc.Allocator.Trait A}
    `{core.clone.Clone.Trait A},
    Set.
End VacantEntry.

(* pub struct Values<'a, K, V> { /* private fields */ } *)
Module Values.
  Parameter t : Set -> Set -> Set.
End Values.

(* pub struct ValuesMut<'a, K, V> { /* private fields */ } *)
Module ValuesMut.
  Parameter t : Set -> Set -> Set.
End ValuesMut.

(* ********ENUMS******** *)
(* 
[?] Entry
*)

(* BUGGED: same as above *)
(* 
pub enum Entry<'a, K, V, A = Global>
where
    K: 'a,
    V: 'a,
    A: Allocator + Clone,
{
    Vacant(VacantEntry<'a, K, V, A>),
    Occupied(OccupiedEntry<'a, K, V, A>),
}
*)
Module Entry.
  Inductive t (K V A : Set) 
    `{alloc.Allocator.Trait A}
    `{core.clone.Clone.Trait A}
  : Set := 
  | Vacant
  | Occupied
  .
End Entry.
