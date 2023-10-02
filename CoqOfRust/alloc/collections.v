Require Import CoqOfRust.Monad.
Require Import CoqOfRust.lib.lib.
Require CoqOfRust.core.alloc.
Require CoqOfRust.core.clone.

Module btree. Module map.
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
  Definition Cursor := Cursor.t.

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
  Definition CursorMut (K V : Set) (A : option Set) := 
    CursorMut.t K V (defaultType A alloc.Global).

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
  Definition DrainFilter (K V : Set) (A : option Set)
    `{alloc.Allocator.Trait (defaultType A alloc.Global)}
    `{core.clone.Clone.Trait (defaultType A alloc.Global)}
    : Set :=
    DrainFilter.t K V (defaultType A alloc.Global).

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
  Definition OccupiedEntry (K V : Set) (A : option Set)
    `{alloc.Allocator.Trait (defaultType A alloc.Global)}
    `{core.clone.Clone.Trait (defaultType A alloc.Global)}
    : Set :=
    OccupiedEntry.t K V (defaultType A alloc.Global).

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
      entry : OccupiedEntry K V (Some A);
      value : V;
    }.
  End OccupiedError.
  Definition OccupiedError (K V : Set) (A : option Set)
    `{alloc.Allocator.Trait (defaultType A alloc.Global)}
    `{core.clone.Clone.Trait (defaultType A alloc.Global)}
    : Set :=
    OccupiedError.t K V (defaultType A alloc.Global).
  
  (* 
  pub struct BTreeMap<K, V, A = Global>
  where
      A: Allocator + Clone,
  { /* private fields */ }
  *)
  Module BTreeMap.
    Parameter t : forall (K V A : Set) 
      `{alloc.Allocator.Trait A}
      `{core.clone.Clone.Trait A},
      Set.

    Module Default.
      Definition A : Set := alloc.Global.
    End Default.
  End BTreeMap.
  Definition BTreeMap (K V A : Set)
    `{alloc.Allocator.Trait A} `{core.clone.Clone.Trait A}
    : Set :=
    BTreeMap.t K V A.

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
  Definition IntoIter (K V : Set) (A : option Set)
    `{alloc.Allocator.Trait (defaultType A alloc.Global)}
    `{core.clone.Clone.Trait (defaultType A alloc.Global)}
    : Set :=
    IntoIter.t K V (defaultType A alloc.Global).

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
  Definition IntoKeys (K V : Set) (A : option Set)
    `{alloc.Allocator.Trait (defaultType A alloc.Global)}
    `{core.clone.Clone.Trait (defaultType A alloc.Global)}
    : Set :=
    IntoKeys.t K V (defaultType A alloc.Global).

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
  Definition IntoValues (K V : Set) (A : option Set)
    `{alloc.Allocator.Trait (defaultType A alloc.Global)}
    `{core.clone.Clone.Trait (defaultType A alloc.Global)}
    : Set :=
    IntoValues.t K V (defaultType A alloc.Global).

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
  Definition Iter := Iter.t.
  
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
  Definition IterMut := IterMut.t.
  
  (* pub struct Keys<'a, K, V> { /* private fields */ } *)
  Module Keys.
    Parameter t : Set -> Set -> Set.
  End Keys.
  Definition Keys := Keys.t.

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
  Definition Range := Range.t.

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
  Definition RangeMut := RangeMut.t.
  
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
  Definition VacantEntry (K V : Set) (A : option Set)
    `{alloc.Allocator.Trait (defaultType A alloc.Global)}
    `{core.clone.Clone.Trait (defaultType A alloc.Global)}
    : Set :=
    VacantEntry.t K V (defaultType A alloc.Global).
  
  (* pub struct Values<'a, K, V> { /* private fields */ } *)
  Module Values.
    Parameter t : Set -> Set -> Set.
  End Values.
  Definition Values := Values.t.
  
  (* pub struct ValuesMut<'a, K, V> { /* private fields */ } *)
  Module ValuesMut.
    Parameter t : Set -> Set -> Set.
  End ValuesMut.
  Definition ValuesMut := ValuesMut.t.
  
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
  Definition Entry (K V : Set) (A : option Set)
    `{alloc.Allocator.Trait (defaultType A alloc.Global)}
    `{core.clone.Clone.Trait (defaultType A alloc.Global)}
    : Set :=
    Entry.t K V (defaultType A alloc.Global).
End map. End btree.
