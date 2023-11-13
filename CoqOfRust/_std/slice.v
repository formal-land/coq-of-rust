Require Import CoqOfRust.lib.lib.

Require Import CoqOfRust.core.option.

(* ********STRUCTS******** *)
(*
[x] ArrayChunks
[x] ArrayChunksMut
[x] ArrayWindows
[x] GroupBy
[x] GroupByMut
[x] Chunks
[x] ChunksExact
[x] ChunksExactMut
[x] ChunksMut
[x] EscapeAscii
[x] Iter
[x] IterMut
[x] RChunks
[x] RChunksExact
[x] RChunksExactMut
[x] RChunksMut
[?] RSplit
[?] RSplitMut
[?] RSplitN
[?] RSplitNMut
[?] Split
[?] SplitInclusive
[?] SplitInclusiveMut
[?] SplitMut
[?] SplitN
[?] SplitNMut
[x] Windows
*)

(* 
pub struct ArrayChunks<'a, T, const N: usize>
where
    T: 'a,
{ /* private fields */ }
*)
Module ArrayChunks.
  Parameter t : forall (T : Set) (N : Z), Set.
End ArrayChunks.

(* 
pub struct ArrayChunksMut<'a, T, const N: usize>
where
    T: 'a,
{ /* private fields */ }
*)
Module ArrayChunksMut.
  Parameter t : forall (T : Set) (N : Z), Set.
End ArrayChunksMut.

(* 
pub struct ArrayWindows<'a, T, const N: usize>
where
    T: 'a,
{ /* private fields */ }
*)
Module ArrayWindows.
  Parameter t : forall (T : Set) (N : Z), Set.
End ArrayWindows.

(* 
pub struct GroupBy<'a, T, P>
where
    T: 'a,
{ /* private fields */ }
*)
Module GroupBy.
  Parameter t : Set -> Set -> Set.
End GroupBy.

(* 
pub struct GroupByMut<'a, T, P>
where
    T: 'a,
{ /* private fields */ }
*)
Module GroupByMut.
  Parameter t : Set -> Set -> Set.
End GroupByMut.

(* 
pub struct Chunks<'a, T>
where
    T: 'a,
{ /* private fields */ }
*)
Module Chunks.
  Parameter t : Set -> Set.
End Chunks.

(* 
pub struct ChunksExact<'a, T>
where
    T: 'a,
{ /* private fields */ }
*)
Module ChunksExact.
  Parameter t : Set -> Set.
End ChunksExact.

(* 
pub struct ChunksExactMut<'a, T>
where
    T: 'a,
{ /* private fields */ }
*)
Module ChunksExactMut.
  Parameter t : Set -> Set.
End ChunksExactMut.

(* 
pub struct ChunksMut<'a, T>
where
    T: 'a,
{ /* private fields */ }
*)
Module ChunksMut.
  Parameter t : Set -> Set.
End ChunksMut.

(* pub struct EscapeAscii<'a> { /* private fields */ } *)
Module EscapeAscii.
  Parameter t : Set.
End EscapeAscii.

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
pub struct RChunks<'a, T>
where
    T: 'a,
{ /* private fields */ }
*)
Module RChunks.
  Parameter t : Set -> Set.
End RChunks.

(* 
pub struct RChunksExact<'a, T>
where
    T: 'a,
{ /* private fields */ }
*)
Module RChunksExact.
  Parameter t : Set -> Set.
End RChunksExact.

(* 
pub struct RChunksExactMut<'a, T>
where
    T: 'a,
{ /* private fields */ }
*)
Module RChunksExactMut.
  Parameter t : Set -> Set.
End RChunksExactMut.

(* 
pub struct RChunksMut<'a, T>
where
    T: 'a,
{ /* private fields */ }
*)
Module RChunksMut.
  Parameter t : Set -> Set.
End RChunksMut.

(* BUGGED: To be translated with function support *)
(* 
pub struct RSplit<'a, T, P>
where
    T: 'a,
    P: FnMut(&T) -> bool,
{ /* private fields */ }
*)
Module RSplit.
  Parameter t : Set -> Set -> Set.
End RSplit.

(* BUGGED: same as above *)
(* 
pub struct RSplitMut<'a, T, P>
where
    T: 'a,
    P: FnMut(&T) -> bool,
{ /* private fields */ }
*)
Module RSplitMut.
  Parameter t : Set -> Set -> Set.
End RSplitMut.

(* BUGGED: same as above *)
(* 
pub struct RSplitN<'a, T, P>
where
    T: 'a,
    P: FnMut(&T) -> bool,
{ /* private fields */ }
*)
Module RSplitN.
  Parameter t : Set -> Set -> Set.
End RSplitN.

(* BUGGED: same as above *)
(* 
pub struct RSplitNMut<'a, T, P>
where
    T: 'a,
    P: FnMut(&T) -> bool,
{ /* private fields */ }
*)
Module RSplitNMut.
  Parameter t : Set -> Set -> Set.
End RSplitNMut.

(* BUGGED: same as above *)
(* 
pub struct Split<'a, T, P>
where
    T: 'a,
    P: FnMut(&T) -> bool,
{ /* private fields */ }
*)
Module Split.
  Parameter t : Set -> Set -> Set.
End Split.

(* BUGGED: same as above *)
(* 
pub struct SplitInclusive<'a, T, P>
where
    T: 'a,
    P: FnMut(&T) -> bool,
{ /* private fields */ }
*)
Module SplitInclusive.
  Parameter t : Set -> Set -> Set.
End SplitInclusive.

(* BUGGED: same as above *)
(* 
pub struct SplitInclusiveMut<'a, T, P>
where
    T: 'a,
    P: FnMut(&T) -> bool,
{ /* private fields */ }
*)
Module SplitInclusiveMut.
  Parameter t : Set -> Set -> Set.
End SplitInclusiveMut.

(* BUGGED: same as above *)
(* 
pub struct SplitMut<'a, T, P>
where
    T: 'a,
    P: FnMut(&T) -> bool,
{ /* private fields */ }
*)
Module SplitMut.
  Parameter t : Set -> Set -> Set.
End SplitMut.

(* BUGGED: same as above *)
(* 
pub struct SplitN<'a, T, P>
where
    T: 'a,
    P: FnMut(&T) -> bool,
{ /* private fields */ }
*)
Module SplitN.
  Parameter t : Set -> Set -> Set.
End SplitN.

(* BUGGED: same as above *)
(* 
pub struct SplitNMut<'a, T, P>
where
    T: 'a,
    P: FnMut(&T) -> bool,
{ /* private fields */ }
*)
Module SplitNMut.
  Parameter t : Set -> Set -> Set.
End SplitNMut.

(* 
pub struct Windows<'a, T>
where
    T: 'a,
{ /* private fields */ }
*)
Module Windows.
  Parameter t : Set -> Set.
End Windows.

(* ********TRAITS******** *)
(*
[x] Concat
[x] Join
[x] SliceIndex
*)
(* 
pub trait Concat<Item>
where
    Item: ?Sized,
{
    type Output;

    // Required method
    fn concat(slice: &Self) -> Self::Output;
}
*)
Module Concat.
  Class Trait (Self Item Output: Set) : Set := { 
    Item := Item;
    Output := Output;

    concat : ref Self -> Output;
  }.
End Concat.

(* 
pub trait Join<Separator> {
    type Output;

    // Required method
    fn join(slice: &Self, sep: Separator) -> Self::Output;
}
*)
Module Join.
  Class Trait (Self Separator Output : Set) : Set := { 
    Separator := Separator;
    Output := Output;

    join : ref Self -> Separator -> Output;
  }.
End Join.

(* 
pub unsafe trait SliceIndex<T>: Sealed
where
    T: ?Sized,
{
    type Output: ?Sized;

    // Required methods
    fn get(self, slice: &T) -> Option<&Self::Output>;
    fn get_mut(self, slice: &mut T) -> Option<&mut Self::Output>;
    unsafe fn get_unchecked(self, slice: *const T) -> *const Self::Output;
    unsafe fn get_unchecked_mut(self, slice: *mut T) -> *mut Self::Output;
    fn index(self, slice: &T) -> &Self::Output;
    fn index_mut(self, slice: &mut T) -> &mut Self::Output;
}
*)
Module SliceIndex.
  Class Trait (Self T Output : Set) : Set := { 
    Output := Output;

    get :
      M.Val Self ->
      M.Val (ref T) ->
      M (M.Val (Option.t Output));
    get_mut :
      M.Val Self ->
      M.Val (mut_ref T) ->
      M (M.Val (Option.t (mut_ref Output)));
    get_unchecked :
      M.Val Self ->
      M.Val (ref T) ->
      M (M.Val (ref Output));
    get_unchecked_mut :
      M.Val Self ->
      M.Val (mut_ref T) ->
      M (M.Val (mut_ref Output));
    index :
      M.Val Self ->
      M.Val (ref T) ->
      M (M.Val (ref Output));
    index_mut :
      M.Val Self ->
      M.Val (mut_ref T) ->
      M (M.Val (mut_ref Output));
  }.
End SliceIndex.

(* ********FUNCTIONS******** *)
(*
[ ] from_mut_ptr_range
[ ] from_ptr_range
[ ] range
[ ] from_mut
[ ] from_raw_parts
[ ] from_raw_parts_mut
[ ] from_ref
*)
