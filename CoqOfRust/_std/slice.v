Require Import CoqOfRust.lib.lib.

Require Import CoqOfRust._std.option.

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
  Record t (T : Set) (N : usize) : Set := { }.
End ArrayChunks.
Definition ArrayChunks := ArrayChunks.t.

(* 
pub struct ArrayChunksMut<'a, T, const N: usize>
where
    T: 'a,
{ /* private fields */ }
*)
Module ArrayChunksMut.
  Record t (T : Set) (N : usize) : Set := { }.
End ArrayChunksMut.
Definition ArrayChunksMut := ArrayChunksMut.t.

(* 
pub struct ArrayWindows<'a, T, const N: usize>
where
    T: 'a,
{ /* private fields */ }
*)
Module ArrayWindows.
  Record t (T : Set) (N : usize) : Set := { }.
End ArrayWindows.
Definition ArrayWindows := ArrayWindows.t.

(* 
pub struct GroupBy<'a, T, P>
where
    T: 'a,
{ /* private fields */ }
*)
Module GroupBy.
  Record t (T P : Set): Set := { }.
End GroupBy.
Definition GroupBy := GroupBy.t.

(* 
pub struct GroupByMut<'a, T, P>
where
    T: 'a,
{ /* private fields */ }
*)
Module GroupByMut.
  Record t (T P : Set): Set := { }.
End GroupByMut.
Definition GroupByMut := GroupByMut.t.

(* 
pub struct Chunks<'a, T>
where
    T: 'a,
{ /* private fields */ }
*)
Module Chunks.
  Record t (T : Set): Set := { }.
End Chunks.
Definition Chunks := Chunks.t.

(* 
pub struct ChunksExact<'a, T>
where
    T: 'a,
{ /* private fields */ }
*)
Module ChunksExact.
  Record t (T : Set): Set := { }.
End ChunksExact.
Definition ChunksExact := ChunksExact.t.

(* 
pub struct ChunksExactMut<'a, T>
where
    T: 'a,
{ /* private fields */ }
*)
Module ChunksExactMut.
  Record t (T : Set): Set := { }.
End ChunksExactMut.
Definition ChunksExactMut := ChunksExactMut.t.

(* 
pub struct ChunksMut<'a, T>
where
    T: 'a,
{ /* private fields */ }
*)
Module ChunksMut.
  Record t (T : Set): Set := { }.
End ChunksMut.
Definition ChunksMut := ChunksMut.t.

(* pub struct EscapeAscii<'a> { /* private fields */ } *)
Module EscapeAscii.
  Record t : Set := { }.
End EscapeAscii.
Definition EscapeAscii := EscapeAscii.t.

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
pub struct IterMut<'a, T>
where
    T: 'a,
{ /* private fields */ }
*)
Module IterMut.
  Record t (T : Set): Set := { }.
End IterMut.
Definition IterMut := IterMut.t.

(* 
pub struct RChunks<'a, T>
where
    T: 'a,
{ /* private fields */ }
*)
Module RChunks.
  Record t (T : Set): Set := { }.
End RChunks.
Definition RChunks := RChunks.t.

(* 
pub struct RChunksExact<'a, T>
where
    T: 'a,
{ /* private fields */ }
*)
Module RChunksExact.
  Record t (T : Set): Set := { }.
End RChunksExact.
Definition RChunksExact := RChunksExact.t.

(* 
pub struct RChunksExactMut<'a, T>
where
    T: 'a,
{ /* private fields */ }
*)
Module RChunksExactMut.
  Record t (T : Set): Set := { }.
End RChunksExactMut.
Definition RChunksExactMut := RChunksExactMut.t.

(* 
pub struct RChunksMut<'a, T>
where
    T: 'a,
{ /* private fields */ }
*)
Module RChunksMut.
  Record t (T : Set): Set := { }.
End RChunksMut.
Definition RChunksMut := RChunksMut.t.

(* BUGGED: To be translated with function support *)
(* 
pub struct RSplit<'a, T, P>
where
    T: 'a,
    P: FnMut(&T) -> bool,
{ /* private fields */ }
*)
Module RSplit.
  Record t (T P : Set): Set := { }.
End RSplit.
Definition RSplit := RSplit.t.

(* BUGGED: same as above *)
(* 
pub struct RSplitMut<'a, T, P>
where
    T: 'a,
    P: FnMut(&T) -> bool,
{ /* private fields */ }
*)
Module RSplitMut.
  Record t (T P : Set): Set := { }.
End RSplitMut.
Definition RSplitMut := RSplitMut.t.

(* BUGGED: same as above *)
(* 
pub struct RSplitN<'a, T, P>
where
    T: 'a,
    P: FnMut(&T) -> bool,
{ /* private fields */ }
*)
Module RSplitN.
  Record t (T P : Set): Set := { }.
End RSplitN.
Definition RSplitN := RSplitN.t.

(* BUGGED: same as above *)
(* 
pub struct RSplitNMut<'a, T, P>
where
    T: 'a,
    P: FnMut(&T) -> bool,
{ /* private fields */ }
*)
Module RSplitNMut.
  Record t (T P : Set): Set := { }.
End RSplitNMut.
Definition RSplitNMut := RSplitNMut.t.

(* BUGGED: same as above *)
(* 
pub struct Split<'a, T, P>
where
    T: 'a,
    P: FnMut(&T) -> bool,
{ /* private fields */ }
*)
Module Split.
  Record t (T P : Set): Set := { }.
End Split.
Definition Split := Split.t.

(* BUGGED: same as above *)
(* 
pub struct SplitInclusive<'a, T, P>
where
    T: 'a,
    P: FnMut(&T) -> bool,
{ /* private fields */ }
*)
Module SplitInclusive.
  Record t (T P : Set): Set := { }.
End SplitInclusive.
Definition SplitInclusive := SplitInclusive.t.

(* BUGGED: same as above *)
(* 
pub struct SplitInclusiveMut<'a, T, P>
where
    T: 'a,
    P: FnMut(&T) -> bool,
{ /* private fields */ }
*)
Module SplitInclusiveMut.
  Record t (T P : Set): Set := { }.
End SplitInclusiveMut.
Definition SplitInclusiveMut := SplitInclusiveMut.t.

(* BUGGED: same as above *)
(* 
pub struct SplitMut<'a, T, P>
where
    T: 'a,
    P: FnMut(&T) -> bool,
{ /* private fields */ }
*)
Module SplitMut.
  Record t (T P : Set) : Set := { }.
End SplitMut.
Definition SplitMut := SplitMut.t.

(* BUGGED: same as above *)
(* 
pub struct SplitN<'a, T, P>
where
    T: 'a,
    P: FnMut(&T) -> bool,
{ /* private fields */ }
*)
Module SplitN.
  Record t (T P : Set): Set := { }.
End SplitN.
Definition SplitN := SplitN.t.

(* BUGGED: same as above *)
(* 
pub struct SplitNMut<'a, T, P>
where
    T: 'a,
    P: FnMut(&T) -> bool,
{ /* private fields */ }
*)
Module SplitNMut.
  Record t (T P : Set): Set := { }.
End SplitNMut.
Definition SplitNMut := SplitNMut.t.

(* 
pub struct Windows<'a, T>
where
    T: 'a,
{ /* private fields */ }
*)
Module Windows.
  Record t (T : Set) : Set := { }.
End Windows.
Definition Windows := Windows.t.

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

    get : Self -> ref T -> Option Output;
    get_mut : Self -> mut_ref T -> Option (mut_ref Output);
    get_unchecked : Self -> ref T -> ref Output;
    get_unchecked_mut : Self -> mut_ref T -> mut_ref Output;
    index : Self -> ref T -> ref Output;
    index_mut : Self -> mut_ref T -> mut_ref Output;
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
