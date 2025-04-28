use core::iter::{FlatMap, IntoIterator, Iterator};
use core::marker::{Send, Sized, Sync};
use core::ops::{Fn, FnOnce};
use core::option::Option;
use core::slice::{
    Chunks, ChunksExact, ChunksExactMut, ChunksMut, RChunks, RChunksExact, RChunksExactMut,
    RChunksMut, Split, SplitMut, Windows,
};

pub trait IntoParallelIterator {
    type Iter: Iterator<Item = Self::Item>;
    type Item: Send;

    fn into_par_iter(self) -> Self::Iter;
}
impl<T: IntoIterator> IntoParallelIterator for T
where
    T::Item: Send,
{
    type Iter = T::IntoIter;
    type Item = T::Item;

    fn into_par_iter(self) -> Self::Iter {
        self.into_iter()
    }
}

pub trait IntoParallelRefIterator<'data> {
    type Iter: Iterator<Item = Self::Item>;
    type Item: Send + 'data;

    fn par_iter(&'data self) -> Self::Iter;
}

impl<'data, I: 'data + ?Sized> IntoParallelRefIterator<'data> for I
where
    &'data I: IntoParallelIterator,
{
    type Iter = <&'data I as IntoParallelIterator>::Iter;
    type Item = <&'data I as IntoParallelIterator>::Item;

    fn par_iter(&'data self) -> Self::Iter {
        self.into_par_iter()
    }
}

pub trait IntoParallelRefMutIterator<'data> {
    type Iter: Iterator<Item = Self::Item>;
    type Item: Send + 'data;

    fn par_iter_mut(&'data mut self) -> Self::Iter;
}

impl<'data, I: 'data + ?Sized> IntoParallelRefMutIterator<'data> for I
where
    &'data mut I: IntoParallelIterator,
{
    type Iter = <&'data mut I as IntoParallelIterator>::Iter;
    type Item = <&'data mut I as IntoParallelIterator>::Item;

    fn par_iter_mut(&'data mut self) -> Self::Iter {
        self.into_par_iter()
    }
}

pub trait ParallelSlice<T: Sync> {
    /// Returns a plain slice, which is used to implement the rest of the
    /// parallel methods.
    fn as_parallel_slice(&self) -> &[T];

    fn par_split<P>(&self, separator: P) -> Split<'_, T, P>
    where
        P: Fn(&T) -> bool + Sync + Send,
    {
        self.as_parallel_slice().split(separator)
    }

    fn par_windows(&self, window_size: usize) -> Windows<'_, T> {
        self.as_parallel_slice().windows(window_size)
    }

    fn par_chunks(&self, chunk_size: usize) -> Chunks<'_, T> {
        self.as_parallel_slice().chunks(chunk_size)
    }

    fn par_chunks_exact(&self, chunk_size: usize) -> ChunksExact<'_, T> {
        self.as_parallel_slice().chunks_exact(chunk_size)
    }

    fn par_rchunks(&self, chunk_size: usize) -> RChunks<'_, T> {
        self.as_parallel_slice().rchunks(chunk_size)
    }

    fn par_rchunks_exact(&self, chunk_size: usize) -> RChunksExact<'_, T> {
        self.as_parallel_slice().rchunks_exact(chunk_size)
    }
}

impl<T: Sync> ParallelSlice<T> for [T] {
    #[inline]
    fn as_parallel_slice(&self) -> &[T] {
        self
    }
}

pub trait ParallelSliceMut<T: Send> {
    /// Returns a plain mutable slice, which is used to implement the rest of
    /// the parallel methods.
    fn as_parallel_slice_mut(&mut self) -> &mut [T];

    fn par_split_mut<P>(&mut self, separator: P) -> SplitMut<'_, T, P>
    where
        P: Fn(&T) -> bool + Sync + Send,
    {
        self.as_parallel_slice_mut().split_mut(separator)
    }

    fn par_chunks_mut(&mut self, chunk_size: usize) -> ChunksMut<'_, T> {
        self.as_parallel_slice_mut().chunks_mut(chunk_size)
    }

    fn par_chunks_exact_mut(&mut self, chunk_size: usize) -> ChunksExactMut<'_, T> {
        self.as_parallel_slice_mut().chunks_exact_mut(chunk_size)
    }

    fn par_rchunks_mut(&mut self, chunk_size: usize) -> RChunksMut<'_, T> {
        self.as_parallel_slice_mut().rchunks_mut(chunk_size)
    }

    fn par_rchunks_exact_mut(&mut self, chunk_size: usize) -> RChunksExactMut<'_, T> {
        self.as_parallel_slice_mut().rchunks_exact_mut(chunk_size)
    }
}

impl<T: Send> ParallelSliceMut<T> for [T] {
    #[inline]
    fn as_parallel_slice_mut(&mut self) -> &mut [T] {
        self
    }
}

pub trait ParIterExt: Iterator {
    fn find_any<P>(self, predicate: P) -> Option<Self::Item>
    where
        P: Fn(&Self::Item) -> bool + Sync + Send;

    fn flat_map_iter<U, F>(self, map_op: F) -> FlatMap<Self, U, F>
    where
        Self: Sized,
        U: IntoIterator,
        F: Fn(Self::Item) -> U;
}

impl<T: Iterator> ParIterExt for T {
    fn find_any<P>(mut self, predicate: P) -> Option<Self::Item>
    where
        P: Fn(&Self::Item) -> bool + Sync + Send,
    {
        self.find(predicate)
    }

    fn flat_map_iter<U, F>(self, map_op: F) -> FlatMap<Self, U, F>
    where
        Self: Sized,
        U: IntoIterator,
        F: Fn(Self::Item) -> U,
    {
        self.flat_map(map_op)
    }
}

pub fn join<A, B, RA, RB>(oper_a: A, oper_b: B) -> (RA, RB)
where
    A: FnOnce() -> RA,
    B: FnOnce() -> RB,
{
    let result_a = oper_a();
    let result_b = oper_b();
    (result_a, result_b)
}

pub const fn current_num_threads() -> usize {
    1
}
