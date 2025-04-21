#![no_std]

#[cfg(feature = "parallel")]
pub mod prelude {
    use core::marker::{Send, Sync};
    use core::ops::Fn;

    pub use rayon::prelude::*;
    pub use rayon::{current_num_threads, join};

    pub trait SharedExt: ParallelIterator {
        fn par_fold_reduce<Acc, Id, F, R>(self, identity: Id, fold_op: F, reduce_op: R) -> Acc
        where
            Acc: Send,
            Id: Fn() -> Acc + Sync + Send,
            F: Fn(Acc, Self::Item) -> Acc + Sync + Send,
            R: Fn(Acc, Acc) -> Acc + Sync + Send;
    }

    impl<I: ParallelIterator> SharedExt for I {
        #[inline]
        fn par_fold_reduce<Acc, Id, F, R>(self, identity: Id, fold_op: F, reduce_op: R) -> Acc
        where
            Acc: Send,
            Id: Fn() -> Acc + Sync + Send,
            F: Fn(Acc, Self::Item) -> Acc + Sync + Send,
            R: Fn(Acc, Acc) -> Acc + Sync + Send,
        {
            self.fold(&identity, fold_op).reduce(&identity, reduce_op)
        }
    }
}

#[cfg(feature = "parallel")]
pub mod iter {
    pub use rayon::iter::{repeat, repeatn as repeat_n};
}

#[cfg(not(feature = "parallel"))]
mod serial;

#[cfg(not(feature = "parallel"))]
pub mod prelude {
    pub use core::iter::{
        ExactSizeIterator as IndexedParallelIterator, Iterator as ParallelIterator,
    };
    use core::marker::{Send, Sync};
    use core::ops::Fn;

    pub use super::serial::*;

    pub trait SharedExt: ParallelIterator {
        fn par_fold_reduce<Acc, Id, F, R>(self, identity: Id, fold_op: F, reduce_op: R) -> Acc
        where
            Acc: Send,
            Id: Fn() -> Acc + Sync + Send,
            F: Fn(Acc, Self::Item) -> Acc + Sync + Send,
            R: Fn(Acc, Acc) -> Acc + Sync + Send;
    }

    impl<I: ParallelIterator> SharedExt for I {
        #[inline]
        fn par_fold_reduce<Acc, Id, F, R>(self, identity: Id, fold_op: F, _reduce_op: R) -> Acc
        where
            Acc: Send,
            Id: Fn() -> Acc + Sync + Send,
            F: Fn(Acc, Self::Item) -> Acc + Sync + Send,
            R: Fn(Acc, Acc) -> Acc + Sync + Send,
        {
            self.fold(identity(), fold_op)
        }
    }
}

#[cfg(not(feature = "parallel"))]
pub mod iter {
    pub use core::iter::{repeat, repeat_n};
}
