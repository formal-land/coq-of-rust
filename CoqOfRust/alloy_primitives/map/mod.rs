//! Re-exports of map types and utilities.
//!
//! This module exports the following types:
//! - [`HashMap`] and [`HashSet`] from the standard library or `hashbrown` crate. The
//!   "map-hashbrown" feature can be used to force the use of `hashbrown`, and is required in
//!   `no_std` environments.
//! - [`IndexMap`] and [`IndexSet`] from the `indexmap` crate, if the "map-indexmap" feature is
//!   enabled.
//! - The previously-listed hash map types prefixed with `Fb`. These are type aliases with
//!   [`FixedBytes<N>`][fb] as the key, and [`FbBuildHasher`] as the hasher builder. This hasher is
//!   optimized for hashing fixed-size byte arrays, and wraps around the default hasher builder. It
//!   performs best when the hasher is `fxhash`, which is enabled by default with the "map-fxhash"
//!   feature.
//! - The previously-listed hash map types prefixed with [`Selector`], [`Address`], and [`B256`].
//!   These use [`FbBuildHasher`] with the respective fixed-size byte array as the key. See the
//!   previous point for more information.
//!
//! Unless specified otherwise, the default hasher builder used by these types is
//! [`DefaultHashBuilder`]. This hasher prioritizes speed over security. Users who require HashDoS
//! resistance should enable the "rand" feature so that the hasher is initialized using a random
//! seed.
//!
//! Note that using the types provided in this module may require using different APIs than the
//! standard library as they might not be generic over the hasher state, such as using
//! `HashMap::default()` instead of `HashMap::new()`.
//!
//! [fb]: crate::FixedBytes
//! [`Selector`]: crate::Selector
//! [`Address`]: crate::Address
//! [`B256`]: crate::B256

use cfg_if::cfg_if;

mod fixed;
pub use fixed::*;

// The `HashMap` implementation.
// Use `hashbrown` if requested with "map-hashbrown" or required by `no_std`.
cfg_if! {
    if #[cfg(any(feature = "map-hashbrown", not(feature = "std")))] {
        use hashbrown as imp;
    } else {
        use hashbrown as _;
        use std::collections as imp;
    }
}

#[doc(no_inline)]
pub use imp::{hash_map, hash_map::Entry, hash_set};

/// A [`HashMap`](imp::HashMap) using the [default hasher](DefaultHasher).
///
/// See [`HashMap`](imp::HashMap) for more information.
pub type HashMap<K, V, S = DefaultHashBuilder> = imp::HashMap<K, V, S>;
/// A [`HashSet`](imp::HashSet) using the [default hasher](DefaultHasher).
///
/// See [`HashSet`](imp::HashSet) for more information.
pub type HashSet<V, S = DefaultHashBuilder> = imp::HashSet<V, S>;

// Faster hashers.
cfg_if! {
    if #[cfg(feature = "map-fxhash")] {
        #[doc(no_inline)]
        pub use rustc_hash::{self, FxHasher};

        cfg_if! {
            if #[cfg(all(feature = "std", feature = "rand"))] {
                // use rustc_hash::FxRandomState as FxBuildHasherInner;

                // TODO: Polyfill for https://github.com/rust-lang/rustc-hash/pull/52/
                #[allow(missing_debug_implementations, missing_copy_implementations)]
                #[doc(hidden)]
                #[derive(Clone)]
                pub struct FxBuildHasherInner(usize);

                impl Default for FxBuildHasherInner {
                    // Copied from `FxRandomState::new`.
                    fn default() -> Self {
                        use rand::Rng;
                        use std::{cell::Cell, thread_local};

                        thread_local!(static SEED: Cell<usize> = {
                            Cell::new(rand::thread_rng().gen())
                        });

                        SEED.with(|seed| {
                            let s = seed.get();
                            seed.set(s.wrapping_add(1));
                            Self(s)
                        })
                    }
                }

                impl core::hash::BuildHasher for FxBuildHasherInner {
                    type Hasher = rustc_hash::FxHasher;

                    #[inline]
                    fn build_hasher(&self) -> Self::Hasher {
                        rustc_hash::FxHasher::with_seed(self.0)
                    }
                }
            } else {
                use rustc_hash::FxBuildHasher as FxBuildHasherInner;
            }
        }

        /// The [`FxHasher`] hasher builder.
        ///
        /// This is [`rustc_hash::FxBuildHasher`], unless both the "std" and "rand" features are
        /// enabled, in which case it will be [`rustc_hash::FxRandomState`] for better security at
        /// very little cost.
        pub type FxBuildHasher = FxBuildHasherInner;
    }
}

// Default hasher.
cfg_if! {
    // TODO: Use `foldhash` in zkVM when it's supported.
    if #[cfg(all(feature = "map-foldhash", not(target_os = "zkvm")))] {
        type DefaultHashBuilderInner = foldhash::fast::RandomState;
    } else if #[cfg(feature = "map-fxhash")] {
        type DefaultHashBuilderInner = FxBuildHasher;
    } else if #[cfg(any(feature = "map-hashbrown", not(feature = "std")))] {
        type DefaultHashBuilderInner = hashbrown::DefaultHashBuilder;
    } else {
        type DefaultHashBuilderInner = std::collections::hash_map::RandomState;
    }
}
/// The default [`BuildHasher`](core::hash::BuildHasher) used by [`HashMap`] and [`HashSet`].
///
/// See [the module documentation](self) for more information on the default hasher.
pub type DefaultHashBuilder = DefaultHashBuilderInner;
/// The default [`Hasher`](core::hash::Hasher) used by [`HashMap`] and [`HashSet`].
///
/// See [the module documentation](self) for more information on the default hasher.
pub type DefaultHasher = <DefaultHashBuilder as core::hash::BuildHasher>::Hasher;

// `indexmap` re-exports.
cfg_if! {
    if #[cfg(feature = "map-indexmap")] {
        #[doc(no_inline)]
        pub use indexmap::{self, map::Entry as IndexEntry};

        /// [`IndexMap`](indexmap::IndexMap) using the [default hasher](DefaultHasher).
        ///
        /// See [`IndexMap`](indexmap::IndexMap) for more information.
        pub type IndexMap<K, V, S = DefaultHashBuilder> = indexmap::IndexMap<K, V, S>;
        /// [`IndexSet`](indexmap::IndexSet) using the [default hasher](DefaultHasher).
        ///
        /// See [`IndexSet`](indexmap::IndexSet) for more information.
        pub type IndexSet<V, S = DefaultHashBuilder> = indexmap::IndexSet<V, S>;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[cfg_attr(miri, ignore = "foldhash queries time (orlp/foldhash#4)")]
    fn default_hasher_builder_traits() {
        let hash_builder = <DefaultHashBuilder as Default>::default();
        let _hash_builder2 = <DefaultHashBuilder as Clone>::clone(&hash_builder);
        let mut hasher =
            <DefaultHashBuilder as core::hash::BuildHasher>::build_hasher(&hash_builder);

        <DefaultHasher as core::hash::Hasher>::write_u8(&mut hasher, 0);
        let _hasher2 = <DefaultHasher as Clone>::clone(&hasher);
    }
}
