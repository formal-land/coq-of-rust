#![no_std]
#![cfg_attr(
    all(
        feature = "nightly-features",
        target_arch = "x86_64",
        target_feature = "avx512f"
    ),
    feature(stdarch_x86_avx512)
)]

extern crate alloc;

mod baby_bear;
mod extension;
mod mds;
mod poseidon2;

pub use baby_bear::*;
pub use mds::*;
pub use poseidon2::*;

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
mod aarch64_neon;
#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
pub use aarch64_neon::*;

#[cfg(all(
    target_arch = "x86_64",
    target_feature = "avx2",
    not(all(feature = "nightly-features", target_feature = "avx512f"))
))]
mod x86_64_avx2;
#[cfg(all(
    target_arch = "x86_64",
    target_feature = "avx2",
    not(all(feature = "nightly-features", target_feature = "avx512f"))
))]
pub use x86_64_avx2::*;

#[cfg(all(
    feature = "nightly-features",
    target_arch = "x86_64",
    target_feature = "avx512f"
))]
mod x86_64_avx512;
#[cfg(all(
    feature = "nightly-features",
    target_arch = "x86_64",
    target_feature = "avx512f"
))]
pub use x86_64_avx512::*;
