//! The prime field `F_p` where `p = 2^31 - 1`.

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

mod complex;
mod dft;
mod extension;
mod mds;
mod mersenne_31;
mod poseidon2;
mod radix_2_dit;

pub use dft::Mersenne31Dft;
pub use mds::*;
pub use mersenne_31::*;
pub use poseidon2::*;
pub use radix_2_dit::Mersenne31ComplexRadix2Dit;

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

#[cfg(not(any(
    all(target_arch = "aarch64", target_feature = "neon"),
    all(target_arch = "x86_64", target_feature = "avx2",),
)))]
mod no_packing;
#[cfg(not(any(
    all(target_arch = "aarch64", target_feature = "neon"),
    all(target_arch = "x86_64", target_feature = "avx2",),
)))]
pub use no_packing::*;
