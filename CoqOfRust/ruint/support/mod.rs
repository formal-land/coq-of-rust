//! Support for external crates.

#![allow(missing_docs, clippy::missing_inline_in_public_items)]

mod alloy_rlp;
mod arbitrary;
mod ark_ff;
mod ark_ff_04;
mod bn_rs;
mod bytemuck;
mod fastrlp;
mod num_bigint;
mod num_traits;
pub mod postgres;
mod primitive_types;
mod proptest;
mod pyo3;
mod quickcheck;
mod rand;
mod rlp;
pub mod scale;
mod serde;
pub mod sqlx;
pub mod ssz;
mod valuable;
mod zeroize;

// FEATURE: Support for many more traits and crates.
// * https://crates.io/crates/der
// * https://crates.io/crates/bitvec

// * open-fastrlp

// Big int types:
// * https://crates.io/crates/crypto-bigint
// * https://crates.io/crates/rug
// * https://crates.io/crates/bigdecimal
// * https://crates.io/crates/rust_decimal

// * wasm-bindgen `JsValue` bigint: https://docs.rs/wasm-bindgen/latest/wasm_bindgen/struct.JsValue.html#method.bigint_from_str
//   or from_f64.
// * Neon `JsBigInt` once it lands: https://github.com/neon-bindings/neon/pull/861

// More databases:
// * https://crates.io/crates/diesel
