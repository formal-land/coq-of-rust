//! Support for the [`zeroize`](https://crates.io/crates/zeroize) crate.
//!
//! Currently only encodes to/from a big-endian byte array.

#![cfg(feature = "zeroize")]
#![cfg_attr(docsrs, doc(cfg(feature = "zeroize")))]

use crate::{Bits, Uint};
use zeroize::Zeroize;

impl<const BITS: usize, const LIMBS: usize> Zeroize for Uint<BITS, LIMBS> {
    fn zeroize(&mut self) {
        unsafe {
            // SAFETY: Setting limbs to zero always safe.
            self.as_limbs_mut().zeroize();
        }
    }
}

impl<const BITS: usize, const LIMBS: usize> Zeroize for Bits<BITS, LIMBS> {
    fn zeroize(&mut self) {
        self.as_uint_mut().zeroize();
    }
}
