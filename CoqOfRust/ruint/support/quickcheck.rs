//! Support for the [`quickcheck`](https://crates.io/crates/quickcheck) crate.

#![cfg(feature = "quickcheck")]
#![cfg_attr(docsrs, doc(cfg(feature = "quickcheck")))]

use crate::Uint;
use quickcheck::{Arbitrary, Gen};

impl<const BITS: usize, const LIMBS: usize> Arbitrary for Uint<BITS, LIMBS> {
    fn arbitrary(g: &mut Gen) -> Self {
        let mut limbs = [0; LIMBS];
        if let Some((last, rest)) = limbs.split_last_mut() {
            for limb in rest {
                *limb = u64::arbitrary(g);
            }
            *last = u64::arbitrary(g) & Self::MASK;
        }
        Self::from_limbs(limbs)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{const_for, nlimbs};
    use quickcheck::quickcheck;

    fn test_quickcheck_inner<const BITS: usize, const LIMBS: usize>(_n: Uint<BITS, LIMBS>) -> bool {
        true
    }

    #[test]
    fn test_quickcheck() {
        const_for!(BITS in SIZES {
            const LIMBS: usize = nlimbs(BITS);
            quickcheck(test_quickcheck_inner::<BITS, LIMBS> as fn(Uint<BITS, LIMBS>) -> bool);
        });
    }
}
