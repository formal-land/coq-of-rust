//! Support for the [`proptest`](https://crates.io/crates/proptest) crate.

#![cfg(feature = "proptest")]
#![cfg_attr(docsrs, doc(cfg(feature = "proptest")))]

use crate::{Bits, Uint};
use proptest::{arbitrary::Mapped, prelude::*};

impl<const BITS: usize, const LIMBS: usize> Arbitrary for Uint<BITS, LIMBS> {
    // FEATURE: Would be nice to have a value range as parameter
    // and/or a choice between uniform and 'exponential' distribution.
    type Parameters = ();
    type Strategy = Mapped<[u64; LIMBS], Self>;

    #[inline]
    fn arbitrary() -> Self::Strategy {
        Self::arbitrary_with(())
    }

    fn arbitrary_with((): Self::Parameters) -> Self::Strategy {
        any::<[u64; LIMBS]>().prop_map(|mut limbs| {
            if LIMBS > 0 {
                limbs[LIMBS - 1] &= Self::MASK;
            }
            Self::from_limbs(limbs)
        })
    }
}

impl<const BITS: usize, const LIMBS: usize> Arbitrary for Bits<BITS, LIMBS> {
    type Parameters = <Uint<BITS, LIMBS> as Arbitrary>::Parameters;
    type Strategy = Mapped<Uint<BITS, LIMBS>, Self>;

    fn arbitrary_with(args: Self::Parameters) -> Self::Strategy {
        Uint::<BITS, LIMBS>::arbitrary_with(args).prop_map(Self::from)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{const_for, nlimbs};
    use proptest::proptest;

    #[test]
    fn test_arbitrary() {
        const_for!(BITS in SIZES {
            const LIMBS: usize = nlimbs(BITS);
            proptest!(|(n: Uint::<BITS, LIMBS>)| {
                let _ = n;
            });
        });
    }
}
