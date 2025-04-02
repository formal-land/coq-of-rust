//! Support for the [`rand`](https://crates.io/crates/rand) crate.

#![cfg(feature = "rand")]
#![cfg_attr(docsrs, doc(cfg(feature = "rand")))]

// FEATURE: Implement the Uniform distribution.

use crate::Uint;
use rand::{
    distributions::{Distribution, Standard, Uniform},
    Rng,
};

impl<const BITS: usize, const LIMBS: usize> Distribution<Uint<BITS, LIMBS>> for Standard {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Uint<BITS, LIMBS> {
        let mut limbs = [0; LIMBS];
        if let Some((last, rest)) = limbs.split_last_mut() {
            for limb in rest {
                *limb = rng.gen();
            }
            *last = Uniform::new_inclusive(0, Uint::<BITS, LIMBS>::MASK).sample(rng);
        }
        Uint::<BITS, LIMBS>::from_limbs(limbs)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{const_for, nlimbs};

    #[test]
    fn test_rand() {
        let mut rng = rand::thread_rng();
        const_for!(BITS in SIZES {
            const LIMBS: usize = nlimbs(BITS);
            for _ in 0..1000 {
                let _: Uint<BITS, LIMBS> = rng.gen();
            }
        });
    }
}
