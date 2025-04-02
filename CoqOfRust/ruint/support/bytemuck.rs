//! Support for the [`bytemuck`](https://crates.io/crates/bytemuck) crate.
#![cfg(feature = "bytemuck")]
#![cfg_attr(docsrs, doc(cfg(feature = "bytemuck")))]

use crate::Uint;
use bytemuck::{Pod, Zeroable};

// Implement Zeroable for all `Uint` types.
unsafe impl<const BITS: usize, const LIMBS: usize> Zeroable for Uint<{ BITS }, { LIMBS }> {}

// Implement the `Pod` trait for `Uint` types with a size that is a multiple of
// 64, up to 1024. Note that implementors must have a size that is divisible by
// 64, and using `Uint` sizes not divisible by 64 would violate Pod's
// guarantees potentially leading to undefined behavior.
macro_rules! impl_pod {
    ($(($bits:expr, $limbs:expr)),+ $(,)?) => {
        $(
            unsafe impl Pod for Uint<{$bits}, $limbs> {}
        )+
    };
}

impl_pod! {
    (64, 1),
    (128, 2),
    (192, 3),
    (256, 4),
    (320, 5),
    (384, 6),
    (448, 7),
    (512, 8),
    (576, 9),
    (640, 10),
    (704, 11),
    (768, 12),
    (832, 13),
    (896, 14),
    (960, 15),
    (1024, 16),
}

#[cfg(test)]
mod tests {
    use bytemuck::{Pod, Zeroable};
    use ruint::Uint;

    #[test]
    fn test_uint_pod() {
        test_pod::<64, 1>();
        test_pod::<128, 2>();
        test_pod::<192, 3>();
        test_pod::<256, 4>();
        test_pod::<320, 5>();
        test_pod::<384, 6>();
        test_pod::<448, 7>();
        test_pod::<512, 8>();
        test_pod::<576, 9>();
        test_pod::<640, 10>();
        test_pod::<704, 11>();
        test_pod::<768, 12>();
        test_pod::<832, 13>();
        test_pod::<896, 14>();
        test_pod::<960, 15>();
        test_pod::<1024, 16>();
    }

    fn test_pod<const BITS: usize, const LIMBS: usize>()
    where
        Uint<{ BITS }, { LIMBS }>: Zeroable + Pod + Eq + Default,
    {
        let val = Uint::<{ BITS }, { LIMBS }>::default();
        let bytes = bytemuck::bytes_of(&val);

        assert_eq!(
            bytes.len(),
            std::mem::size_of::<Uint<{ BITS }, { LIMBS }>>()
        );

        let zeroed_val: Uint<{ BITS }, { LIMBS }> = Zeroable::zeroed();
        assert_eq!(zeroed_val, Uint::<{ BITS }, { LIMBS }>::default());
    }
}
