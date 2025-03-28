//! Support for the [`primitive-types`](https://crates.io/crates/primitive-types) crate.

#![cfg(feature = "primitive-types")]
#![cfg_attr(docsrs, doc(cfg(feature = "primitive-types")))]

use crate::aliases as ours;
use primitive_types::{H128, H160, H256, H512, U128, U256, U512};

macro_rules! impl_uint_froms {
    ($ours:ty, $theirs:ident) => {
        impl From<$theirs> for $ours {
            #[inline(always)]
            fn from(value: $theirs) -> Self {
                Self::from_limbs(value.0)
            }
        }

        impl From<$ours> for $theirs {
            #[inline(always)]
            fn from(value: $ours) -> Self {
                $theirs(value.into_limbs())
            }
        }
    };
}

impl_uint_froms!(ours::U128, U128);
impl_uint_froms!(ours::U256, U256);
impl_uint_froms!(ours::U512, U512);

/// Hash types (H128, H160, H256, H512) in `primitive-types` are stored as
/// big-endian order bytes.
macro_rules! impl_bits_froms {
    ($ours:ty, $theirs:ident) => {
        impl From<$theirs> for $ours {
            fn from(value: $theirs) -> Self {
                Self::from_be_bytes(value.0)
            }
        }

        impl From<$ours> for $theirs {
            fn from(value: $ours) -> Self {
                Self::from(value.to_be_bytes())
            }
        }
    };
}

impl_bits_froms!(ours::B128, H128);
impl_bits_froms!(ours::B160, H160);
impl_bits_froms!(ours::B256, H256);
impl_bits_froms!(ours::B512, H512);

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::{arbitrary::Arbitrary, proptest};

    fn test_roundtrip<Ours, Theirs>()
    where
        Ours: Clone + PartialEq + Arbitrary + From<Theirs>,
        Theirs: From<Ours>,
    {
        proptest!(|(value: Ours)| {
            let theirs: Theirs = value.clone().into();
            let ours: Ours = theirs.into();
            assert_eq!(ours, value);
        });
    }

    #[test]
    fn test_roundtrips() {
        test_roundtrip::<ours::U128, U128>();
        test_roundtrip::<ours::U256, U256>();
        test_roundtrip::<ours::U512, U512>();
        test_roundtrip::<ours::B128, H128>();
        test_roundtrip::<ours::B160, H160>();
        test_roundtrip::<ours::B256, H256>();
        test_roundtrip::<ours::B512, H512>();
    }
}
