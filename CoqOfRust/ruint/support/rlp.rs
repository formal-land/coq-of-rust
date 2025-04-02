//! Support for the [`rlp`](https://crates.io/crates/rlp) crate.

#![cfg(feature = "rlp")]
#![cfg_attr(docsrs, doc(cfg(feature = "rlp")))]

use crate::{Bits, Uint};
use core::cmp::Ordering;
use rlp::{Decodable, DecoderError, Encodable, Rlp, RlpStream};

/// Allows a [`Uint`] to be serialized as RLP.
///
/// See <https://eth.wiki/en/fundamentals/rlp>
impl<const BITS: usize, const LIMBS: usize> Encodable for Uint<BITS, LIMBS> {
    fn rlp_append(&self, s: &mut RlpStream) {
        let bytes = self.to_be_bytes_vec();
        // Strip most-significant zeros.
        let bytes = trim_leading_zeros(&bytes);
        bytes.rlp_append(s);
    }
}

/// Allows a [`Uint`] to be deserialized from RLP.
///
/// See <https://eth.wiki/en/fundamentals/rlp>
impl<const BITS: usize, const LIMBS: usize> Decodable for Uint<BITS, LIMBS> {
    fn decode(s: &Rlp) -> Result<Self, DecoderError> {
        Self::try_from_be_slice(s.data()?).ok_or(DecoderError::Custom(
            "RLP integer value too large for Uint.",
        ))
    }
}

/// Allows a [`Bits`] to be serialized as RLP.
///
/// See <https://eth.wiki/en/fundamentals/rlp>
impl<const BITS: usize, const LIMBS: usize> Encodable for Bits<BITS, LIMBS> {
    #[allow(clippy::collection_is_never_read)] // have to use vec
    fn rlp_append(&self, s: &mut RlpStream) {
        #[allow(clippy::collection_is_never_read)]
        let bytes = self.to_be_bytes_vec();
        bytes.rlp_append(s);
    }
}

/// Allows a [`Bits`] to be deserialized from RLP.
///
/// See <https://eth.wiki/en/fundamentals/rlp>
impl<const BITS: usize, const LIMBS: usize> Decodable for Bits<BITS, LIMBS> {
    fn decode(s: &Rlp) -> Result<Self, DecoderError> {
        s.decoder()
            .decode_value(|bytes| match bytes.len().cmp(&Self::BYTES) {
                Ordering::Less => Err(DecoderError::RlpIsTooShort),
                Ordering::Greater => Err(DecoderError::RlpIsTooBig),
                Ordering::Equal => Self::try_from_be_slice(bytes).ok_or(DecoderError::RlpIsTooBig),
            })
    }
}

fn trim_leading_zeros(bytes: &[u8]) -> &[u8] {
    let zeros = bytes.iter().position(|&b| b != 0).unwrap_or(bytes.len());
    &bytes[zeros..]
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{
        aliases::{B160, U0, U256},
        const_for, nlimbs,
    };
    use hex_literal::hex;
    use proptest::proptest;

    #[test]
    fn test_uint_rlp() {
        // See <https://github.com/paritytech/parity-common/blob/436cb0827f0e3238ccb80d7d453f756d126c0615/rlp/tests/tests.rs#L214>
        assert_eq!(U0::from(0).rlp_bytes()[..], hex!("80"));
        assert_eq!(U256::from(0).rlp_bytes()[..], hex!("80"));
        assert_eq!(U256::from(15).rlp_bytes()[..], hex!("0f"));
        assert_eq!(U256::from(1024).rlp_bytes()[..], hex!("820400"));
        assert_eq!(U256::from(0x1234_5678).rlp_bytes()[..], hex!("8412345678"));
    }

    #[test]
    fn test_uint_roundtrip() {
        const_for!(BITS in SIZES {
            const LIMBS: usize = nlimbs(BITS);
            proptest!(|(value: Uint<BITS, LIMBS>)| {
                let serialized = value.rlp_bytes();
                let deserialized = Uint::decode(&Rlp::new(&serialized)).unwrap();
                assert_eq!(value, deserialized);
            });
        });
    }

    #[test]
    fn test_bits_rlp() {
        // See <https://github.com/paritytech/parity-common/blob/09371a1c63e315c9c390a9c761f1863a5b97be47/rlp/tests/tests.rs#L271-L278>
        assert_eq!(
            "0xef2d6d194084c2de36e0dabfce45d046b37d1106"
                .parse::<B160>()
                .unwrap()
                .rlp_bytes()[..],
            hex!("94ef2d6d194084c2de36e0dabfce45d046b37d1106")
        );
    }

    #[test]
    fn test_bits_roundtrip() {
        const_for!(BITS in SIZES {
            const LIMBS: usize = nlimbs(BITS);
            proptest!(|(value: Bits<BITS, LIMBS>)| {
                let serialized = value.rlp_bytes();
                let deserialized = Bits::decode(&Rlp::new(&serialized)).unwrap();
                assert_eq!(value, deserialized);
            });
        });
    }
}
