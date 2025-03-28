//! Support for the [`serde`](https://crates.io/crates/serde) crate.

#![cfg(feature = "serde")]
#![cfg_attr(docsrs, doc(cfg(feature = "serde")))]

use crate::{nbytes, Bits, Uint};
use core::{
    fmt::{Formatter, Result as FmtResult, Write},
    str,
};
use serde::{
    de::{Error, Unexpected, Visitor},
    Deserialize, Deserializer, Serialize, Serializer,
};

#[allow(unused_imports)]
use alloc::string::String;

/// Canonical serialization for all human-readable instances of `Uint<0, 0>`,
/// and minimal human-readable `Uint<BITS, LIMBS>::ZERO` for any bit size.
const ZERO_STR: &str = "0x0";

impl<const BITS: usize, const LIMBS: usize> Uint<BITS, LIMBS> {
    fn serialize_human_full<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        if BITS == 0 {
            return s.serialize_str(ZERO_STR);
        }

        let mut result = String::with_capacity(2 + nbytes(BITS) * 2);
        result.push_str("0x");

        self.as_le_bytes()
            .iter()
            .rev()
            .try_for_each(|byte| write!(result, "{byte:02x}"))
            .unwrap();

        s.serialize_str(&result)
    }

    fn serialize_human_minimal<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        if BITS == 0 {
            return s.serialize_str(ZERO_STR);
        }

        let le_bytes = self.as_le_bytes();
        let mut bytes = le_bytes.iter().rev().skip_while(|b| **b == 0);

        // We avoid String allocation if there is no non-0 byte
        // If there is a first byte, we allocate a string, and write the prefix
        // and first byte to it
        let mut result = match bytes.next() {
            Some(b) => {
                let mut result = String::with_capacity(2 + nbytes(BITS) * 2);
                write!(result, "0x{b:x}").unwrap();
                result
            }
            None => return s.serialize_str(ZERO_STR),
        };
        bytes
            .try_for_each(|byte| write!(result, "{byte:02x}"))
            .unwrap();

        s.serialize_str(&result)
    }

    fn serialize_binary<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        s.serialize_bytes(&self.to_be_bytes_vec())
    }
}

/// Serialize a [`Uint`] value.
///
/// For human readable formats a `0x` prefixed lower case hex string is used.
/// For binary formats a byte array is used. Leading zeros are included.
impl<const BITS: usize, const LIMBS: usize> Serialize for Uint<BITS, LIMBS> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        if serializer.is_human_readable() {
            self.serialize_human_minimal(serializer)
        } else {
            self.serialize_binary(serializer)
        }
    }
}

/// Deserialize human readable hex strings or byte arrays into hashes.
/// Hex strings can be upper/lower/mixed case, have an optional `0x` prefix, and
/// can be any length. They are interpreted big-endian.
impl<'de, const BITS: usize, const LIMBS: usize> Deserialize<'de> for Uint<BITS, LIMBS> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        if deserializer.is_human_readable() {
            deserializer.deserialize_any(HrVisitor)
        } else {
            deserializer.deserialize_bytes(ByteVisitor)
        }
    }
}

impl<const BITS: usize, const LIMBS: usize> Serialize for Bits<BITS, LIMBS> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        if serializer.is_human_readable() {
            self.as_uint().serialize_human_full(serializer)
        } else {
            self.as_uint().serialize_binary(serializer)
        }
    }
}

impl<'de, const BITS: usize, const LIMBS: usize> Deserialize<'de> for Bits<BITS, LIMBS> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        Uint::deserialize(deserializer).map(Self::from)
    }
}

/// Serde Visitor for human readable formats.
///
/// Accepts either a primitive number, a decimal or a hexadecimal string.
struct HrVisitor<const BITS: usize, const LIMBS: usize>;

impl<'de, const BITS: usize, const LIMBS: usize> Visitor<'de> for HrVisitor<BITS, LIMBS> {
    type Value = Uint<BITS, LIMBS>;

    fn expecting(&self, formatter: &mut Formatter) -> FmtResult {
        write!(formatter, "a {} byte hex string", nbytes(BITS))
    }

    fn visit_u64<E: Error>(self, v: u64) -> Result<Self::Value, E> {
        Uint::try_from(v).map_err(|_| Error::invalid_value(Unexpected::Unsigned(v), &self))
    }

    fn visit_u128<E: Error>(self, v: u128) -> Result<Self::Value, E> {
        // `Unexpected::Unsigned` cannot contain a `u128`
        Uint::try_from(v).map_err(Error::custom)
    }

    fn visit_str<E: Error>(self, value: &str) -> Result<Self::Value, E> {
        // Shortcut for common case
        if value == ZERO_STR {
            return Ok(Uint::<BITS, LIMBS>::ZERO);
        }
        // `ZERO_STR` is the only valid serialization of `Uint<0, 0>`, so if we
        // have not shortcut, we are in an error case
        if BITS == 0 {
            return Err(Error::invalid_value(Unexpected::Str(value), &self));
        }

        value
            .parse()
            .map_err(|_| Error::invalid_value(Unexpected::Str(value), &self))
    }
}

/// Serde Visitor for non-human readable formats
struct ByteVisitor<const BITS: usize, const LIMBS: usize>;

impl<'de, const BITS: usize, const LIMBS: usize> Visitor<'de> for ByteVisitor<BITS, LIMBS> {
    type Value = Uint<BITS, LIMBS>;

    fn expecting(&self, formatter: &mut Formatter) -> FmtResult {
        write!(formatter, "{BITS} bits of binary data in big endian order")
    }

    fn visit_bytes<E: Error>(self, value: &[u8]) -> Result<Self::Value, E> {
        if value.len() != nbytes(BITS) {
            return Err(Error::invalid_length(value.len(), &self));
        }
        Uint::try_from_be_slice(value).ok_or_else(|| {
            Error::invalid_value(
                Unexpected::Other(&format!("too large for Uint<{BITS}>")),
                &self,
            )
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{const_for, nlimbs};
    use proptest::proptest;

    #[allow(unused_imports)]
    use alloc::vec::Vec;

    #[test]
    fn test_serde_human_readable() {
        const_for!(BITS in SIZES {
            const LIMBS: usize = nlimbs(BITS);
            proptest!(|(value: Uint<BITS, LIMBS>)| {
                let serialized = serde_json::to_string(&value).unwrap();
                let deserialized = serde_json::from_str(&serialized).unwrap();
                assert_eq!(value, deserialized);
            });
            proptest!(|(value: Bits<BITS, LIMBS>)| {
                let serialized = serde_json::to_string(&value).unwrap();
                let deserialized = serde_json::from_str(&serialized).unwrap();
                assert_eq!(value, deserialized);
            });
        });
    }

    #[test]
    fn test_human_readable_de() {
        let jason = r#"[
            1,
            "0x1",
            "0o1",
            "0b1"
        ]"#;
        let numbers: Vec<Uint<1, 1>> = serde_json::from_str(jason).unwrap();
        uint! {
            assert_eq!(numbers, vec![1_U1, 1_U1, 1_U1, 1_U1]);
        }

        let jason = r#"[
            "",
            "0x",
            "0o",
            "0b"
        ]"#;
        let numbers: Vec<Uint<1, 1>> = serde_json::from_str(jason).unwrap();
        uint! {
            assert_eq!(numbers, vec![0_U1, 0_U1, 0_U1, 0_U1]);
        }
    }

    #[test]
    fn test_serde_machine_readable() {
        const_for!(BITS in SIZES {
            const LIMBS: usize = nlimbs(BITS);
            proptest!(|(value: Uint<BITS, LIMBS>)| {
                let serialized = bincode::serialize(&value).unwrap();
                let deserialized = bincode::deserialize(&serialized[..]).unwrap();
                assert_eq!(value, deserialized);
            });
            proptest!(|(value: Bits<BITS, LIMBS>)| {
                let serialized = bincode::serialize(&value).unwrap();
                let deserialized = bincode::deserialize(&serialized[..]).unwrap();
                assert_eq!(value, deserialized);
            });
        });
    }

    #[test]
    fn test_serde_invalid_size_error() {
        // Test that if we add a character to a value that is already the max length for
        // the given number of bits, we get an error.
        const_for!(BITS in SIZES {
            const LIMBS: usize = nlimbs(BITS);
            let value = Uint::<BITS, LIMBS>::MAX;
            let mut serialized = serde_json::to_string(&value).unwrap();

            // ensure format of serialized value is correct ("0x...")
            assert_eq!(&serialized[..3], "\"0x");
            // last character should be a quote
            assert_eq!(&serialized[serialized.len() - 1..], "\"");

            // strip the last character, add a zero, and finish with a quote
            serialized.pop();
            serialized.push('0');
            serialized.push('"');
            let deserialized = serde_json::from_str::<Uint<BITS, LIMBS>>(&serialized);
            assert!(deserialized.is_err(), "{BITS} {serialized}");
        });
    }
}
