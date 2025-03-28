// OPT: Use u64::from_{be/le}_bytes() to work 8 bytes at a time.
// FEATURE: (BLOCKED) Make `const fn`s when `const_for` is stable.

use crate::Uint;
use core::slice;

#[cfg(feature = "alloc")]
#[allow(unused_imports)]
use alloc::{borrow::Cow, vec::Vec};

// OPT: *_to_smallvec to avoid allocation.
impl<const BITS: usize, const LIMBS: usize> Uint<BITS, LIMBS> {
    /// The size of this integer type in bytes. Note that some bits may be
    /// forced zero if BITS is not cleanly divisible by eight.
    pub const BYTES: usize = (BITS + 7) / 8;

    /// Access the underlying store as a little-endian slice of bytes.
    ///
    /// Only available on little-endian targets.
    ///
    /// If `BITS` does not evenly divide 8, it is padded with zero bits in the
    /// most significant position.
    #[cfg(target_endian = "little")]
    #[must_use]
    #[inline(always)]
    pub const fn as_le_slice(&self) -> &[u8] {
        unsafe { slice::from_raw_parts(self.limbs.as_ptr().cast(), Self::BYTES) }
    }

    /// Access the underlying store as a mutable little-endian slice of bytes.
    ///
    /// Only available on litte-endian targets.
    ///
    /// # Safety
    ///
    /// If `BITS` does not evenly divide 8, it is padded with zero bits in the
    /// most significant position. Setting those bits puts the [`Uint`] in an
    /// invalid state.
    #[cfg(target_endian = "little")]
    #[must_use]
    #[inline(always)]
    pub unsafe fn as_le_slice_mut(&mut self) -> &mut [u8] {
        unsafe { slice::from_raw_parts_mut(self.limbs.as_mut_ptr().cast(), Self::BYTES) }
    }

    /// Access the underlying store as a little-endian bytes.
    ///
    /// Uses an optimized implementation on little-endian targets.
    #[cfg(feature = "alloc")]
    #[must_use]
    #[inline]
    #[allow(clippy::missing_const_for_fn)]
    pub fn as_le_bytes(&self) -> Cow<'_, [u8]> {
        // On little endian platforms this is a no-op.
        #[cfg(target_endian = "little")]
        return Cow::Borrowed(self.as_le_slice());

        // In others, reverse each limb and return a copy.
        #[cfg(target_endian = "big")]
        return Cow::Owned({
            let mut cpy = *self;
            for limb in &mut cpy.limbs {
                *limb = limb.reverse_bits();
            }
            unsafe { slice::from_raw_parts(cpy.limbs.as_ptr().cast(), Self::BYTES).to_vec() }
        });
    }

    /// Access the underlying store as a little-endian bytes with trailing zeros
    /// removed.
    ///
    /// Uses an optimized implementation on little-endian targets.
    #[cfg(feature = "alloc")]
    #[must_use]
    #[inline]
    pub fn as_le_bytes_trimmed(&self) -> Cow<'_, [u8]> {
        match self.as_le_bytes() {
            Cow::Borrowed(slice) => Cow::Borrowed(crate::utils::trim_end_slice(slice, &0)),
            Cow::Owned(mut vec) => {
                crate::utils::trim_end_vec(&mut vec, &0);
                Cow::Owned(vec)
            }
        }
    }

    /// Converts the [`Uint`] to a little-endian byte array of size exactly
    /// [`Self::BYTES`].
    ///
    /// # Panics
    ///
    /// Panics if the generic parameter `BYTES` is not exactly [`Self::BYTES`].
    /// Ideally this would be a compile time error, but this is blocked by
    /// Rust issue [#60551].
    ///
    /// [#60551]: https://github.com/rust-lang/rust/issues/60551
    #[inline]
    #[must_use]
    pub const fn to_le_bytes<const BYTES: usize>(&self) -> [u8; BYTES] {
        // TODO: Use a `const {}` block for this assertion
        assert!(BYTES == Self::BYTES, "BYTES must be equal to Self::BYTES");

        // Specialized impl
        #[cfg(target_endian = "little")]
        // SAFETY: BYTES == Self::BYTES == self.as_le_slice().len()
        return unsafe { *self.as_le_slice().as_ptr().cast() };

        // Generic impl
        #[cfg(target_endian = "big")]
        {
            let mut limbs = self.limbs;
            let mut i = 0;
            while i < LIMBS {
                limbs[i] = limbs[i].to_le();
                i += 1;
            }
            // SAFETY: BYTES <= LIMBS * 8
            unsafe { *limbs.as_ptr().cast() }
        }
    }

    /// Converts the [`Uint`] to a little-endian byte vector of size exactly
    /// [`Self::BYTES`].
    ///
    /// This method is useful when [`Self::to_le_bytes`] can not be used because
    /// byte size is not known compile time.
    #[cfg(feature = "alloc")]
    #[must_use]
    #[inline]
    pub fn to_le_bytes_vec(&self) -> Vec<u8> {
        self.as_le_bytes().into_owned()
    }

    /// Converts the [`Uint`] to a little-endian byte vector with trailing zeros
    /// bytes removed.
    #[cfg(feature = "alloc")]
    #[must_use]
    #[inline]
    pub fn to_le_bytes_trimmed_vec(&self) -> Vec<u8> {
        self.as_le_bytes_trimmed().into_owned()
    }

    /// Converts the [`Uint`] to a big-endian byte array of size exactly
    /// [`Self::BYTES`].
    ///
    /// # Panics
    ///
    /// Panics if the generic parameter `BYTES` is not exactly [`Self::BYTES`].
    /// Ideally this would be a compile time error, but this is blocked by
    /// Rust issue [#60551].
    ///
    /// [#60551]: https://github.com/rust-lang/rust/issues/60551
    #[must_use]
    #[inline]
    pub const fn to_be_bytes<const BYTES: usize>(&self) -> [u8; BYTES] {
        let mut bytes = self.to_le_bytes::<BYTES>();

        // bytes.reverse()
        let len = bytes.len();
        let half_len = len / 2;
        let mut i = 0;
        while i < half_len {
            let tmp = bytes[i];
            bytes[i] = bytes[len - 1 - i];
            bytes[len - 1 - i] = tmp;
            i += 1;
        }

        bytes
    }

    /// Converts the [`Uint`] to a big-endian byte vector of size exactly
    /// [`Self::BYTES`].
    ///
    /// This method is useful when [`Self::to_be_bytes`] can not be used because
    /// byte size is not known compile time.
    #[cfg(feature = "alloc")]
    #[must_use]
    #[inline]
    pub fn to_be_bytes_vec(&self) -> Vec<u8> {
        let mut bytes = self.to_le_bytes_vec();
        bytes.reverse();
        bytes
    }

    /// Converts the [`Uint`] to a big-endian byte vector with leading zeros
    /// bytes removed.
    #[cfg(feature = "alloc")]
    #[must_use]
    #[inline]
    pub fn to_be_bytes_trimmed_vec(&self) -> Vec<u8> {
        let mut bytes = self.to_le_bytes_trimmed_vec();
        bytes.reverse();
        bytes
    }

    /// Converts a big-endian byte array of size exactly
    /// [`Self::BYTES`] to [`Uint`].
    ///
    /// # Panics
    ///
    /// Panics if the generic parameter `BYTES` is not exactly [`Self::BYTES`].
    /// Ideally this would be a compile time error, but this is blocked by
    /// Rust issue [#60551].
    ///
    /// [#60551]: https://github.com/rust-lang/rust/issues/60551
    ///
    /// Panics if the value is too large for the bit-size of the Uint.
    #[must_use]
    #[track_caller]
    #[inline]
    pub const fn from_be_bytes<const BYTES: usize>(bytes: [u8; BYTES]) -> Self {
        // TODO: Use a `const {}` block for this assertion
        assert!(BYTES == Self::BYTES, "BYTES must be equal to Self::BYTES");
        Self::from_be_slice(&bytes)
    }

    /// Creates a new integer from a big endian slice of bytes.
    ///
    /// The slice is interpreted as a big endian number. Leading zeros
    /// are ignored. The slice can be any length.
    ///
    /// # Panics
    ///
    /// Panics if the value is larger than fits the [`Uint`].
    #[must_use]
    #[track_caller]
    #[inline]
    pub const fn from_be_slice(bytes: &[u8]) -> Self {
        match Self::try_from_be_slice(bytes) {
            Some(value) => value,
            None => panic!("Value too large for Uint"),
        }
    }

    /// Creates a new integer from a big endian slice of bytes.
    ///
    /// The slice is interpreted as a big endian number. Leading zeros
    /// are ignored. The slice can be any length.
    ///
    /// Returns [`None`] if the value is larger than fits the [`Uint`].
    #[must_use]
    #[inline]
    pub const fn try_from_be_slice(bytes: &[u8]) -> Option<Self> {
        if bytes.len() > Self::BYTES {
            return None;
        }

        if Self::BYTES % 8 == 0 && bytes.len() == Self::BYTES {
            // Optimized implementation for full-limb types.
            let mut limbs = [0; LIMBS];
            let end = bytes.as_ptr_range().end;
            let mut i = 0;
            while i < LIMBS {
                limbs[i] = u64::from_be_bytes(unsafe { *end.sub((i + 1) * 8).cast() });
                i += 1;
            }
            return Some(Self::from_limbs(limbs));
        }

        let mut limbs = [0; LIMBS];
        let mut i = 0;
        let mut c = bytes.len();
        while i < bytes.len() {
            c -= 1;
            limbs[i / 8] += (bytes[c] as u64) << ((i % 8) * 8);
            i += 1;
        }
        if Self::LIMBS > 0 && limbs[Self::LIMBS - 1] > Self::MASK {
            return None;
        }
        Some(Self::from_limbs(limbs))
    }

    /// Converts a little-endian byte array of size exactly
    /// [`Self::BYTES`] to [`Uint`].
    ///
    /// # Panics
    ///
    /// Panics if the generic parameter `BYTES` is not exactly [`Self::BYTES`].
    /// Ideally this would be a compile time error, but this is blocked by
    /// Rust issue [#60551].
    ///
    /// [#60551]: https://github.com/rust-lang/rust/issues/60551
    ///
    /// Panics if the value is too large for the bit-size of the Uint.
    #[must_use]
    #[track_caller]
    #[inline]
    pub const fn from_le_bytes<const BYTES: usize>(bytes: [u8; BYTES]) -> Self {
        // TODO: Use a `const {}` block for this assertion
        assert!(BYTES == Self::BYTES, "BYTES must be equal to Self::BYTES");
        Self::from_le_slice(&bytes)
    }

    /// Creates a new integer from a little endian slice of bytes.
    ///
    /// The slice is interpreted as a little endian number. Leading zeros
    /// are ignored. The slice can be any length.
    ///
    /// # Panics
    ///
    /// Panics if the value is larger than fits the [`Uint`].
    #[must_use]
    #[track_caller]
    #[inline]
    pub const fn from_le_slice(bytes: &[u8]) -> Self {
        match Self::try_from_le_slice(bytes) {
            Some(value) => value,
            None => panic!("Value too large for Uint"),
        }
    }

    /// Creates a new integer from a little endian slice of bytes.
    ///
    /// The slice is interpreted as a little endian number. Leading zeros
    /// are ignored. The slice can be any length.
    ///
    /// Returns [`None`] if the value is larger than fits the [`Uint`].
    #[must_use]
    #[inline]
    pub const fn try_from_le_slice(bytes: &[u8]) -> Option<Self> {
        if bytes.len() / 8 > Self::LIMBS {
            return None;
        }

        if Self::BYTES % 8 == 0 && bytes.len() == Self::BYTES {
            // Optimized implementation for full-limb types.
            let mut limbs = [0; LIMBS];
            let mut i = 0;
            while i < LIMBS {
                limbs[i] = u64::from_le_bytes(unsafe { *bytes.as_ptr().add(i * 8).cast() });
                i += 1;
            }
            return Some(Self::from_limbs(limbs));
        }

        let mut limbs = [0; LIMBS];
        let mut i = 0;
        while i < bytes.len() {
            limbs[i / 8] += (bytes[i] as u64) << ((i % 8) * 8);
            i += 1;
        }
        if Self::LIMBS > 0 && limbs[Self::LIMBS - 1] > Self::MASK {
            return None;
        }
        Some(Self::from_limbs(limbs))
    }
}

/// Number of bytes required to represent the given number of bits.
///
/// This needs to be public because it is used in the `Uint` type,
/// specifically in the [`to_be_bytes()`][Uint::to_be_bytes] and related
/// functions.
#[inline]
#[must_use]
pub const fn nbytes(bits: usize) -> usize {
    (bits + 7) / 8
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{const_for, nlimbs};
    use proptest::proptest;

    const N: Uint<128, 2> =
        Uint::from_limbs([0x7890_1234_5678_9012_u64, 0x1234_5678_9012_3456_u64]);
    const BE: [u8; 16] = [
        0x12, 0x34, 0x56, 0x78, 0x90, 0x12, 0x34, 0x56, 0x78, 0x90, 0x12, 0x34, 0x56, 0x78, 0x90,
        0x12,
    ];
    const LE: [u8; 16] = [
        0x12, 0x90, 0x78, 0x56, 0x34, 0x12, 0x90, 0x78, 0x56, 0x34, 0x12, 0x90, 0x78, 0x56, 0x34,
        0x12,
    ];

    const K: Uint<72, 2> = Uint::from_limbs([0x3456_7890_1234_5678_u64, 0x12_u64]);
    const KBE: [u8; 9] = [0x12, 0x34, 0x56, 0x78, 0x90, 0x12, 0x34, 0x56, 0x78];
    const KLE: [u8; 9] = [0x78, 0x56, 0x34, 0x12, 0x90, 0x78, 0x56, 0x34, 0x12];

    #[test]
    const fn const_from_to_bytes() {
        const NL: [u64; 2] = N.limbs;
        assert!(matches!(Uint::<128, 2>::from_be_bytes(BE).limbs, NL));
        assert!(matches!(Uint::<128, 2>::from_le_bytes(LE).limbs, NL));
        assert!(matches!(N.to_be_bytes::<{ BE.len() }>(), BE));
        assert!(matches!(N.to_le_bytes::<{ LE.len() }>(), LE));

        const KL: [u64; 2] = K.limbs;
        assert!(matches!(Uint::<72, 2>::from_be_bytes(KBE).limbs, KL));
        assert!(matches!(Uint::<72, 2>::from_le_bytes(KLE).limbs, KL));
        assert!(matches!(K.to_be_bytes::<{ KBE.len() }>(), KBE));
        assert!(matches!(K.to_le_bytes::<{ KLE.len() }>(), KLE));

        assert!(matches!(Uint::<0, 0>::ZERO.to_be_bytes::<0>(), []));
        assert!(matches!(Uint::<1, 1>::ZERO.to_be_bytes::<1>(), [0]));
        assert!(matches!(
            Uint::<1, 1>::from_limbs([1]).to_be_bytes::<1>(),
            [1]
        ));
        assert!(matches!(
            Uint::<16, 1>::from_limbs([0x1234]).to_be_bytes::<2>(),
            [0x12, 0x34]
        ));

        assert!(matches!(Uint::<0, 0>::ZERO.to_be_bytes::<0>(), []));
        assert!(matches!(Uint::<0, 0>::ZERO.to_le_bytes::<0>(), []));
        assert!(matches!(Uint::<1, 1>::ZERO.to_be_bytes::<1>(), [0]));
        assert!(matches!(Uint::<1, 1>::ZERO.to_le_bytes::<1>(), [0]));
        assert!(matches!(
            Uint::<1, 1>::from_limbs([1]).to_be_bytes::<1>(),
            [1]
        ));
        assert!(matches!(
            Uint::<1, 1>::from_limbs([1]).to_le_bytes::<1>(),
            [1]
        ));
        assert!(matches!(
            Uint::<16, 1>::from_limbs([0x1234]).to_be_bytes::<2>(),
            [0x12, 0x34]
        ));
        assert!(matches!(
            Uint::<16, 1>::from_limbs([0x1234]).to_le_bytes::<2>(),
            [0x34, 0x12]
        ));

        assert!(matches!(
            Uint::<63, 1>::from_limbs([0x010203]).to_be_bytes::<8>(),
            [0, 0, 0, 0, 0, 1, 2, 3]
        ));
        assert!(matches!(
            Uint::<63, 1>::from_limbs([0x010203]).to_le_bytes::<8>(),
            [3, 2, 1, 0, 0, 0, 0, 0]
        ));
    }

    #[test]
    fn test_from_bytes() {
        assert_eq!(Uint::<0, 0>::from_be_bytes([]), Uint::ZERO);
        assert_eq!(Uint::<0, 0>::from_le_bytes([]), Uint::ZERO);
        assert_eq!(
            Uint::<12, 1>::from_be_bytes([0x01, 0x23]),
            Uint::from(0x0123)
        );
        assert_eq!(
            Uint::<12, 1>::from_le_bytes([0x23, 0x01]),
            Uint::from(0x0123)
        );
        assert_eq!(
            Uint::<16, 1>::from_be_bytes([0x12, 0x34]),
            Uint::from(0x1234)
        );
        assert_eq!(
            Uint::<16, 1>::from_le_bytes([0x34, 0x12]),
            Uint::from(0x1234)
        );
        assert_eq!(Uint::from_be_bytes(BE), N);
        assert_eq!(Uint::from_le_bytes(LE), N);
        assert_eq!(Uint::from_be_bytes(KBE), K);
        assert_eq!(Uint::from_le_bytes(KLE), K);
    }

    #[test]
    fn test_to_bytes() {
        assert_eq!(Uint::<0, 0>::ZERO.to_le_bytes(), [0_u8; 0]);
        assert_eq!(Uint::<0, 0>::ZERO.to_be_bytes(), [0_u8; 0]);
        assert_eq!(Uint::<12, 1>::from(0x0123_u64).to_le_bytes(), [0x23, 0x01]);
        assert_eq!(Uint::<12, 1>::from(0x0123_u64).to_be_bytes(), [0x01, 0x23]);
        assert_eq!(Uint::<16, 1>::from(0x1234_u64).to_le_bytes(), [0x34, 0x12]);
        assert_eq!(Uint::<16, 1>::from(0x1234_u64).to_be_bytes(), [0x12, 0x34]);
        assert_eq!(K.to_be_bytes(), KBE);
        assert_eq!(K.to_le_bytes(), KLE);
    }

    #[test]
    fn test_bytes_roundtrip() {
        const_for!(BITS in SIZES {
            const LIMBS: usize = nlimbs(BITS);
            const BYTES: usize = nbytes(BITS);
            proptest!(|(value: Uint<BITS, LIMBS>)| {
                assert_eq!(value, Uint::try_from_le_slice(&value.as_le_bytes()).unwrap());
                assert_eq!(value, Uint::try_from_le_slice(&value.as_le_bytes_trimmed()).unwrap());
                assert_eq!(value, Uint::try_from_be_slice(&value.to_be_bytes_trimmed_vec()).unwrap());
                assert_eq!(value, Uint::try_from_le_slice(&value.to_le_bytes_trimmed_vec()).unwrap());
                assert_eq!(value, Uint::from_be_bytes(value.to_be_bytes::<BYTES>()));
                assert_eq!(value, Uint::from_le_bytes(value.to_le_bytes::<BYTES>()));
            });
        });
    }
}
