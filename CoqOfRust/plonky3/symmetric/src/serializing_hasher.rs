use core::iter;

use p3_field::{PackedValue, PrimeField32, PrimeField64};

use crate::CryptographicHasher;

/// Serializes 32-bit field elements to bytes (i.e. the little-endian encoding of their canonical
/// values), then hashes those bytes using some inner hasher, and outputs a `[u8; 32]`.
#[derive(Copy, Clone, Debug)]
pub struct SerializingHasher32<Inner> {
    inner: Inner,
}

/// Serializes 32-bit field elements to u64s (packing two canonical values together), then hashes
/// those u64s using some inner hasher, and outputs a `[u64; 4]`.
#[derive(Copy, Clone, Debug)]
pub struct SerializingHasher32To64<Inner> {
    inner: Inner,
}

/// Serializes 64-bit field elements to bytes (i.e. the little-endian encoding of their canonical
/// values), then hashes those bytes using some inner hasher, and outputs a `[u8; 32]`.
#[derive(Copy, Clone, Debug)]
pub struct SerializingHasher64<Inner> {
    inner: Inner,
}

impl<Inner> SerializingHasher32<Inner> {
    pub const fn new(inner: Inner) -> Self {
        Self { inner }
    }
}

impl<Inner> SerializingHasher32To64<Inner> {
    pub const fn new(inner: Inner) -> Self {
        Self { inner }
    }
}

impl<Inner> SerializingHasher64<Inner> {
    pub const fn new(inner: Inner) -> Self {
        Self { inner }
    }
}

impl<F, Inner> CryptographicHasher<F, [u8; 32]> for SerializingHasher32<Inner>
where
    F: PrimeField32,
    Inner: CryptographicHasher<u8, [u8; 32]>,
{
    fn hash_iter<I>(&self, input: I) -> [u8; 32]
    where
        I: IntoIterator<Item = F>,
    {
        self.inner.hash_iter(
            input
                .into_iter()
                .flat_map(|x| x.to_unique_u32().to_le_bytes()),
        )
    }
}

impl<P, PW, Inner> CryptographicHasher<P, [PW; 8]> for SerializingHasher32<Inner>
where
    P: PackedValue,
    P::Value: PrimeField32,
    PW: PackedValue<Value = u32>,
    Inner: CryptographicHasher<PW, [PW; 8]>,
{
    fn hash_iter<I>(&self, input: I) -> [PW; 8]
    where
        I: IntoIterator<Item = P>,
    {
        self.inner.hash_iter(
            input
                .into_iter()
                .map(|x| PW::from_fn(|i| x.as_slice()[i].to_unique_u32())),
        )
    }
}

impl<P, PW, Inner> CryptographicHasher<P, [PW; 4]> for SerializingHasher32To64<Inner>
where
    P: PackedValue,
    P::Value: PrimeField32,
    PW: PackedValue<Value = u64>,
    Inner: CryptographicHasher<PW, [PW; 4]>,
{
    fn hash_iter<I>(&self, input: I) -> [PW; 4]
    where
        I: IntoIterator<Item = P>,
    {
        assert_eq!(P::WIDTH, PW::WIDTH);
        let mut input = input.into_iter();
        self.inner.hash_iter(iter::from_fn(
            #[inline]
            || {
                let a = input.next();
                let b = input.next();
                if let (Some(a), Some(b)) = (a, b) {
                    let ab = PW::from_fn(|i| {
                        let a_i = a.as_slice()[i].to_unique_u64();
                        let b_i = b.as_slice()[i].to_unique_u64();
                        a_i | (b_i << 32)
                    });
                    Some(ab)
                } else {
                    a.map(|a| PW::from_fn(|i| a.as_slice()[i].to_unique_u64()))
                }
            },
        ))
    }
}

impl<F, Inner> CryptographicHasher<F, [u8; 32]> for SerializingHasher64<Inner>
where
    F: PrimeField64,
    Inner: CryptographicHasher<u8, [u8; 32]>,
{
    fn hash_iter<I>(&self, input: I) -> [u8; 32]
    where
        I: IntoIterator<Item = F>,
    {
        self.inner.hash_iter(
            input
                .into_iter()
                .flat_map(|x| x.to_unique_u64().to_le_bytes()),
        )
    }
}

impl<P, PW, Inner> CryptographicHasher<P, [PW; 4]> for SerializingHasher64<Inner>
where
    P: PackedValue,
    P::Value: PrimeField64,
    PW: PackedValue<Value = u64>,
    Inner: CryptographicHasher<PW, [PW; 4]>,
{
    fn hash_iter<I>(&self, input: I) -> [PW; 4]
    where
        I: IntoIterator<Item = P>,
    {
        self.inner.hash_iter(
            input
                .into_iter()
                .map(|x| PW::from_fn(|i| x.as_slice()[i].to_unique_u64())),
        )
    }
}
