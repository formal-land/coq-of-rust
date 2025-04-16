use core::borrow::Borrow;
use core::marker::PhantomData;

use serde::{Deserialize, Serialize};

/// A wrapper around an array digest, with a phantom type parameter to ensure that the digest is
/// associated with a particular field.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(bound(serialize = "[W; DIGEST_ELEMS]: Serialize"))]
#[serde(bound(deserialize = "[W; DIGEST_ELEMS]: Deserialize<'de>"))]
pub struct Hash<F, W, const DIGEST_ELEMS: usize> {
    value: [W; DIGEST_ELEMS],
    _marker: PhantomData<F>,
}

impl<F, W, const DIGEST_ELEMS: usize> From<[W; DIGEST_ELEMS]> for Hash<F, W, DIGEST_ELEMS> {
    fn from(value: [W; DIGEST_ELEMS]) -> Self {
        Self {
            value,
            _marker: PhantomData,
        }
    }
}

impl<F, W, const DIGEST_ELEMS: usize> From<Hash<F, W, DIGEST_ELEMS>> for [W; DIGEST_ELEMS] {
    fn from(value: Hash<F, W, DIGEST_ELEMS>) -> [W; DIGEST_ELEMS] {
        value.value
    }
}

impl<F, W: PartialEq, const DIGEST_ELEMS: usize> PartialEq<[W; DIGEST_ELEMS]>
    for Hash<F, W, DIGEST_ELEMS>
{
    fn eq(&self, other: &[W; DIGEST_ELEMS]) -> bool {
        self.value == *other
    }
}

impl<F, W, const DIGEST_ELEMS: usize> IntoIterator for Hash<F, W, DIGEST_ELEMS> {
    type Item = W;
    type IntoIter = core::array::IntoIter<W, DIGEST_ELEMS>;

    fn into_iter(self) -> Self::IntoIter {
        self.value.into_iter()
    }
}

impl<F, W, const DIGEST_ELEMS: usize> Borrow<[W; DIGEST_ELEMS]> for Hash<F, W, DIGEST_ELEMS> {
    fn borrow(&self) -> &[W; DIGEST_ELEMS] {
        &self.value
    }
}

impl<F, W, const DIGEST_ELEMS: usize> AsRef<[W; DIGEST_ELEMS]> for Hash<F, W, DIGEST_ELEMS> {
    fn as_ref(&self) -> &[W; DIGEST_ELEMS] {
        &self.value
    }
}
