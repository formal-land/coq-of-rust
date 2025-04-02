//! Support for the [`sqlx`](https://crates.io/crates/sqlx) crate.
//!
//! Currently only encodes to/from a big-endian byte array.

#![cfg(feature = "sqlx")]
#![cfg_attr(docsrs, doc(cfg(feature = "sqlx")))]

use crate::Uint;
use sqlx_core::{
    database::{Database, HasArguments, HasValueRef},
    decode::Decode,
    encode::{Encode, IsNull},
    error::BoxDynError,
    types::Type,
};
use thiserror::Error;

#[derive(Error, Debug)]
pub enum DecodeError {
    #[error("Value too large for target type")]
    Overflow,
}

impl<const BITS: usize, const LIMBS: usize, DB: Database> Type<DB> for Uint<BITS, LIMBS>
where
    Vec<u8>: Type<DB>,
{
    fn type_info() -> DB::TypeInfo {
        <Vec<u8> as Type<DB>>::type_info()
    }

    fn compatible(ty: &DB::TypeInfo) -> bool {
        <Vec<u8> as Type<DB>>::compatible(ty)
    }
}

impl<'a, const BITS: usize, const LIMBS: usize, DB: Database> Encode<'a, DB> for Uint<BITS, LIMBS>
where
    Vec<u8>: Encode<'a, DB>,
{
    fn encode_by_ref(&self, buf: &mut <DB as HasArguments<'a>>::ArgumentBuffer) -> IsNull {
        self.to_be_bytes_vec().encode_by_ref(buf)
    }
}

impl<'a, const BITS: usize, const LIMBS: usize, DB: Database> Decode<'a, DB> for Uint<BITS, LIMBS>
where
    Vec<u8>: Decode<'a, DB>,
{
    fn decode(value: <DB as HasValueRef<'a>>::ValueRef) -> Result<Self, BoxDynError> {
        let bytes = Vec::<u8>::decode(value)?;
        Self::try_from_be_slice(bytes.as_slice()).ok_or_else(|| DecodeError::Overflow.into())
    }
}
