use super::{JumpTable, LegacyAnalyzedBytecode};
use bitvec::{bitvec, order::Lsb0, vec::BitVec};
use core::ops::Deref;
use primitives::Bytes;
use std::{sync::Arc, vec::Vec};

#[derive(Clone, Debug, PartialEq, Eq, Hash, Ord, PartialOrd)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct LegacyRawBytecode(pub Bytes);

impl LegacyRawBytecode {
    pub fn analysis(&self) -> JumpTable {
        analyze_legacy(&self.0)
    }

    pub fn into_analyzed(self) -> LegacyAnalyzedBytecode {
        let jump_table = self.analysis();
        let len = self.0.len();
        let mut padded_bytecode = Vec::with_capacity(len + 33);
        padded_bytecode.extend_from_slice(&self.0);
        padded_bytecode.resize(len + 33, 0);
        LegacyAnalyzedBytecode::new(padded_bytecode.into(), len, jump_table)
    }
}

impl From<Bytes> for LegacyRawBytecode {
    fn from(bytes: Bytes) -> Self {
        Self(bytes)
    }
}

impl<const N: usize> From<[u8; N]> for LegacyRawBytecode {
    fn from(bytes: [u8; N]) -> Self {
        Self(bytes.into())
    }
}

impl Deref for LegacyRawBytecode {
    type Target = Bytes;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// Analyze the bytecode to find the jumpdests
pub fn analyze_legacy(bytetecode: &[u8]) -> JumpTable {
    let jumps: BitVec<u8> = bitvec![u8, Lsb0; 0; bytetecode.len()];

    JumpTable(Arc::new(jumps))
}
