use std::iter;

use openvm_stark_backend::{
    interaction::{BusIndex, InteractionBuilder, LookupBus},
    p3_field::FieldAlgebra,
};

#[derive(Debug, Clone, Copy)]
pub struct ProgramBus {
    pub inner: LookupBus,
}

impl ProgramBus {
    pub const fn new(index: BusIndex) -> Self {
        Self {
            inner: LookupBus::new(index),
        }
    }

    #[inline(always)]
    pub fn index(&self) -> BusIndex {
        self.inner.index
    }
}

impl ProgramBus {
    /// Caller must constrain that `enabled` is boolean.
    pub fn lookup_instruction<AB: InteractionBuilder, E: Into<AB::Expr>>(
        &self,
        builder: &mut AB,
        pc: impl Into<AB::Expr>,
        opcode: impl Into<AB::Expr>,
        operands: impl IntoIterator<Item = E>,
        enabled: impl Into<AB::Expr>,
    ) {
        self.inner.lookup_key(
            builder,
            [pc.into(), opcode.into()].into_iter().chain(
                operands
                    .into_iter()
                    .map(Into::into)
                    .chain(iter::repeat(AB::Expr::ZERO))
                    .take(7),
            ),
            enabled,
        );
    }
}
