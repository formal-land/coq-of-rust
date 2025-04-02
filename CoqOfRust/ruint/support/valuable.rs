//! Support for the [`valuable`](https://crates.io/crates/valuable) crate.

#![cfg(feature = "valuable")]
#![cfg_attr(docsrs, doc(cfg(feature = "valuable")))]

use crate::Uint;
use valuable::{Fields, NamedField, NamedValues, StructDef, Structable, Valuable, Value, Visit};

const FIELDS: &[NamedField<'static>] = &[NamedField::new("limbs")];

impl<const BITS: usize, const LIMBS: usize> Structable for Uint<BITS, LIMBS> {
    fn definition(&self) -> StructDef<'_> {
        StructDef::new_static("Uint", Fields::Named(FIELDS))
    }
}

impl<const BITS: usize, const LIMBS: usize> Valuable for Uint<BITS, LIMBS> {
    fn as_value(&self) -> Value<'_> {
        Value::Structable(self)
    }

    fn visit(&self, visitor: &mut dyn Visit) {
        visitor.visit_named_fields(&NamedValues::new(FIELDS, &[self.limbs.as_value()]));
    }
}
