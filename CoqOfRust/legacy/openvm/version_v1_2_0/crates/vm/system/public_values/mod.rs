use crate::{
    arch::{VmAirWrapper, VmChipWrapper},
    system::{
        native_adapter::{NativeAdapterAir, NativeAdapterChip},
        public_values::core::{PublicValuesCoreAir, PublicValuesCoreChip},
    },
};

mod columns;
/// Chip to publish custom public values from VM programs.
pub mod core;

#[cfg(test)]
mod tests;

pub type PublicValuesAir = VmAirWrapper<NativeAdapterAir<2, 0>, PublicValuesCoreAir>;
pub type PublicValuesChip<F> =
    VmChipWrapper<F, NativeAdapterChip<F, 2, 0>, PublicValuesCoreChip<F>>;
