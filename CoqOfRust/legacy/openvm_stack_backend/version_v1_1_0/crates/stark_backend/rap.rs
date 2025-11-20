//! # RAP (Randomized Air with Preprocessing)
//! See <https://hackmd.io/@aztec-network/plonk-arithmetiization-air> for formal definition.

use std::{
    any::{type_name, Any},
    sync::Arc,
};

use p3_air::{BaseAir, PermutationAirBuilder};

use crate::{
    air_builders::{debug::DebugConstraintBuilder, symbolic::SymbolicRapBuilder},
    config::{StarkGenericConfig, Val},
};

/// An AIR with 0 or more public values.
/// This trait will be merged into Plonky3 in PR: <https://github.com/Plonky3/Plonky3/pull/470>
pub trait BaseAirWithPublicValues<F>: BaseAir<F> {
    fn num_public_values(&self) -> usize {
        0
    }
}

/// An AIR with 1 or more main trace partitions.
pub trait PartitionedBaseAir<F>: BaseAir<F> {
    /// By default, an AIR has no cached main trace.
    fn cached_main_widths(&self) -> Vec<usize> {
        vec![]
    }
    /// By default, an AIR has only one private main trace.
    fn common_main_width(&self) -> usize {
        self.width()
    }
}

/// An AIR that works with a particular `AirBuilder` which allows preprocessing
/// and injected randomness.
///
/// Currently this is not a fully general RAP. Only the following phases are allowed:
/// - Preprocessing
/// - Main trace generation and commitment
/// - Permutation trace generation and commitment
///
/// Randomness is drawn after the main trace commitment phase, and used in the permutation trace.
///
/// Does not inherit [Air](p3_air::Air) trait to allow overrides for technical reasons
/// around dynamic dispatch.
pub trait Rap<AB>: Sync
where
    AB: PermutationAirBuilder,
{
    fn eval(&self, builder: &mut AB);
}

/// Permutation AIR builder that exposes certain values to both prover and verifier
/// _after_ the permutation challenges are drawn. These can be thought of as
/// "public values" known after the challenges are drawn.
///
/// Exposed values are used internally by the prover and verifier
/// in cross-table permutation arguments.
pub trait PermutationAirBuilderWithExposedValues: PermutationAirBuilder {
    fn permutation_exposed_values(&self) -> &[Self::VarEF];
}

/// Shared reference to any Interactive Air.
/// This type is the main interface for keygen.
pub type AirRef<SC> = Arc<dyn AnyRap<SC>>;

/// RAP trait for all-purpose dynamic dispatch use.
/// This trait is auto-implemented if you implement `Air` and `BaseAirWithPublicValues` and `PartitionedBaseAir` traits.
pub trait AnyRap<SC: StarkGenericConfig>:
Rap<SymbolicRapBuilder<Val<SC>>> // for keygen to extract fixed data about the RAP
    + for<'a> Rap<DebugConstraintBuilder<'a, SC>> // for debugging
    + BaseAirWithPublicValues<Val<SC>>
    + PartitionedBaseAir<Val<SC>>
    + Send + Sync
{
    fn as_any(&self) -> &dyn Any;
    /// Name for display purposes
    fn name(&self) -> String;
}

impl<SC, T> AnyRap<SC> for T
where
    SC: StarkGenericConfig,
    T: Rap<SymbolicRapBuilder<Val<SC>>>
        + for<'a> Rap<DebugConstraintBuilder<'a, SC>>
        + BaseAirWithPublicValues<Val<SC>>
        + PartitionedBaseAir<Val<SC>>
        + Send
        + Sync
        + 'static,
{
    fn as_any(&self) -> &dyn Any {
        self
    }

    fn name(&self) -> String {
        get_air_name(self)
    }
}

/// Automatically derives the AIR name from the type name for pretty display purposes.
pub fn get_air_name<T>(_rap: &T) -> String {
    let full_name = type_name::<T>().to_string();
    // Split the input by the first '<' to separate the main type from its generics
    if let Some((main_part, generics_part)) = full_name.split_once('<') {
        // Extract the last segment of the main type
        let main_type = main_part.split("::").last().unwrap_or("");

        // Remove the trailing '>' from the generics part and split by ", " to handle multiple generics
        let generics: Vec<String> = generics_part
            .trim_end_matches('>')
            .split(", ")
            .map(|generic| {
                // For each generic type, extract the last segment after "::"
                generic.split("::").last().unwrap_or("").to_string()
            })
            .collect();

        // Join the simplified generics back together with ", " and format the result
        format!("{}<{}>", main_type, generics.join(", "))
    } else {
        // If there's no generic part, just return the last segment after "::"
        full_name.split("::").last().unwrap_or("").to_string()
    }
}
