use p3_air::AirBuilder;
use p3_matrix::{dense::RowMajorMatrixView, stack::VerticalPair};

pub mod debug;
pub mod sub;
/// AIR builder that collects the constraints expressed via the [Air](p3_air::Air) trait into
/// a directed acyclic graph of symbolic expressions for serialization purposes.
pub mod symbolic;

pub type ViewPair<'a, T> = VerticalPair<RowMajorMatrixView<'a, T>, RowMajorMatrixView<'a, T>>;

/// AIR builder that supports main trace matrix which is partitioned
/// into sub-matrices which belong to different commitments.
pub trait PartitionedAirBuilder: AirBuilder {
    /// Cached main trace matrix.
    fn cached_mains(&self) -> &[Self::M];
    /// Common main trace matrix. Panic if there is no common main trace.
    fn common_main(&self) -> &Self::M;
}
