use crate::path::*;
use crate::ty::*;
use std::collections::HashMap;

/// The environment used for the translation steps, holding various state
/// information
pub(crate) struct Env {
    /// We use a counter for the disambiguation of several impls for the same
    /// type
    pub(crate) impl_counter: HashMap<CoqType, u64>,
    /// The types that are currently in scope after a `use` statement
    pub(crate) use_types: HashMap<String, Path>,
}
