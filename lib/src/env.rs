use crate::configuration::*;
use crate::path::*;
use crate::ty::*;
use rustc_middle::ty::TyCtxt;
use std::collections::HashMap;
use std::rc::Rc;

/// The environment used for the translation steps, holding various state
/// information
pub(crate) struct Env<'a> {
    /// We use a counter for the disambiguation of several impls for the same
    /// type
    pub(crate) impl_counter: HashMap<Rc<CoqType>, u64>,
    pub(crate) tcx: TyCtxt<'a>,
    pub(crate) axiomatize: bool,
    pub(crate) axiomatize_public: bool,
    /// path of the file being compiled
    pub(crate) file: String,
    /// accumulate the reordering for printing,
    pub(crate) reorder_map: HashMap<String, Vec<String>>,
    /// the configuration read or default if no config file is found
    pub(crate) configuration: Configuration,
    /// the current trait that we are implementing, with its Self type
    pub(crate) current_trait_impl: Option<(Path, Rc<CoqType>)>,
}
