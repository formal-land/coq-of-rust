use crate::ty::*;

use rustc_middle::ty::TyCtxt;
use std::collections::HashMap;

/// The environment used for the translation steps, holding various state
/// information
pub(crate) struct Env<'a> {
    /// We use a counter for the disambiguation of several impls for the same
    /// type
    pub(crate) impl_counter: HashMap<CoqType, u64>,
    pub(crate) tcx: TyCtxt<'a>,
    pub(crate) axiomatize: bool,
    pub(crate) context: String, // full path for the current scope
}

impl<'a> Env<'a> {
    pub(crate) fn push_context(&mut self, context: &str) {
        self.context = format!("{}::{}", self.context, context);
    }

    pub(crate) fn pop_context(&mut self) {
        let segments: Vec<String> = self.context.split("::").map(String::from).collect();
        let segments: &[String] = &segments[0..segments.len() - 1];
        let context: String = segments.join("::");
        self.context = context
    }
}
