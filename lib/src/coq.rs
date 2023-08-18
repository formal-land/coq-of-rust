use crate::render;

/*
/// a coq item
pub(crate) enum Item {
    Module(Module),
}
*/

/// a coq module
pub(crate) struct Module<'a> {
    pub(crate) name: &'a str,
}

impl<'a> Module<'a> {
    pub(crate) fn to_doc(&self, content: &render::Doc<'a>) -> render::Doc<'a> {
        render::module(self.name, content.clone())
    }
}
