use crate::render::{self, group, hardline, nest, text, Doc};

/// a coq module
pub(crate) struct Module<'a> {
    pub name: &'a str,
}

/// a coq definition
pub(crate) struct Definition {}

impl<'a> Module<'a> {
    pub(crate) fn to_doc(&self, content: &Doc<'a>) -> Doc<'a> {
        render::module(self.name, content.clone())
    }
}

impl Definition {
    pub(crate) fn to_doc<'a>(&self, signature: &Doc<'a>, body: &Doc<'a>) -> Doc<'a> {
        group([
            nest([signature.clone(), body.clone()]),
            hardline(),
            text("}."),
        ])
    }
}
