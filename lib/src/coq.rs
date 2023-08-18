use crate::render::{self, group, hardline, nest, text, Doc};

/// a coq module
pub(crate) struct Module<'a> {
    pub name: &'a str,
    pub content: Vec<Doc<'a>>,
}

/// a coq definition
pub(crate) struct Definition<'a, U> {
    pub ty_params: Vec<(U, Option<Doc<'a>>)>,
    pub predicates: Vec<Doc<'a>>,
    pub bounds: Vec<Doc<'a>>,
    pub associated_types: Vec<(U, Vec<Doc<'a>>)>,
    pub items: Vec<Doc<'a>>,
}

impl<'a> Module<'a> {
    pub(crate) fn to_doc(&self) -> Doc<'a> {
        render::module(self.name, group(self.content.clone()))
    }
}

impl<'a, U> Definition<'a, U>
where
    U: Into<std::borrow::Cow<'a, str>> + std::marker::Copy,
{
    pub(crate) fn to_doc(&self) -> Doc<'a> {
        group([
            nest([
                render::new_trait_typeclass_header(
                    &self.ty_params,
                    &self.predicates,
                    &self.bounds,
                    &self.associated_types,
                ),
                render::new_typeclass_body(self.items.clone()),
            ]),
            hardline(),
            text("}."),
        ])
    }
}
