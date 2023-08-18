use crate::render::{self, concat, group, hardline, nest, text, Doc};

/// a coq module
pub(crate) struct Module<'a> {
    pub name: &'a str,
    pub content: Vec<Doc<'a>>,
}

/// a coq definition
pub(crate) struct Definition<'a, U> {
    ty_params: Vec<(U, Option<Doc<'a>>)>,
    predicates: Vec<Doc<'a>>,
    bounds: Vec<Doc<'a>>,
    associated_types: Vec<(U, Vec<Doc<'a>>)>,
    items: Vec<Doc<'a>>,
}

/// a global instance of a coq typeclass
pub(crate) struct Instance<'a> {
    name: &'a str,
    trait_parameters: Vec<&'a str>,
    kind: Doc<'a>,
    field: Doc<'a>,
    value: Doc<'a>,
}

impl<'a> Module<'a> {
    pub(crate) fn new(name: &'a str, content: Vec<Doc<'a>>) -> Self {
        Module { name, content }
    }

    pub(crate) fn to_doc(&self) -> Doc<'a> {
        render::module(self.name, group(self.content.clone()))
    }
}

impl<'a, U> Definition<'a, U>
where
    U: Into<std::borrow::Cow<'a, str>> + std::marker::Copy,
{
    /// produces a new coq instance
    pub(crate) fn new(
        ty_params: Vec<(U, Option<Doc<'a>>)>,
        predicates: Vec<Doc<'a>>,
        bounds: Vec<Doc<'a>>,
        associated_types: Vec<(U, Vec<Doc<'a>>)>,
        items: Vec<Doc<'a>>,
    ) -> Self {
        Definition {
            ty_params,
            predicates,
            bounds,
            associated_types,
            items,
        }
    }

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

impl<'a> Instance<'a> {
    /// produces a new coq instance
    pub(crate) fn new(
        name: &'a str,
        trait_parameters: &[&'a str],
        kind: Doc<'a>,
        field: Doc<'a>,
        value: Doc<'a>,
    ) -> Self {
        Instance {
            name,
            trait_parameters: trait_parameters.to_vec(),
            kind,
            field,
            value,
        }
    }

    pub(crate) fn to_doc(&self) -> Doc<'a> {
        concat([
            render::new_instance_header(self.name, &self.trait_parameters, self.kind.to_owned()),
            nest([
                hardline(),
                render::new_instance_body(self.field.to_owned(), self.value.to_owned()),
            ]),
            hardline(),
            text("}."),
        ])
    }
}
