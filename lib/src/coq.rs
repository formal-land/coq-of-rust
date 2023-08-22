use crate::path::Path;
use crate::render::{self, concat, group, hardline, intersperse, line, nest, paren, text, Doc};

pub(crate) struct Comment {
    text: String,
}

/// a coq module
pub(crate) struct Module<'a> {
    name: &'a str,
    content: Vec<Doc<'a>>,
}

/// a coq `Context` item
pub(crate) struct Context {
    idents: Vec<String>,
    ty: Expression,
}

/// a coq definition
pub(crate) struct Class<'a, U> {
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
    class: Expression,
    field: Doc<'a>,
    value: Doc<'a>,
}

#[derive(Clone)]
/// a coq expression
pub(crate) enum Expression {
    Application {
        func: Box<Expression>,
        arg: Box<Expression>,
    },
    Variable(Path),
}

impl Comment {
    /// produces a new coq comment
    pub(crate) fn new(text: &str) -> Self {
        Comment {
            text: text.to_owned(),
        }
    }

    pub(crate) fn to_doc<'a>(&self) -> Doc<'a> {
        concat([text("(* "), text(self.text.to_string()), text(" *)")])
    }
}

impl<'a> Module<'a> {
    /// produces a new coq module
    pub(crate) fn new(name: &'a str, content: Vec<Doc<'a>>) -> Self {
        Module { name, content }
    }

    pub(crate) fn to_doc(&self) -> Doc<'a> {
        render::enclose("Module", self.name, &vec![], group(self.content.clone()))
    }
}

impl Context {
    pub(crate) fn new(idents: &[String], ty: &Expression) -> Self {
        Context {
            idents: idents.to_owned(),
            ty: ty.to_owned(),
        }
    }

    pub(crate) fn to_doc<'a>(&self) -> Doc<'a> {
        nest([
            text("Context"),
            line(),
            if self.idents.is_empty() {
                // I assume that an empty identifier list means a typeclass definition
                group([text("`{"), self.ty.to_doc(false), text("}")])
            } else {
                group([
                    text("{"),
                    intersperse(self.idents.to_owned(), [line()]),
                    line(),
                    text(":"),
                    line(),
                    self.ty.to_doc(false),
                    text("}"),
                ])
            },
            text("."),
        ])
    }
}

impl<'a, U> Class<'a, U>
where
    U: Into<std::borrow::Cow<'a, str>> + std::marker::Copy,
{
    /// produces a new coq definition
    pub(crate) fn new(
        ty_params: Vec<(U, Option<Doc<'a>>)>,
        predicates: Vec<Doc<'a>>,
        bounds: Vec<Doc<'a>>,
        associated_types: Vec<(U, Vec<Doc<'a>>)>,
        items: Vec<Doc<'a>>,
    ) -> Self {
        Class {
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
        class: Expression,
        field: Doc<'a>,
        value: Doc<'a>,
    ) -> Self {
        Instance {
            name,
            trait_parameters: trait_parameters.to_vec(),
            class,
            field,
            value,
        }
    }

    pub(crate) fn to_doc(&self) -> Doc<'a> {
        concat([
            render::new_instance_header(
                self.name,
                &self.trait_parameters,
                self.class.to_doc(false),
            ),
            nest([
                hardline(),
                render::new_instance_body(self.field.to_owned(), self.value.to_owned()),
            ]),
            hardline(),
            text("}."),
        ])
    }
}

impl Expression {
    pub(crate) fn to_doc<'a>(&self, with_paren: bool) -> Doc<'a> {
        match self {
            Self::Application { func, arg } => paren(
                with_paren,
                group([func.to_doc(false), line(), arg.to_doc(true)]),
            ),
            Self::Variable(path) => path.to_doc(),
        }
    }
}
