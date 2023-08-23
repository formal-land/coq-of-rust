use crate::path::Path;
use crate::render::{
    self, concat, group, hardline, intersperse, line, nest, nil, paren, text, Doc,
};

#[allow(dead_code)]
#[derive(Clone)]
/// any coq top level item
pub(crate) enum TopLevelItem<'a> {
    Code(Doc<'a>),
    Class(Class<'a>),
    Comment(Comment),
    Context(Context),
    Instance(Instance<'a>),
    Module(Module<'a>),
    Section(Section<'a>),
}

#[derive(Clone)]
/// a coq comment
pub(crate) struct Comment {
    text: String,
}

#[derive(Clone)]
/// a coq module
pub(crate) struct Module<'a> {
    name: &'a str,
    content: Vec<TopLevelItem<'a>>,
}

#[derive(Clone)]
/// a coq section
pub(crate) struct Section<'a> {
    name: &'a str,
    content: Vec<TopLevelItem<'a>>,
}

#[derive(Clone)]
/// a coq `Context` item
pub(crate) struct Context {
    args: Vec<ArgSpec>,
}

#[derive(Clone)]
/// a coq definition
pub(crate) struct Class<'a> {
    name: String,
    ty_params: Vec<(String, Option<Doc<'a>>)>,
    predicates: Vec<Doc<'a>>,
    bounds: Vec<Doc<'a>>,
    associated_types: Vec<(String, Vec<Doc<'a>>)>,
    items: Vec<Doc<'a>>,
}

#[derive(Clone)]
/// a global instance of a coq typeclass
pub(crate) struct Instance<'a> {
    name: &'a str,
    parameters: Vec<ArgSpec>,
    class: Expression,
    field: Doc<'a>,
    value: Doc<'a>,
}

#[derive(Clone)]
/// a coq expression
pub(crate) enum Expression {
    Application {
        func: Box<Expression>,
        param: Option<String>,
        arg: Box<Expression>,
    },
    Variable(Path),
}

#[derive(Clone)]
/// a specification of an argument of a coq construction
pub(crate) struct ArgSpec {
    decl: ArgDecl,
    kind: ArgSpecKind,
}

#[derive(Clone)]
/// a variant of the argument specification
pub(crate) enum ArgDecl {
    Normal {
        // @TODO: try to make it really non-empty
        /// a non-empty vector of identifiers
        idents: Vec<String>,
        /// a type of the identifiers
        ty: Option<Expression>,
    },
    Generalized {
        /// a possibly empty vector of identifiers
        idents: Vec<String>,
        /// a type of the identifiers
        ty: Expression,
    },
}

#[derive(Clone)]
/// a kind of an argument
pub(crate) enum ArgSpecKind {
    /// a regular argument
    Explicit,
    /// a maximally inserted implicit argument
    /// (we do not use non-maximal insertion level)
    Implicit,
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

impl<'a> TopLevelItem<'a> {
    pub(crate) fn to_doc(&self) -> Doc<'a> {
        match self {
            TopLevelItem::Code(code) => code.to_owned(),
            TopLevelItem::Class(class) => class.to_doc(),
            TopLevelItem::Comment(comment) => comment.to_doc(),
            TopLevelItem::Context(context) => context.to_doc(),
            TopLevelItem::Instance(instance) => instance.to_doc(),
            TopLevelItem::Module(module) => module.to_doc(),
            TopLevelItem::Section(section) => section.to_doc(),
        }
    }

    /// decides whether to enclose [doc] within a section with a context
    pub(crate) fn add_context_in_section_if_necessary(
        name: &'a str,
        ty_params: &Vec<String>,
        doc: &[TopLevelItem<'a>],
    ) -> Vec<Self> {
        if ty_params.is_empty() {
            doc.to_owned()
        } else {
            vec![TopLevelItem::Section(Section::new(
                name,
                &[
                    &[TopLevelItem::Context(Context::new(&[ArgSpec::new(
                        &ArgDecl::Normal {
                            idents: ty_params.iter().map(|arg| arg.to_owned()).collect(),
                            ty: Some(Expression::set()),
                        },
                        ArgSpecKind::Implicit,
                    )]))],
                    doc,
                ]
                .concat(),
            ))]
        }
    }
}

impl<'a> Module<'a> {
    /// produces a new coq module
    pub(crate) fn new(name: &'a str, content: Vec<TopLevelItem<'a>>) -> Self {
        Module { name, content }
    }

    pub(crate) fn to_doc(&self) -> Doc<'a> {
        render::enclose(
            "Module",
            self.name,
            intersperse(self.content.iter().map(|item| item.to_doc()), [hardline()]),
        )
    }

    /// creates a module with the translation of the given trait
    pub(crate) fn trait_module(
        name: &'a str,
        ty_params: &[(String, Option<Doc<'a>>)],
        predicates: &[Doc<'a>],
        bounds: &[Doc<'a>],
        associated_types: &[(String, Vec<Doc<'a>>)],
        items: Vec<Doc<'a>>,
        instances: Vec<Instance<'a>>,
    ) -> Self {
        Module::new(
            name,
            [
                vec![TopLevelItem::Code(
                    render::locally_unset_primitive_projections_if(
                        items.is_empty(),
                        &Class::new(
                            "Trait",
                            ty_params.to_vec(),
                            predicates.to_vec(),
                            bounds.to_vec(),
                            associated_types.to_vec(),
                            items,
                        )
                        .to_doc(),
                    ),
                )],
                instances
                    .iter()
                    .map(|i| TopLevelItem::Instance(i.to_owned()))
                    .collect(),
            ]
            .concat(),
        )
    }
}

impl<'a> Section<'a> {
    /// produces a new coq module
    pub(crate) fn new(name: &'a str, content: &[TopLevelItem<'a>]) -> Self {
        Section {
            name,
            content: content.to_owned(),
        }
    }

    pub(crate) fn to_doc(&self) -> Doc<'a> {
        render::enclose(
            "Section",
            self.name,
            intersperse(self.content.iter().map(|item| item.to_doc()), [hardline()]),
        )
    }
}

impl Context {
    pub(crate) fn new(args: &[ArgSpec]) -> Self {
        Context {
            args: args.to_owned(),
        }
    }

    pub(crate) fn to_doc<'a>(&self) -> Doc<'a> {
        nest([
            text("Context"),
            line(),
            intersperse(self.args.iter().map(|arg| arg.to_doc()), [line()]),
            text("."),
        ])
    }
}

impl<'a> Class<'a> {
    /// produces a new coq typeclass definition
    pub(crate) fn new(
        name: &str,
        ty_params: Vec<(String, Option<Doc<'a>>)>,
        predicates: Vec<Doc<'a>>,
        bounds: Vec<Doc<'a>>,
        associated_types: Vec<(String, Vec<Doc<'a>>)>,
        items: Vec<Doc<'a>>,
    ) -> Self {
        Class {
            name: name.to_owned(),
            ty_params: ty_params.to_owned(),
            predicates,
            bounds,
            associated_types: associated_types.to_owned(),
            items,
        }
    }

    pub(crate) fn to_doc(&self) -> Doc<'a> {
        group([
            nest([
                render::new_trait_typeclass_header(
                    &self.name,
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
        parameters: &[ArgSpec],
        class: Expression,
        field: Doc<'a>,
        value: Doc<'a>,
    ) -> Self {
        Instance {
            name,
            parameters: parameters.to_vec(),
            class,
            field,
            value,
        }
    }

    pub(crate) fn to_doc(&self) -> Doc<'a> {
        concat([
            render::new_instance_header(
                self.name,
                &self
                    .parameters
                    .iter()
                    .map(|p| p.to_doc())
                    .collect::<Vec<Doc<'a>>>(),
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
            Self::Application { func, param, arg } => paren(
                with_paren,
                group([
                    func.to_doc(false),
                    line(),
                    match param {
                        Some(param) => render::round_brackets(group([
                            text(param.to_owned()),
                            text(" := "),
                            arg.to_doc(true),
                        ])),
                        None => arg.to_doc(true),
                    },
                ]),
            ),
            Self::Variable(path) => path.to_doc(),
        }
    }

    /// a coq Set
    pub(crate) fn set() -> Self {
        Expression::Variable(Path::new(&["Set"]))
    }
}

impl ArgSpec {
    pub(crate) fn new(decl: &ArgDecl, kind: ArgSpecKind) -> Self {
        ArgSpec {
            decl: decl.to_owned(),
            kind,
        }
    }

    pub(crate) fn monadic_typeclass_parameter() -> Self {
        ArgSpec {
            decl: ArgDecl::Generalized {
                idents: vec!["H".to_string()],
                ty: Expression::Variable(Path::new(&["State", "Trait"])),
            },
            kind: ArgSpecKind::Implicit,
        }
    }

    pub(crate) fn to_doc<'a>(&self) -> Doc<'a> {
        let brackets = match self.kind {
            ArgSpecKind::Explicit => render::round_brackets,
            ArgSpecKind::Implicit => render::curly_brackets,
        };
        match self.decl.to_owned() {
            ArgDecl::Normal { idents, ty } => brackets(concat([
                intersperse(idents, [line()]),
                match ty {
                    Some(ty) => concat([line(), text(":"), line(), ty.to_doc(false)]),
                    None => nil(),
                },
            ])),
            ArgDecl::Generalized { idents, ty } => group([
                text("`"),
                brackets(concat([
                    if idents.is_empty() {
                        nil()
                    } else {
                        concat([intersperse(idents, [line()]), line(), text(":"), line()])
                    },
                    ty.to_doc(false),
                ])),
            ]),
        }
    }
}

/// produces a definition of the given function
pub(crate) fn function_header<'a>(
    name: &'a str,
    ty_params: &'a Vec<String>,
    bounds: Vec<Doc<'a>>,
    args: &[(&'a String, Doc<'a>)],
) -> Doc<'a> {
    group([
        text(name),
        if ty_params.is_empty() {
            nil()
        } else {
            group([
                render::curly_brackets(group([
                    // change here if it doesn't work with '{}' brackets
                    intersperse(ty_params, [line()]),
                    text(": Set"),
                ])),
                line(),
            ])
        },
        if bounds.is_empty() {
            nil()
        } else {
            group([intersperse(bounds, [line()]), line()])
        },
        concat(args.iter().map(|(name, ty)| {
            concat([
                line(),
                nest([
                    text("("),
                    text(*name),
                    line(),
                    text(": "),
                    ty.clone(),
                    text(")"),
                ]),
            ])
        })),
    ])
}
