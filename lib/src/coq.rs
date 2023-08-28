use crate::path::Path;
use crate::render::{
    self, concat, group, hardline, intersperse, line, nest, nil, paren, text, Doc,
};

#[derive(Clone)]
/// a list of coq top level items
pub(crate) struct TopLevel<'a> {
    items: Vec<TopLevelItem<'a>>,
}

#[derive(Clone)]
/// any coq top level item
pub(crate) enum TopLevelItem<'a> {
    /// the Code variant is for those constructions
    /// that are not yet represented by the types in this file
    Code(Doc<'a>),
    Class(Class<'a>),
    Comment(Comment),
    Context(Context<'a>),
    Definition(Definition<'a>),
    Instance(Instance<'a>),
    Line,
    Module(Module<'a>),
    Section(Section<'a>),
}

#[derive(Clone)]
/// a coq comment (always occupies whole lines)
pub(crate) struct Comment {
    text: String,
}

#[derive(Clone)]
/// a coq module
pub(crate) struct Module<'a> {
    name: String,
    items: TopLevel<'a>,
}

#[derive(Clone)]
/// a coq section
pub(crate) struct Section<'a> {
    name: &'a str,
    items: TopLevel<'a>,
}

#[derive(Clone)]
/// a coq constant definition
pub(crate) struct Definition<'a> {
    name: String,
    kind: DefinitionKind<'a>,
}

#[derive(Clone)]
/// a coq `Context` item
pub(crate) struct Context<'a> {
    args: Vec<ArgDecl<'a>>,
}

#[derive(Clone)]
/// a coq typeclass definition
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
    parameters: Vec<ArgDecl<'a>>,
    class: Expression<'a>,
    field: Doc<'a>,
    value: Doc<'a>,
}

#[derive(Clone)]
/// the kind of a coq definition
pub(crate) enum DefinitionKind<'a> {
    /// an alias for an expression
    /// (using `Definition`)
    Alias {
        args: Vec<ArgDecl<'a>>,
        ty: Option<Expression<'a>>,
        body: Expression<'a>,
    },
    /// an opaque constant
    /// (using `Parameter`)
    Assumption { ty: Expression<'a> },
}

#[derive(Clone)]
/// a coq expression
/// (sutable also for coq type expressions,
///     because in coq types are like any other values)
pub(crate) enum Expression<'a> {
    /// the Code variant is for those constructions
    /// that are not yet represented by the types in this file
    Code(Doc<'a>),
    /// an (curried) application of a function to some arguments
    Application {
        /// the function that is applied
        func: Box<Expression<'a>>,
        /// a nonempty list of arguments
        /// (we accept many arguments to control their indentation better,
        ///     the application is curried when it gets printed)
        args: Vec<(Option<String>, Expression<'a>)>,
    },
    /// a (curried) function type
    Function {
        /// a nonempty list of domains
        /// (we accept many domains to control their indentation in the type better,
        ///     the type is curried when it gets printed)
        domains: Vec<Expression<'a>>,
        /// the image (range, co-domain) of functions of the type
        image: Box<Expression<'a>>,
    },
    /// a dependent product of types
    /// (like `forall (x : A), B(x)`)
    PiType {
        /// a list of arguments of `forall`
        args: Vec<ArgDecl<'a>>,
        /// the expression for the resulting type
        image: Box<Expression<'a>>,
    },
    /// a product of two variables (they can be types or numbers)
    Product {
        /// left hand side
        lhs: Box<Expression<'a>>,
        /// right hand side
        rhs: Box<Expression<'a>>,
    },
    /// Set constant (the type of our types)
    Set,
    /// the unit type
    Unit,
    /// a single variable
    Variable {
        /// a list of names (a path) used to refer to the variable
        ident: Path,
        /// a flag, set if implicit arguments are deactivated with '@'
        no_implicit: bool,
    },
}

#[derive(Clone)]
/// a declaration of an argument of a coq construction
pub(crate) struct ArgDecl<'a> {
    decl: ArgDeclVar<'a>,
    kind: ArgSpecKind,
}

#[derive(Clone)]
/// a variant of the argument declaration
pub(crate) enum ArgDeclVar<'a> {
    /// a regular declaration
    Normal {
        // @TODO: try to make it really non-empty
        /// a non-empty vector of identifiers
        idents: Vec<String>,
        /// a type of the identifiers
        ty: Option<Expression<'a>>,
    },
    /// a generalized declaration (preceded by `` ` ``)
    Generalized {
        /// a possibly empty vector of identifiers
        idents: Vec<String>,
        /// a type of the identifiers
        ty: Expression<'a>,
    },
}

#[derive(Clone)]
/// a kind of an argument
pub(crate) enum ArgSpecKind {
    /// a regular argument
    /// (with `()` brackets)
    Explicit,
    /// a maximally inserted implicit argument
    /// (with `{}` brackets)
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

impl<'a> TopLevel<'a> {
    /// produces a new list of coq items
    pub(crate) fn new(items: &[TopLevelItem<'a>]) -> Self {
        TopLevel {
            items: items.to_vec(),
        }
    }

    pub(crate) fn to_doc(&self) -> Doc<'a> {
        intersperse(self.items.iter().map(|item| item.to_doc()), [hardline()])
    }

    /// joins a list of lists of items into one list
    pub(crate) fn concat(tls: &[Self]) -> Self {
        TopLevel {
            items: tls.iter().flat_map(|tl| tl.items.to_owned()).collect(),
        }
    }

    /// locally unsets primitive projecitons
    pub(crate) fn locally_unset_primitive_projections(items: &[TopLevelItem<'a>]) -> Self {
        TopLevel {
            items: [
                vec![TopLevelItem::Code(text("Unset Primitive Projections."))],
                items.to_vec(),
                vec![TopLevelItem::Code(text(
                    "Global Set Primitive Projections.",
                ))],
            ]
            .concat(),
        }
    }

    /// locally unsets primitive projecitons if the condition is satisfied
    pub(crate) fn locally_unset_primitive_projections_if(
        condition: bool,
        items: &[TopLevelItem<'a>],
    ) -> Self {
        if condition {
            TopLevel::locally_unset_primitive_projections(items)
        } else {
            TopLevel {
                items: [items.to_vec(), vec![TopLevelItem::Line]].concat(),
            }
        }
    }

    /// decides whether to enclose [items] within a section with a context
    pub(crate) fn add_context_in_section_if_necessary(
        name: &'a str,
        ty_params: &[String],
        items: &[TopLevelItem<'a>],
    ) -> Self {
        if ty_params.is_empty() {
            TopLevel {
                items: items.to_owned(),
            }
        } else {
            TopLevel::add_context_in_section(name, ty_params, items)
        }
    }

    /// creates a section with a context with type variables
    /// with the given variable names
    pub(crate) fn add_context_in_section(
        name: &'a str,
        ty_params: &[String],
        items: &[TopLevelItem<'a>],
    ) -> Self {
        TopLevel {
            items: vec![TopLevelItem::Section(Section::new(
                name,
                &TopLevel {
                    items: [
                        &[TopLevelItem::Context(Context::new(&[ArgDecl::new(
                            &ArgDeclVar::Normal {
                                idents: ty_params.iter().map(|arg| arg.to_owned()).collect(),
                                ty: Some(Expression::Set),
                            },
                            ArgSpecKind::Implicit,
                        )]))],
                        items,
                    ]
                    .concat(),
                },
            ))],
        }
    }
}

impl<'a> TopLevelItem<'a> {
    pub(crate) fn to_doc(&self) -> Doc<'a> {
        match self {
            TopLevelItem::Code(code) => code.to_owned(),
            TopLevelItem::Class(class) => class.to_doc(),
            TopLevelItem::Comment(comment) => comment.to_doc(),
            TopLevelItem::Context(context) => context.to_doc(),
            TopLevelItem::Definition(definition) => definition.to_doc(),
            TopLevelItem::Instance(instance) => instance.to_doc(),
            TopLevelItem::Line => nil(),
            TopLevelItem::Module(module) => module.to_doc(),
            TopLevelItem::Section(section) => section.to_doc(),
        }
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
        TopLevelItem::Module(Module::new(
            name,
            TopLevel::concat(&[
                TopLevel::locally_unset_primitive_projections_if(
                    items.is_empty(),
                    &[TopLevelItem::Class(Class::new(
                        "Trait",
                        ty_params.to_vec(),
                        predicates.to_vec(),
                        bounds.to_vec(),
                        associated_types.to_vec(),
                        items,
                    ))],
                ),
                TopLevel {
                    items: instances
                        .iter()
                        .map(|i| TopLevelItem::Instance(i.to_owned()))
                        .collect(),
                },
            ]),
        ))
    }
}

impl<'a> Module<'a> {
    /// produces a new coq module
    pub(crate) fn new(name: &str, content: TopLevel<'a>) -> Self {
        Module {
            name: name.to_string(),
            items: content,
        }
    }

    pub(crate) fn to_doc(&self) -> Doc<'a> {
        render::enclose("Module", self.name.to_owned(), self.items.to_doc())
    }
}

impl<'a> Section<'a> {
    /// produces a new coq section
    pub(crate) fn new(name: &'a str, content: &TopLevel<'a>) -> Self {
        Section {
            name,
            items: content.to_owned(),
        }
    }

    pub(crate) fn to_doc(&self) -> Doc<'a> {
        render::enclose("Section", self.name.to_owned(), self.items.to_doc())
    }
}

impl<'a> Definition<'a> {
    /// produces a new coq definition
    pub(crate) fn new(name: &str, kind: &DefinitionKind<'a>) -> Self {
        Definition {
            name: name.to_owned(),
            kind: kind.to_owned(),
        }
    }

    pub(crate) fn to_doc(&self) -> Doc<'a> {
        match self.kind.to_owned() {
            DefinitionKind::Alias { args, ty, body } => nest([
                nest([
                    group([text("Definition"), line(), text(self.name.to_owned())]),
                    group([
                        if args.is_empty() {
                            nil()
                        } else {
                            concat([
                                line(),
                                intersperse(args.iter().map(|arg| arg.to_doc()), [line()]),
                            ])
                        },
                        match ty {
                            Some(ty) => {
                                concat([line(), nest([text(":"), line(), ty.to_doc(false)])])
                            }
                            None => nil(),
                        },
                        text(" :="),
                    ]),
                ]),
                line(),
                body.to_doc(false),
                text("."),
            ]),
            DefinitionKind::Assumption { ty } => nest([
                nest([
                    text("Parameter"),
                    line(),
                    text(self.name.to_owned()),
                    line(),
                ]),
                nest([text(":"), line(), ty.to_doc(false)]),
                text("."),
            ]),
        }
    }
}

impl<'a> Context<'a> {
    /// produces a new coq `Context`
    pub(crate) fn new(args: &[ArgDecl<'a>]) -> Self {
        Context {
            args: args.to_owned(),
        }
    }

    pub(crate) fn to_doc(&self) -> Doc<'a> {
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
        parameters: &[ArgDecl<'a>],
        class: Expression<'a>,
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

impl<'a> Expression<'a> {
    pub(crate) fn to_doc(&self, with_paren: bool) -> Doc<'a> {
        match self {
            Self::Code(doc) => paren(with_paren, doc.to_owned()),
            Self::Application { func, args } => paren(
                with_paren,
                nest([
                    func.to_doc(false),
                    if args.is_empty() { nil() } else { line() },
                    intersperse(
                        args.iter().map(|(param, arg)| match param {
                            Some(param) => render::round_brackets(group([
                                text(param.to_owned()),
                                text(" := "),
                                arg.to_doc(false),
                            ])),
                            None => arg.to_doc(true),
                        }),
                        [line()],
                    ),
                ]),
            ),
            Self::Function { domains, image } => paren(
                with_paren,
                nest([
                    intersperse(
                        domains
                            .iter()
                            .map(|domain| group([domain.to_doc(true), line(), text("->")])),
                        [line()],
                    ),
                    if domains.is_empty() { nil() } else { line() },
                    image.to_doc(false),
                ]),
            ),
            Self::PiType { args, image } => paren(
                with_paren,
                concat([
                    nest([
                        text("forall"),
                        line(),
                        intersperse(args.iter().map(|arg| arg.to_doc()), [line()]),
                        text(","),
                    ]),
                    line(),
                    image.to_doc(false),
                ]),
            ),
            Self::Product { lhs, rhs } => paren(
                with_paren,
                group([
                    lhs.to_doc(true),
                    line(),
                    text("*"),
                    line(),
                    rhs.to_doc(true),
                ]),
            ),
            Self::Set => text("Set"),
            Self::Unit => text("unit"),
            Self::Variable { ident, no_implicit } => {
                concat([if *no_implicit { text("@") } else { nil() }, ident.to_doc()])
            }
        }
    }

    /// apply the expression as a function to one argument
    pub(crate) fn apply(&self, arg: &Self) -> Self {
        Expression::Application {
            func: Box::new(self.clone()),
            args: vec![(None, arg.clone())],
        }
    }

    /// apply the expression as a function to many arguments
    pub(crate) fn apply_many(&self, args: &[Self]) -> Self {
        Expression::Application {
            func: Box::new(self.to_owned()),
            args: args.iter().map(|arg| (None, arg.to_owned())).collect(),
        }
    }

    pub(crate) fn arrows_from(&self, domains: &[Self]) -> Self {
        Expression::Function {
            domains: domains.to_owned(),
            image: Box::new(self.to_owned()),
        }
    }

    pub(crate) fn multiply(lhs: Self, rhs: Self) -> Self {
        Expression::Product {
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        }
    }

    pub(crate) fn multiply_many(exprs: &[Self]) -> Self {
        let product = exprs
            .iter()
            .map(|e| e.to_owned())
            .reduce(Expression::multiply);
        match product {
            Some(product) => product,
            None => Expression::Unit,
        }
    }
}

impl<'a> ArgDecl<'a> {
    /// produces a new coq argument
    pub(crate) fn new(decl: &ArgDeclVar<'a>, kind: ArgSpecKind) -> Self {
        ArgDecl {
            decl: decl.to_owned(),
            kind,
        }
    }

    /// provides the instance of the Struct.Trait typeclass
    /// for definitions of functions and constants
    /// which types utilize the M monad constructor
    pub(crate) fn monadic_typeclass_parameter() -> Self {
        ArgDecl {
            decl: ArgDeclVar::Generalized {
                // @TODO: check whether the name of the parameter is necessary
                idents: vec!["H".to_string()],
                ty: Expression::Variable {
                    ident: Path::new(&["State", "Trait"]),
                    no_implicit: false,
                },
            },
            kind: ArgSpecKind::Implicit,
        }
    }

    pub(crate) fn to_doc(&self) -> Doc<'a> {
        let brackets = match self.kind {
            ArgSpecKind::Explicit => render::round_brackets,
            ArgSpecKind::Implicit => render::curly_brackets,
        };
        match self.decl.to_owned() {
            ArgDeclVar::Normal { idents, ty } => brackets(nest([
                intersperse(idents, [line()]),
                match ty {
                    Some(ty) => concat([line(), text(":"), line(), ty.to_doc(false)]),
                    None => nil(),
                },
            ])),
            ArgDeclVar::Generalized { idents, ty } => group([
                text("`"),
                brackets(nest([
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

    pub(crate) fn of_ty_params(ty_params: &[String]) -> Self {
        ArgDecl {
            decl: ArgDeclVar::Normal {
                idents: ty_params.to_owned(),
                ty: Some(Expression::Set),
            },
            kind: ArgSpecKind::Implicit,
        }
    }
}

/// produces a definition of the given function
pub(crate) fn function_header<'a>(
    name: &Path,
    params: &[ArgDecl<'a>],
    args: &[(&'a String, Doc<'a>)],
) -> Doc<'a> {
    group([
        name.to_doc(),
        if params.is_empty() {
            nil()
        } else {
            group([
                line(),
                intersperse(params.iter().map(|param| param.to_doc()), [line()]),
            ])
        },
        concat(args.iter().map(|(name, ty)| {
            concat([nest([
                line(),
                text("("),
                text(*name),
                line(),
                text(": "),
                ty.clone(),
                text(")"),
            ])])
        })),
    ])
}
