use crate::path::Path;
use crate::render::{
    curly_brackets, enclose, group, list, nest, optional_insert, optional_insert_with, paren,
    round_brackets,
};
use pretty::{DocAllocator, DocBuilder};
use std::rc::Rc;

#[derive(Clone)]
/// a list of coq top level items
pub(crate) struct TopLevel {
    pub(crate) items: Vec<Rc<TopLevelItem>>,
}

#[derive(Clone)]
/// any coq top level item
pub(crate) enum TopLevelItem {
    Comment(Vec<Rc<Expression>>),
    Definition(Rc<Definition>),
    Hint {
        kind: String,
        name: String,
        database: Option<String>,
    },
    Line,
    Module(Rc<Module>),
    Empty,
}

#[derive(Clone)]
/// a coq module
pub(crate) struct Module {
    name: String,
    items: Rc<TopLevel>,
}

#[derive(Clone)]
/// a coq constant definition
pub(crate) struct Definition {
    name: String,
    kind: Rc<DefinitionKind>,
}

#[derive(Clone)]
/// the kind of a coq definition
pub(crate) enum DefinitionKind {
    AdmittedInstance {
        locality: String,
        ty: Rc<Expression>,
    },
    /// an alias for an expression
    /// (using `Definition`)
    Alias {
        args: Vec<Rc<ArgDecl>>,
        ty: Option<Rc<Expression>>,
        body: Rc<Expression>,
    },
    /// an opaque constant
    /// (using `Parameter`)
    Assumption { ty: Rc<Expression> },
    /// an axiom
    /// (using `Axiom`)
    Axiom { ty: Rc<Expression> },
    /// a definition with an `exact` tactic
    #[allow(dead_code)]
    Ltac {
        args: Vec<String>,
        body: Rc<Expression>,
    },
}

#[derive(Clone)]
/// a coq expression
/// (suitable also for coq type expressions,
///     because in coq types are like any other values)
pub(crate) enum Expression {
    /// an (curried) application of a function to some arguments
    Application {
        /// the function that is applied
        func: Rc<Expression>,
        /// a nonempty list of arguments
        /// (we accept many arguments to control their indentation better,
        ///     the application is curried when it gets printed)
        args: Vec<(Option<String>, Rc<Expression>)>,
    },
    MonadicApplication {
        func: Rc<Expression>,
        args: Vec<(Option<String>, Rc<Expression>)>,
    },
    /// a (curried) function
    Function {
        parameters: Vec<Rc<Expression>>,
        body: Rc<Expression>,
    },
    Let {
        name: Option<String>,
        is_user: bool,
        ty: Option<Rc<Expression>>,
        init: Rc<Expression>,
        body: Rc<Expression>,
    },
    Match {
        scrutinees: Vec<Rc<Expression>>,
        arms: Vec<(Vec<Rc<Expression>>, Rc<Expression>)>,
    },
    /// a (curried) function type
    FunctionType {
        /// a nonempty list of domains
        /// (we accept many domains to control their indentation in the type better,
        ///     the type is curried when it gets printed)
        domains: Vec<Rc<Expression>>,
        /// the image (range, co-domain) of functions of the type
        image: Rc<Expression>,
    },
    /// a dependent product of types
    /// (like `forall (x : A), B(x)`)
    PiType {
        /// a list of arguments of `forall`
        args: Vec<Rc<ArgDecl>>,
        /// the expression for the resulting type
        image: Rc<Expression>,
    },
    /// The equality of two expressions `lhs = rhs`
    Equality {
        lhs: Rc<Expression>,
        rhs: Rc<Expression>,
    },
    /// a product of two variables (they can be types or numbers)
    Product {
        /// left hand side
        lhs: Rc<Expression>,
        /// right hand side
        rhs: Rc<Expression>,
    },
    /// A tuple of expressions `(e1, e2, ...)`
    Tuple(Vec<Rc<Expression>>),
    Record {
        fields: Vec<Rc<Field>>,
    },
    #[allow(dead_code)]
    RecordField {
        record: Rc<Expression>,
        field: String,
    },
    #[allow(dead_code)]
    RecordUpdate {
        record: Rc<Expression>,
        field: String,
        update: Rc<Expression>,
    },
    List {
        exprs: Vec<Rc<Expression>>,
    },
    /// For example ltac:(...) or constr:(...)
    ModeWrapper {
        mode: String,
        expr: Rc<Expression>,
    },
    /// Comment next to an expression
    Comment(String, Rc<Expression>),
    /// `as` expression in patterns
    As(Rc<Expression>, Rc<Expression>),
    /// An integer
    U128(u128),
    /// a string in quotes
    String(String),
    /// a plain string in the code
    Message(String),
    /// a single variable
    Variable {
        /// a list of names (a path) used to refer to the variable
        ident: Rc<Path>,
        /// a flag, set if implicit arguments are deactivated with '@'
        no_implicit: bool,
    },
    /// a wildcard: '_'
    Wild,
}

/// a field of a record expression
#[derive(Clone)]
pub(crate) struct Field {
    pub(crate) name: String,
    pub(crate) args: Vec<Rc<ArgDecl>>,
    pub(crate) body: Rc<Expression>,
}

#[derive(Clone)]
/// a declaration of an argument of a coq construction
pub(crate) struct ArgDecl {
    decl: Rc<ArgDeclVar>,
    kind: ArgSpecKind,
}

#[derive(Clone)]
/// a variant of the argument declaration
pub(crate) enum ArgDeclVar {
    /// a regular declaration
    Simple {
        // @TODO: try to make it really non-empty
        /// a non-empty vector of identifiers
        idents: Vec<String>,
        /// a type of the identifiers
        ty: Option<Rc<Expression>>,
    },
    /// a generalized declaration (preceded by `` ` ``)
    #[allow(dead_code)]
    Generalized {
        /// a possibly empty vector of identifiers
        idents: Vec<String>,
        /// a type of the identifiers
        ty: Rc<Expression>,
    },
    /// a destructured argument
    #[allow(dead_code)]
    Destructured { pattern: Rc<Expression> },
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
    #[allow(dead_code)]
    Implicit,
}

impl TopLevel {
    /// produces a new list of coq items
    pub(crate) fn new(items: &[Rc<TopLevelItem>]) -> Rc<Self> {
        Rc::new(TopLevel {
            items: items.to_vec(),
        })
    }

    /// Get the list of modules that have a given name, as well as the remaining items once we
    /// remove those.
    fn get_modules_of_name(
        top_level_items: &[Rc<TopLevelItem>],
        name: &str,
    ) -> (Vec<Rc<Module>>, Vec<Rc<TopLevelItem>>) {
        top_level_items.iter().fold(
            (vec![], vec![]),
            |(mut matching_modules, mut other_items), item| {
                match item.as_ref() {
                    TopLevelItem::Module(module) if module.name == name => {
                        matching_modules.push(module.clone());
                    }
                    _ => {
                        other_items.push(item.clone());
                    }
                };

                (matching_modules, other_items)
            },
        )
    }

    /// Remove a potential leading `Self` in the module, as this would collide with previous
    /// definitions.
    fn remove_self_ty(self: Rc<Self>) -> Rc<Self> {
        if let [first, second, rest @ ..] = self.items.as_slice() {
            if let (TopLevelItem::Definition(definition), TopLevelItem::Line) =
                (first.as_ref(), second.as_ref())
            {
                if definition.name == "Self" {
                    return Rc::new(TopLevel {
                        items: rest.to_vec(),
                    });
                }
            }
        }

        self
    }

    /// A same module can be implemented in many small bits, for example with the `impl` of a same
    /// type but split in many places in a file. With this method we group the modules with the same
    /// name together. We take care of de-duplicating the `Self` definition if there is one.
    /// We do so because in Coq we cannot have two separate modules with the same name.
    fn group_modules(top_level_items: &[Rc<TopLevelItem>]) -> Vec<Rc<TopLevelItem>> {
        match top_level_items {
            [] => vec![],
            [item, rest @ ..] => match item.as_ref() {
                TopLevelItem::Module(module) => {
                    let (matching_modules, other_items) =
                        Self::get_modules_of_name(rest, &module.name);

                    [
                        vec![Rc::new(TopLevelItem::Module(Module::new(
                            &module.name,
                            Self::concat(
                                &[
                                    vec![module.items.clone()],
                                    matching_modules
                                        .into_iter()
                                        .map(|matching_module| {
                                            matching_module.items.clone().remove_self_ty()
                                        })
                                        .collect(),
                                ]
                                .concat(),
                            ),
                        )))],
                        Self::group_modules(&other_items),
                    ]
                    .concat()
                }
                _ => [vec![item.clone()], Self::group_modules(rest)].concat(),
            },
        }
    }

    pub(crate) fn to_doc<'a, D>(&self, ψ: &'a D) -> DocBuilder<'a, D>
    where
        D: DocAllocator<'a>,
        D::Doc: Clone,
    {
        ψ.intersperse(
            Self::group_modules(&self.items)
                .iter()
                .filter_map(|item| item.to_doc(ψ)),
            ψ.hardline(),
        )
    }

    /// joins a list of lists of items into one list
    pub(crate) fn concat(tls: &[Rc<Self>]) -> Rc<Self> {
        Rc::new(TopLevel {
            items: tls.iter().flat_map(|tl| tl.items.clone()).collect(),
        })
    }
}

impl TopLevelItem {
    pub(crate) fn to_doc<'a, D>(&self, ψ: &'a D) -> Option<DocBuilder<'a, D>>
    where
        D: DocAllocator<'a>,
        D::Doc: Clone,
    {
        match self {
            TopLevelItem::Comment(expression) => {
                let expression: Vec<_> = expression.iter().map(|e| e.to_doc(ψ, false)).collect();
                if expression.len() <= 1 {
                    Some(ψ.concat([vec![ψ.text("(* ")], expression, vec![ψ.text(" *)")]].concat()))
                } else {
                    Some(ψ.intersperse(
                        [vec![ψ.text("(*")], expression, vec![ψ.text("*)")]].concat(),
                        ψ.hardline(),
                    ))
                }
            }
            TopLevelItem::Definition(definition) => Some(definition.to_doc(ψ)),
            TopLevelItem::Hint {
                kind,
                name,
                database,
            } => Some(nest(
                ψ,
                [
                    vec![
                        ψ.text(kind.to_owned()),
                        ψ.text(" "),
                        ψ.text(name.to_owned()),
                    ],
                    match database {
                        None => vec![],
                        Some(database) => vec![ψ.text(" :"), ψ.line(), ψ.text(database.to_owned())],
                    },
                    vec![ψ.text(".")],
                ]
                .concat(),
            )),
            TopLevelItem::Line => Some(ψ.nil()),
            TopLevelItem::Module(module) => Some(module.to_doc(ψ)),
            TopLevelItem::Empty => None,
        }
    }
}

impl Module {
    /// produces a new coq module
    pub(crate) fn new(name: &str, items: Rc<TopLevel>) -> Rc<Self> {
        Rc::new(Module {
            name: name.to_string(),
            items,
        })
    }

    pub(crate) fn to_doc<'a, D>(&self, ψ: &'a D) -> DocBuilder<'a, D>
    where
        D: DocAllocator<'a>,
        D::Doc: Clone,
    {
        if self.items.items.is_empty() {
            return ψ.text(format!("(* Empty module '{}' *)", self.name));
        }

        enclose(ψ, "Module", self.name.clone(), true, self.items.to_doc(ψ))
    }
}

impl Definition {
    /// produces a new coq definition
    pub(crate) fn new(name: &str, kind: Rc<DefinitionKind>) -> Rc<Self> {
        Rc::new(Definition {
            name: name.to_owned(),
            kind,
        })
    }

    pub(crate) fn to_doc<'a, D>(&self, ψ: &'a D) -> DocBuilder<'a, D>
    where
        D: DocAllocator<'a>,
        D::Doc: Clone,
    {
        match self.kind.as_ref() {
            DefinitionKind::AdmittedInstance { locality, ty } => ψ.concat([
                nest(
                    ψ,
                    [
                        ψ.text(locality.clone()),
                        ψ.text(" Instance "),
                        ψ.text(self.name.clone()),
                        ψ.text(" :"),
                        ψ.line(),
                        ty.to_doc(ψ, false),
                        ψ.text("."),
                    ],
                ),
                ψ.hardline(),
                ψ.text("Admitted."),
            ]),
            DefinitionKind::Alias { args, ty, body } => nest(
                ψ,
                [
                    nest(
                        ψ,
                        [
                            group(
                                ψ,
                                [ψ.text("Definition"), ψ.line(), ψ.text(self.name.to_owned())],
                            ),
                            group(
                                ψ,
                                [
                                    ψ.concat(args.iter().filter_map(|arg| {
                                        if arg.is_empty() {
                                            None
                                        } else {
                                            Some(ψ.concat([ψ.line(), arg.to_doc(ψ)]))
                                        }
                                    })),
                                    match ty {
                                        Some(ty) => ψ.concat([
                                            ψ.line(),
                                            nest(ψ, [ψ.text(":"), ψ.line(), ty.to_doc(ψ, false)]),
                                        ]),
                                        None => ψ.nil(),
                                    },
                                    ψ.text(" :="),
                                ],
                            ),
                        ],
                    ),
                    ψ.line(),
                    body.to_doc(ψ, false),
                    ψ.text("."),
                ],
            ),
            DefinitionKind::Assumption { ty } => nest(
                ψ,
                [
                    nest(
                        ψ,
                        [
                            ψ.text("Parameter"),
                            ψ.line(),
                            ψ.text(self.name.to_owned()),
                            ψ.line(),
                        ],
                    ),
                    nest(ψ, [ψ.text(":"), ψ.line(), ty.to_doc(ψ, false)]),
                    ψ.text("."),
                ],
            ),
            DefinitionKind::Axiom { ty } => nest(
                ψ,
                [
                    nest(
                        ψ,
                        [
                            ψ.text("Axiom"),
                            ψ.line(),
                            ψ.text(self.name.to_owned()),
                            ψ.text(" :"),
                        ],
                    ),
                    ψ.line(),
                    ty.to_doc(ψ, false),
                    ψ.text("."),
                ],
            ),
            DefinitionKind::Ltac { args, body } => nest(
                ψ,
                [
                    nest(
                        ψ,
                        [
                            nest(ψ, [ψ.text("Ltac"), ψ.line(), ψ.text(self.name.to_owned())]),
                            ψ.concat(
                                args.iter()
                                    .map(|arg| ψ.concat([ψ.line(), ψ.text(arg.clone())])),
                            ),
                            ψ.text(" :="),
                        ],
                    ),
                    ψ.line(),
                    nest(ψ, [ψ.text("exact"), ψ.line(), body.to_doc(ψ, true)]),
                    ψ.text("."),
                ],
            ),
        }
    }
}

impl Expression {
    pub(crate) fn to_doc<'a, D>(&self, ψ: &'a D, with_paren: bool) -> DocBuilder<'a, D>
    where
        D: DocAllocator<'a>,
        D::Doc: Clone,
    {
        match self {
            Self::Application { func, args } => paren(
                ψ,
                with_paren,
                nest(
                    ψ,
                    [
                        func.to_doc(ψ, false),
                        optional_insert(ψ, args.is_empty(), ψ.line()),
                        ψ.intersperse(
                            args.iter().map(|(param, arg)| match param {
                                Some(param) => round_brackets(
                                    ψ,
                                    group(
                                        ψ,
                                        [
                                            ψ.text(param.to_owned()),
                                            ψ.text(" := "),
                                            arg.to_doc(ψ, false),
                                        ],
                                    ),
                                ),
                                None => arg.to_doc(ψ, true),
                            }),
                            ψ.line(),
                        ),
                    ],
                ),
            ),
            Self::MonadicApplication { func, args } => paren(
                ψ,
                with_paren,
                group(
                    ψ,
                    [
                        func.to_doc(ψ, false),
                        ψ.text(" "),
                        optional_insert(ψ, !args.is_empty(), ψ.text("(||)")),
                        optional_insert(
                            ψ,
                            args.is_empty(),
                            ψ.concat([
                                ψ.text("(|"),
                                ψ.concat([
                                    ψ.line(),
                                    ψ.intersperse(
                                        args.iter().map(|(param, arg)| match param {
                                            Some(param) => round_brackets(
                                                ψ,
                                                nest(
                                                    ψ,
                                                    [
                                                        ψ.text(param.to_owned()),
                                                        ψ.text(" := "),
                                                        arg.to_doc(ψ, false),
                                                    ],
                                                ),
                                            ),
                                            None => arg.to_doc(ψ, false),
                                        }),
                                        ψ.concat([ψ.text(","), ψ.line()]),
                                    ),
                                ])
                                .nest(2),
                                ψ.line(),
                                ψ.text("|)"),
                            ]),
                        ),
                    ],
                ),
            ),
            Self::Function { parameters, body } => {
                if parameters.is_empty() {
                    body.to_doc(ψ, with_paren)
                } else {
                    paren(
                        ψ,
                        with_paren,
                        nest(
                            ψ,
                            [
                                nest(
                                    ψ,
                                    [
                                        ψ.text("fun"),
                                        ψ.concat(parameters.iter().map(|parameter| {
                                            ψ.concat([ψ.line(), parameter.to_doc(ψ, true)])
                                        })),
                                        ψ.text(" =>"),
                                    ],
                                ),
                                ψ.line(),
                                body.to_doc(ψ, false),
                            ],
                        ),
                    )
                }
            }
            Self::Let {
                name,
                is_user,
                ty,
                init,
                body,
            } => {
                // NOTE: The following variable is intended to bypass self-referencing issue for borrow checkers.
                // See: https://users.rust-lang.org/t/argument-requires-that-1-must-outlive-a/105444
                let name = match name {
                    Some(name) => name.as_str(),
                    None => "_",
                }
                .to_string();
                paren(
                    ψ,
                    with_paren,
                    group(
                        ψ,
                        [
                            nest(
                                ψ,
                                [
                                    nest(
                                        ψ,
                                        [
                                            nest(
                                                ψ,
                                                [
                                                    ψ.text("let"),
                                                    optional_insert(ψ, !*is_user, ψ.text("~")),
                                                    ψ.line(),
                                                    ψ.text(name),
                                                ],
                                            ),
                                            match ty {
                                                None => ψ.nil(),
                                                Some(ty) => ψ.concat([
                                                    ψ.text(" :"),
                                                    ψ.line(),
                                                    ty.to_doc(ψ, false),
                                                ]),
                                            },
                                            ψ.text(" :="),
                                        ],
                                    ),
                                    ψ.line(),
                                    init.to_doc(ψ, false),
                                    ψ.text(" in"),
                                ],
                            ),
                            ψ.hardline(),
                            body.to_doc(ψ, false),
                        ],
                    ),
                )
            }
            Self::Match { scrutinees, arms } => group(
                ψ,
                [
                    group(
                        ψ,
                        [
                            nest(
                                ψ,
                                [
                                    ψ.text("match"),
                                    ψ.line(),
                                    ψ.intersperse(
                                        scrutinees
                                            .iter()
                                            .map(|scrutinee| scrutinee.to_doc(ψ, false)),
                                        ψ.concat([ψ.text(","), ψ.line()]),
                                    ),
                                ],
                            ),
                            ψ.line(),
                            ψ.text("with"),
                        ],
                    ),
                    ψ.concat(arms.iter().map(|(patterns, body)| {
                        ψ.concat([
                            ψ.line(),
                            nest(
                                ψ,
                                [
                                    nest(
                                        ψ,
                                        [
                                            ψ.text("| "),
                                            ψ.intersperse(
                                                patterns
                                                    .iter()
                                                    .map(|pattern| pattern.to_doc(ψ, false)),
                                                ψ.concat([ψ.text(","), ψ.line()]),
                                            ),
                                            ψ.text(" =>"),
                                        ],
                                    ),
                                    ψ.line(),
                                    body.to_doc(ψ, false),
                                ],
                            ),
                        ])
                    })),
                    ψ.line(),
                    ψ.text("end"),
                ],
            ),
            Self::FunctionType { domains, image } => paren(
                ψ,
                with_paren,
                nest(
                    ψ,
                    [
                        ψ.intersperse(
                            domains.iter().map(|domain| {
                                group(ψ, [domain.to_doc(ψ, true), ψ.line(), ψ.text("->")])
                            }),
                            ψ.line(),
                        ),
                        optional_insert(ψ, domains.is_empty(), ψ.line()),
                        image.to_doc(ψ, false),
                    ],
                ),
            ),
            Self::PiType { args, image } => optional_insert_with(
                args.iter().all(|arg| arg.is_empty()),
                image.to_doc(ψ, with_paren),
                paren(
                    ψ,
                    with_paren,
                    ψ.concat([
                        nest(
                            ψ,
                            [
                                ψ.text("forall"),
                                ψ.line(),
                                ψ.intersperse(
                                    args.iter()
                                        .filter(|arg| !arg.is_empty())
                                        .map(|arg| arg.to_doc(ψ)),
                                    ψ.line(),
                                ),
                                ψ.text(","),
                            ],
                        ),
                        ψ.line(),
                        image.to_doc(ψ, false),
                    ]),
                ),
            ),
            Self::Equality { lhs, rhs } => paren(
                ψ,
                with_paren,
                nest(
                    ψ,
                    [
                        lhs.to_doc(ψ, true),
                        ψ.text(" ="),
                        ψ.line(),
                        rhs.to_doc(ψ, true),
                    ],
                ),
            ),
            Self::Product { lhs, rhs } => paren(
                ψ,
                with_paren,
                group(
                    ψ,
                    [
                        lhs.to_doc(ψ, true),
                        ψ.line(),
                        ψ.text("*"),
                        ψ.line(),
                        rhs.to_doc(ψ, true),
                    ],
                ),
            ),
            Self::Tuple(es) => nest(
                ψ,
                [
                    ψ.text("("),
                    ψ.intersperse(
                        es.iter().map(|e| e.to_doc(ψ, false)),
                        ψ.concat([ψ.text(","), ψ.line()]),
                    ),
                    ψ.text(")"),
                ],
            ),
            Self::Record { fields } => ψ.concat([curly_brackets(
                ψ,
                ψ.concat([
                    optional_insert(
                        ψ,
                        fields.is_empty(),
                        nest(
                            ψ,
                            [
                                ψ.hardline(),
                                ψ.intersperse(
                                    fields.iter().map(|field| field.to_doc(ψ)),
                                    ψ.hardline(),
                                ),
                            ],
                        ),
                    ),
                    ψ.hardline(),
                ]),
            )]),
            Self::RecordField { record, field } => ψ.concat([
                record.to_doc(ψ, true),
                ψ.text(".("),
                ψ.text(field.to_owned()),
                ψ.text(")"),
            ]),
            Self::RecordUpdate {
                record,
                field,
                update,
            } => paren(
                ψ,
                with_paren,
                nest(
                    ψ,
                    [
                        record.to_doc(ψ, true),
                        ψ.line(),
                        nest(
                            ψ,
                            [
                                ψ.text("<| "),
                                ψ.text(field.to_owned()),
                                ψ.text(" :="),
                                ψ.line(),
                                update.to_doc(ψ, false),
                                ψ.text(" |>"),
                            ],
                        ),
                    ],
                ),
            ),
            Self::List { exprs } => {
                list(ψ, exprs.iter().map(|expr| expr.to_doc(ψ, false)).collect())
            }
            Self::ModeWrapper { mode, expr } => ψ.concat([
                ψ.text(mode.to_owned()),
                ψ.text(":("),
                expr.to_doc(ψ, false),
                ψ.text(")"),
            ]),
            Self::Comment(comment, expr) => group(
                ψ,
                [
                    ψ.text(format!("(* {comment} *)")),
                    ψ.line(),
                    expr.to_doc(ψ, with_paren),
                ],
            ),
            Self::As(expr, ty) => paren(
                ψ,
                with_paren,
                nest(
                    ψ,
                    [
                        expr.to_doc(ψ, true),
                        ψ.text(" as"),
                        ψ.line(),
                        ty.to_doc(ψ, true),
                    ],
                ),
            ),
            Self::U128(u) => ψ.text(u.to_string()),
            Self::String(string) => ψ.text(format!("\"{string}\"")),
            Self::Message(string) => ψ.text(string.clone()),
            Self::Variable { ident, no_implicit } => ψ.concat([
                optional_insert(ψ, !*no_implicit, ψ.text("@")),
                ident.to_doc(ψ),
            ]),
            Self::Wild => ψ.text("_"),
        }
    }

    pub(crate) fn just_name(name: &str) -> Rc<Self> {
        Rc::new(Expression::Variable {
            ident: Path::new(&[name]),
            no_implicit: false,
        })
    }

    /// apply the expression as a function to one argument
    pub(crate) fn apply_arg(self: Rc<Self>, name: &Option<String>, arg: Rc<Self>) -> Rc<Self> {
        Rc::new(Expression::Application {
            func: self,
            args: vec![(name.clone(), arg.clone())],
        })
    }

    /// apply the expression as a function to one argument
    pub(crate) fn apply(self: Rc<Self>, arg: Rc<Self>) -> Rc<Self> {
        self.apply_arg(&None, arg)
    }

    /// apply the expression as a function to many arguments
    pub(crate) fn apply_many_args(self: Rc<Self>, args: &[(Option<String>, Rc<Self>)]) -> Rc<Self> {
        if args.is_empty() {
            return self.to_owned();
        }

        Rc::new(Expression::Application {
            func: self,
            args: args.to_vec(),
        })
    }

    /// apply the expression as a function to many arguments
    pub(crate) fn apply_many(self: Rc<Self>, args: &[Rc<Self>]) -> Rc<Self> {
        self.apply_many_args(
            &args
                .iter()
                .map(|arg| (None, arg.to_owned()))
                .collect::<Vec<_>>(),
        )
    }

    pub(crate) fn monadic_apply_empty(self: Rc<Self>) -> Rc<Self> {
        Rc::new(Expression::MonadicApplication {
            func: self,
            args: vec![],
        })
    }

    /// apply the expression as a function to one argument
    pub(crate) fn monadic_apply_arg(
        self: Rc<Self>,
        name: &Option<String>,
        arg: Rc<Self>,
    ) -> Rc<Self> {
        Rc::new(Expression::MonadicApplication {
            func: self,
            args: vec![(name.clone(), arg)],
        })
    }

    /// apply the expression as a function to one argument
    pub(crate) fn monadic_apply(self: Rc<Self>, arg: Rc<Self>) -> Rc<Self> {
        self.monadic_apply_arg(&None, arg)
    }

    /// apply the expression as a function to many arguments
    pub(crate) fn monadic_apply_many_args(
        self: Rc<Self>,
        args: &[(Option<String>, Rc<Self>)],
    ) -> Rc<Self> {
        if args.is_empty() {
            return self;
        }

        Rc::new(Expression::MonadicApplication {
            func: self,
            args: args.to_vec(),
        })
    }

    /// apply the expression as a function to many arguments
    pub(crate) fn monadic_apply_many(self: Rc<Self>, args: &[Rc<Self>]) -> Rc<Self> {
        self.monadic_apply_many_args(
            &args
                .iter()
                .map(|arg| (None, arg.to_owned()))
                .collect::<Vec<_>>(),
        )
    }

    pub(crate) fn monadic(self: Rc<Self>) -> Rc<Self> {
        Rc::new(Expression::ModeWrapper {
            mode: "ltac".to_string(),
            expr: Rc::new(Expression::Application {
                func: Expression::just_name("M.monadic"),
                args: vec![(None, self.to_owned())],
            }),
        })
    }

    #[allow(dead_code)]
    pub(crate) fn arrows_from(self: Rc<Self>, domains: &[Rc<Self>]) -> Rc<Self> {
        if domains.is_empty() {
            return self.to_owned();
        }

        Rc::new(Expression::FunctionType {
            domains: domains.to_owned(),
            image: self,
        })
    }

    #[allow(dead_code)]
    pub(crate) fn multiply(lhs: Rc<Self>, rhs: Rc<Self>) -> Rc<Self> {
        Rc::new(Expression::Product { lhs, rhs })
    }

    #[allow(dead_code)]
    pub(crate) fn multiply_many(exprs: &[Rc<Self>]) -> Rc<Self> {
        let product = exprs
            .iter()
            .map(|e| e.to_owned())
            .reduce(Expression::multiply);
        match product {
            Some(product) => product,
            None => Expression::just_name("unit"),
        }
    }

    /// A pattern for a name, taking into account names that are known
    /// constructors in Coq.
    pub(crate) fn name_pattern(name: &str) -> Rc<Self> {
        let known_constructors = ["I", "inl", "inr", "left", "None", "O", "right", "Some", "S"];

        if known_constructors.contains(&name) {
            Rc::new(Expression::As(
                Rc::new(Expression::Wild),
                Expression::just_name(name),
            ))
        } else {
            Expression::just_name(name)
        }
    }
}

impl Field {
    #[allow(dead_code)]
    pub(crate) fn new(name: &str, args: &[Rc<ArgDecl>], body: Rc<Expression>) -> Rc<Self> {
        Rc::new(Field {
            name: name.to_owned(),
            args: args.to_owned(),
            body,
        })
    }

    pub(crate) fn to_doc<'a, D>(&self, ψ: &'a D) -> DocBuilder<'a, D>
    where
        D: DocAllocator<'a>,
        D::Doc: Clone,
    {
        nest(
            ψ,
            [
                group(
                    ψ,
                    [
                        ψ.text(self.name.clone()),
                        optional_insert(
                            ψ,
                            self.args.is_empty(),
                            group(
                                ψ,
                                [
                                    ψ.line(),
                                    ψ.intersperse(
                                        self.args.iter().map(|param| param.to_doc(ψ)),
                                        ψ.line(),
                                    ),
                                ],
                            ),
                        ),
                    ],
                ),
                ψ.text(" :="),
                ψ.line(),
                self.body.to_doc(ψ, false),
                ψ.text(";"),
            ],
        )
    }
}

impl ArgDecl {
    pub(crate) fn is_empty(&self) -> bool {
        match self.decl.as_ref() {
            ArgDeclVar::Simple { idents, .. } => idents.is_empty(),
            ArgDeclVar::Generalized { .. } => false, // ty would always be exist
            ArgDeclVar::Destructured { .. } => false,
        }
    }

    /// produces a new coq argument
    pub(crate) fn new(decl: Rc<ArgDeclVar>, kind: ArgSpecKind) -> Rc<Self> {
        Rc::new(ArgDecl { decl, kind })
    }

    pub(crate) fn to_doc<'a, D>(&self, ψ: &'a D) -> DocBuilder<'a, D>
    where
        D: DocAllocator<'a>,
        D::Doc: Clone,
    {
        let brackets = match self.kind {
            ArgSpecKind::Explicit => round_brackets,
            ArgSpecKind::Implicit => curly_brackets,
        };
        match self.decl.as_ref() {
            ArgDeclVar::Simple { idents, ty } => {
                let arg_decl = nest(
                    ψ,
                    [
                        ψ.intersperse(idents.clone(), ψ.line()),
                        match &ty {
                            Some(ty) => {
                                ψ.concat([ψ.line(), ψ.text(":"), ψ.line(), ty.to_doc(ψ, false)])
                            }
                            None => ψ.nil(),
                        },
                    ],
                );
                if let (ArgSpecKind::Explicit, None) = (&self.kind, ty) {
                    arg_decl
                } else {
                    brackets(ψ, arg_decl)
                }
            }
            ArgDeclVar::Generalized { idents, ty } => group(
                ψ,
                [
                    ψ.text("`"),
                    brackets(
                        ψ,
                        nest(
                            ψ,
                            [
                                optional_insert(
                                    ψ,
                                    idents.is_empty(),
                                    ψ.concat([
                                        ψ.intersperse(idents.clone(), ψ.line()),
                                        ψ.line(),
                                        ψ.text(":"),
                                        ψ.line(),
                                    ]),
                                ),
                                ty.to_doc(ψ, false),
                            ],
                        ),
                    ),
                ],
            ),
            ArgDeclVar::Destructured { pattern } => {
                group(ψ, [ψ.text("'"), brackets(ψ, pattern.to_doc(ψ, false))])
            }
        }
    }

    pub(crate) fn of_const_ty_params(
        const_params: &[String],
        ty_params: &[String],
        kind: ArgSpecKind,
    ) -> Vec<Rc<Self>> {
        vec![
            Rc::new(ArgDecl {
                decl: Rc::new(ArgDeclVar::Simple {
                    idents: const_params.to_owned(),
                    ty: Some(Expression::just_name("Value.t")),
                }),
                kind: kind.clone(),
            }),
            Rc::new(ArgDecl {
                decl: Rc::new(ArgDeclVar::Simple {
                    idents: ty_params.to_owned(),
                    ty: Some(Expression::just_name("Ty.t")),
                }),
                kind,
            }),
        ]
    }
}
