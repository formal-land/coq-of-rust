use rpds::HashTrieMap;

use crate::path::Path;
use crate::render::{
    self, concat, curly_brackets, group, hardline, intersperse, line, list, nest, nil,
    optional_insert, optional_insert_with, paren, text, Doc,
};
use std::rc::Rc;

#[derive(Clone)]
/// a list of coq top level items
pub(crate) struct TopLevel<'a> {
    pub(crate) items: Vec<TopLevelItem<'a>>,
}

#[derive(Clone)]
/// any coq top level item
pub(crate) enum TopLevelItem<'a> {
    /// the Code variant is for those constructions
    /// that are not yet represented by the types in this file
    Code(Doc<'a>),
    Comment(Expression<'a>),
    Definition(Definition<'a>),
    Line,
    Module(Module<'a>),
}

#[derive(Clone)]
/// a coq module
pub(crate) struct Module<'a> {
    name: String,
    items: TopLevel<'a>,
}

#[derive(Clone)]
/// a coq constant definition
pub(crate) struct Definition<'a> {
    name: String,
    kind: DefinitionKind<'a>,
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
    /// an axiom
    /// (using `Axiom`)
    Axiom { ty: Expression<'a> },
    /// a definition with an `exact` tactic
    #[allow(dead_code)]
    Ltac {
        args: Vec<String>,
        body: Expression<'a>,
    },
}

#[derive(Clone)]
/// a coq expression
/// (suitable also for coq type expressions,
///     because in coq types are like any other values)
pub(crate) enum Expression<'a> {
    /// the Code variant is for those constructions
    /// that are not yet represented by the types in this file
    Code(Doc<'a>),
    /// an (curried) application of a function to some arguments
    Application {
        /// the function that is applied
        func: Rc<Expression<'a>>,
        /// a nonempty list of arguments
        /// (we accept many arguments to control their indentation better,
        ///     the application is curried when it gets printed)
        args: Vec<(Option<String>, Expression<'a>)>,
    },
    /// a (curried) function
    Function {
        parameters: Vec<Expression<'a>>,
        body: Rc<Expression<'a>>,
    },
    Let {
        name: String,
        ty: Option<Rc<Expression<'a>>>,
        value: Rc<Expression<'a>>,
        body: Rc<Expression<'a>>,
    },
    Match {
        scrutinees: Vec<Expression<'a>>,
        arms: Vec<(Vec<Expression<'a>>, Expression<'a>)>,
    },
    /// a (curried) function type
    FunctionType {
        /// a nonempty list of domains
        /// (we accept many domains to control their indentation in the type better,
        ///     the type is curried when it gets printed)
        domains: Vec<Expression<'a>>,
        /// the image (range, co-domain) of functions of the type
        image: Rc<Expression<'a>>,
    },
    /// a dependent product of types
    /// (like `forall (x : A), B(x)`)
    PiType {
        /// a list of arguments of `forall`
        args: Vec<ArgDecl<'a>>,
        /// the expression for the resulting type
        image: Rc<Expression<'a>>,
    },
    /// The equality of two expressions `lhs = rhs`
    Equality {
        lhs: Rc<Expression<'a>>,
        rhs: Rc<Expression<'a>>,
    },
    /// a product of two variables (they can be types or numbers)
    #[allow(dead_code)]
    Product {
        /// left hand side
        lhs: Rc<Expression<'a>>,
        /// right hand side
        rhs: Rc<Expression<'a>>,
    },
    /// A tuple of expressions `(e1, e2, ...)`
    Tuple(Vec<Expression<'a>>),
    Record {
        fields: Vec<Field<'a>>,
    },
    #[allow(dead_code)]
    RecordField {
        record: Rc<Expression<'a>>,
        field: String,
    },
    #[allow(dead_code)]
    RecordUpdate {
        record: Rc<Expression<'a>>,
        field: String,
        update: Rc<Expression<'a>>,
    },
    List {
        exprs: Vec<Expression<'a>>,
    },
    /// For example ltac:(...) or constr:(...)
    /// #[allow(dead_code)]
    #[allow(dead_code)]
    ModeWrapper {
        mode: String,
        expr: Rc<Expression<'a>>,
    },
    /// Comment next to an expression
    Comment(String, Rc<Expression<'a>>),
    /// `as` expression in patterns
    As(Rc<Expression<'a>>, Rc<Expression<'a>>),
    /// An integer
    U128(u128),
    /// a string in quotes
    String(String),
    /// a plain string in the code
    Message(String),
    /// a single variable
    Variable {
        /// a list of names (a path) used to refer to the variable
        ident: Path,
        /// a flag, set if implicit arguments are deactivated with '@'
        no_implicit: bool,
    },
    Paren {
        // An extra parameter for more recursive managements?
        // with_paren: bool,
        expr: Rc<Expression<'a>>,
    },
    /// a wildcard: '_'
    Wild,
}

/// a field of a record expression
#[derive(Clone)]
pub(crate) struct Field<'a> {
    pub(crate) name: String,
    pub(crate) args: Vec<ArgDecl<'a>>,
    pub(crate) body: Expression<'a>,
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
    Simple {
        // @TODO: try to make it really non-empty
        /// a non-empty vector of identifiers
        idents: Vec<String>,
        /// a type of the identifiers
        ty: Option<Expression<'a>>,
    },
    /// a generalized declaration (preceded by `` ` ``)
    #[allow(dead_code)]
    Generalized {
        /// a possibly empty vector of identifiers
        idents: Vec<String>,
        /// a type of the identifiers
        ty: Expression<'a>,
    },
    /// a destructured argument
    #[allow(dead_code)]
    Destructured { pattern: Expression<'a> },
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

impl<'a> TopLevel<'a> {
    /// produces a new list of coq items
    pub(crate) fn new(items: &[TopLevelItem<'a>]) -> Self {
        TopLevel {
            items: items.to_vec(),
        }
    }

    pub(crate) fn to_doc(&self) -> Doc<'a> {
        self.items
            .iter()
            .enumerate()
            .fold(
                (HashTrieMap::new(), nil()),
                |(previous_module_names, doc), (index, item)| {
                    let doc = concat([
                        doc,
                        if index != 0 { hardline() } else { nil() },
                        item.to_doc(previous_module_names.clone()),
                    ]);
                    let previous_module_names = match item {
                        TopLevelItem::Module(Module { name, items }) if !items.items.is_empty() => {
                            previous_module_names.insert(
                                name.clone(),
                                *previous_module_names.get(name).unwrap_or(&0) + 1,
                            )
                        }
                        _ => previous_module_names,
                    };

                    (previous_module_names, doc)
                },
            )
            .1
    }

    /// joins a list of lists of items into one list
    pub(crate) fn concat(tls: &[Self]) -> Self {
        TopLevel {
            items: tls.iter().flat_map(|tl| tl.items.to_owned()).collect(),
        }
    }
}

impl<'a> TopLevelItem<'a> {
    pub(crate) fn to_doc(&self, previous_module_names: HashTrieMap<String, u64>) -> Doc<'a> {
        match self {
            TopLevelItem::Code(code) => code.to_owned(),
            TopLevelItem::Comment(expression) => {
                concat([text("(* "), expression.to_doc(false), text(" *)")])
            }
            TopLevelItem::Definition(definition) => definition.to_doc(),
            TopLevelItem::Line => nil(),
            TopLevelItem::Module(module) => module.to_doc(previous_module_names),
        }
    }
}

impl<'a> Module<'a> {
    /// produces a new coq module
    pub(crate) fn new(name: &str, items: TopLevel<'a>) -> Self {
        Module {
            name: name.to_string(),
            items,
        }
    }

    pub(crate) fn to_doc(&self, previous_module_names: HashTrieMap<String, u64>) -> Doc<'a> {
        if self.items.items.is_empty() {
            return text(format!("(* Empty module '{}' *)", self.name));
        }

        let items = self.items.to_doc();
        let inner_module = render::enclose("Module", self.name.to_owned(), true, items);
        let nb_repeat = *previous_module_names.get(&self.name).unwrap_or(&0);

        if nb_repeat == 0 {
            inner_module
        } else {
            let wrap_name = format!("Wrap_{}_{}", self.name, nb_repeat + 1);

            concat([
                render::enclose("Module", wrap_name.clone(), false, inner_module),
                hardline(),
                nest([text("Import"), line(), text(wrap_name), text(".")]),
            ])
        }
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
                        concat(args.iter().filter_map(|arg| {
                            if arg.is_empty() {
                                None
                            } else {
                                Some(concat([line(), arg.to_doc()]))
                            }
                        })),
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
            DefinitionKind::Axiom { ty } => nest([
                nest([
                    text("Axiom"),
                    line(),
                    text(self.name.to_owned()),
                    text(" :"),
                ]),
                line(),
                ty.to_doc(false),
                text("."),
            ]),
            DefinitionKind::Ltac { args, body } => nest([
                nest([
                    nest([text("Ltac"), line(), text(self.name.to_owned())]),
                    concat(args.iter().map(|arg| concat([line(), text(arg.clone())]))),
                    text(" :="),
                ]),
                line(),
                nest([text("exact"), line(), body.to_doc(true)]),
                text("."),
            ]),
        }
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
                    optional_insert(args.is_empty(), line()),
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
            Self::Function { parameters, body } => {
                if parameters.is_empty() {
                    body.to_doc(with_paren)
                } else {
                    paren(
                        with_paren,
                        nest([
                            nest([
                                text("fun"),
                                concat(
                                    parameters
                                        .iter()
                                        .map(|parameter| concat([line(), parameter.to_doc(true)])),
                                ),
                                text(" =>"),
                            ]),
                            line(),
                            body.to_doc(false),
                        ]),
                    )
                }
            }
            Self::Let {
                name,
                ty,
                value,
                body,
            } => paren(
                with_paren,
                group([
                    nest([
                        nest([
                            nest([text("let"), line(), text(name.to_owned())]),
                            match ty {
                                None => nil(),
                                Some(ty) => concat([text(" :"), line(), ty.to_doc(false)]),
                            },
                            text(" :="),
                        ]),
                        line(),
                        value.to_doc(false),
                        text(" in"),
                    ]),
                    line(),
                    body.to_doc(false),
                ]),
            ),
            Self::Match { scrutinees, arms } => group([
                group([
                    nest([
                        text("match"),
                        line(),
                        intersperse(
                            scrutinees.iter().map(|scrutinee| scrutinee.to_doc(false)),
                            [text(","), line()],
                        ),
                    ]),
                    line(),
                    text("with"),
                ]),
                concat(arms.iter().map(|(patterns, body)| {
                    concat([
                        line(),
                        nest([
                            nest([
                                text("| "),
                                intersperse(
                                    patterns.iter().map(|pattern| pattern.to_doc(false)),
                                    [text(","), line()],
                                ),
                                text(" =>"),
                            ]),
                            line(),
                            body.to_doc(false),
                        ]),
                    ])
                })),
                line(),
                text("end"),
            ]),
            Self::FunctionType { domains, image } => paren(
                with_paren,
                nest([
                    intersperse(
                        domains
                            .iter()
                            .map(|domain| group([domain.to_doc(true), line(), text("->")])),
                        [line()],
                    ),
                    optional_insert(domains.is_empty(), line()),
                    image.to_doc(false),
                ]),
            ),
            Self::PiType { args, image } => optional_insert_with(
                args.iter().all(|arg| arg.is_empty()),
                image.to_doc(with_paren),
                paren(
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
            ),
            Self::Equality { lhs, rhs } => paren(
                with_paren,
                nest([lhs.to_doc(true), text(" ="), line(), rhs.to_doc(true)]),
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
            Self::Tuple(es) => nest([
                text("("),
                intersperse(es.iter().map(|e| e.to_doc(false)), [text(","), line()]),
                text(")"),
            ]),
            Self::Record { fields } => concat([curly_brackets(concat([
                optional_insert(
                    fields.is_empty(),
                    nest([
                        hardline(),
                        intersperse(fields.iter().map(|field| field.to_doc()), [hardline()]),
                    ]),
                ),
                hardline(),
            ]))]),
            Self::RecordField { record, field } => concat([
                record.to_doc(true),
                text(".("),
                text(field.to_owned()),
                text(")"),
            ]),
            Self::RecordUpdate {
                record,
                field,
                update,
            } => paren(
                with_paren,
                nest([
                    record.to_doc(true),
                    line(),
                    nest([
                        text("<| "),
                        text(field.to_owned()),
                        text(" :="),
                        line(),
                        update.to_doc(false),
                        text(" |>"),
                    ]),
                ]),
            ),
            Self::List { exprs } => list(exprs.iter().map(|expr| expr.to_doc(false)).collect()),
            Self::ModeWrapper { mode, expr } => concat([
                text(mode.to_owned()),
                text(":("),
                expr.to_doc(false),
                text(")"),
            ]),
            Self::Comment(comment, expr) => nest([
                text(format!("(* {comment} *)")),
                line(),
                expr.to_doc(with_paren),
            ]),
            Self::As(expr, ty) => paren(
                with_paren,
                nest([expr.to_doc(true), text(" as"), line(), ty.to_doc(true)]),
            ),
            Self::U128(u) => text(u.to_string()),
            Self::String(string) => text(format!("\"{string}\"")),
            Self::Message(string) => text(string.clone()),
            Self::Variable { ident, no_implicit } => {
                concat([optional_insert(!*no_implicit, text("@")), ident.to_doc()])
            }
            Self::Wild => text("_"),
            Self::Paren { expr } => paren(true, expr.to_doc(with_paren)),
        }
    }

    pub(crate) fn just_name(name: &str) -> Self {
        Expression::Variable {
            ident: Path::new(&[name]),
            no_implicit: false,
        }
    }

    /// apply the expression as a function to one argument
    pub(crate) fn apply_arg(&self, name: &Option<String>, arg: &Self) -> Self {
        Expression::Application {
            func: Rc::new(self.clone()),
            args: vec![(name.clone(), arg.clone())],
        }
    }

    /// apply the expression as a function to one argument
    pub(crate) fn apply(&self, arg: &Self) -> Self {
        self.apply_arg(&None, arg)
    }

    /// apply the expression as a function to many arguments
    pub(crate) fn apply_many_args(&self, args: &[(Option<String>, Self)]) -> Self {
        if args.is_empty() {
            return self.to_owned();
        }

        Expression::Application {
            func: Rc::new(self.to_owned()),
            args: args.to_vec(),
        }
    }

    /// apply the expression as a function to many arguments
    pub(crate) fn apply_many(&self, args: &[Self]) -> Self {
        self.apply_many_args(
            &args
                .iter()
                .map(|arg| (None, arg.to_owned()))
                .collect::<Vec<_>>(),
        )
    }

    #[allow(dead_code)]
    pub(crate) fn arrows_from(&self, domains: &[Self]) -> Self {
        if domains.is_empty() {
            return self.to_owned();
        }

        Expression::FunctionType {
            domains: domains.to_owned(),
            image: Rc::new(self.to_owned()),
        }
    }

    #[allow(dead_code)]
    pub(crate) fn multiply(lhs: Self, rhs: Self) -> Self {
        Expression::Product {
            lhs: Rc::new(lhs),
            rhs: Rc::new(rhs),
        }
    }

    #[allow(dead_code)]
    pub(crate) fn multiply_many(exprs: &[Self]) -> Self {
        let product = exprs
            .iter()
            .map(|e| e.to_owned())
            .reduce(Expression::multiply);
        match product {
            Some(product) => product,
            None => Expression::just_name("unit"),
        }
    }

    pub(crate) fn of_option<'b, A>(expr: &'b Option<A>, to_coq: fn(&'b A) -> Self) -> Self {
        match expr {
            None => Expression::just_name("None"),
            Some(expr) => Expression::just_name("Some").apply(&to_coq(expr)),
        }
    }

    /// A pattern for a name, taking into account names that are known
    /// constructors in Coq.
    pub(crate) fn name_pattern(name: &str) -> Self {
        let known_constructors = ["I", "inl", "inr", "left", "None", "O", "right", "Some", "S"];

        if known_constructors.contains(&name) {
            Expression::As(
                Rc::new(Expression::Wild),
                Rc::new(Expression::just_name(name)),
            )
        } else {
            Expression::just_name(name)
        }
    }

    pub(crate) fn paren(with_paren: bool, expr: &Self) -> Self {
        if with_paren {
            Self::Paren {
                expr: Rc::new(expr.to_owned()),
            }
        } else {
            expr.to_owned()
        }
    }
}

impl<'a> Field<'a> {
    #[allow(dead_code)]
    pub(crate) fn new(name: &str, args: &[ArgDecl<'a>], body: &Expression<'a>) -> Self {
        Field {
            name: name.to_owned(),
            args: args.to_owned(),
            body: body.to_owned(),
        }
    }

    pub(crate) fn to_doc(&self) -> Doc<'a> {
        nest([
            group([
                text(self.name.clone()),
                optional_insert(
                    self.args.is_empty(),
                    group([
                        line(),
                        intersperse(self.args.iter().map(|param| param.to_doc()), [line()]),
                    ]),
                ),
            ]),
            text(" :="),
            line(),
            self.body.to_doc(false),
            text(";"),
        ])
    }
}

impl<'a> ArgDecl<'a> {
    pub(crate) fn is_empty(&self) -> bool {
        match self.decl.to_owned() {
            ArgDeclVar::Simple { idents, .. } => idents.is_empty(),
            ArgDeclVar::Generalized { .. } => false, // ty would always be exist
            ArgDeclVar::Destructured { .. } => false,
        }
    }

    /// produces a new coq argument
    pub(crate) fn new(decl: &ArgDeclVar<'a>, kind: ArgSpecKind) -> Self {
        ArgDecl {
            decl: decl.to_owned(),
            kind,
        }
    }

    pub(crate) fn to_doc(&self) -> Doc<'a> {
        let brackets = match self.kind {
            ArgSpecKind::Explicit => render::round_brackets,
            ArgSpecKind::Implicit => render::curly_brackets,
        };
        match self.decl.to_owned() {
            ArgDeclVar::Simple { idents, ty } => {
                let arg_decl = nest([
                    intersperse(idents, [line()]),
                    match &ty {
                        Some(ty) => concat([line(), text(":"), line(), ty.to_doc(false)]),
                        None => nil(),
                    },
                ]);
                if let (ArgSpecKind::Explicit, None) = (&self.kind, ty) {
                    arg_decl
                } else {
                    brackets(arg_decl)
                }
            }
            ArgDeclVar::Generalized { idents, ty } => group([
                text("`"),
                brackets(nest([
                    optional_insert(
                        idents.is_empty(),
                        concat([intersperse(idents, [line()]), line(), text(":"), line()]),
                    ),
                    ty.to_doc(false),
                ])),
            ]),
            ArgDeclVar::Destructured { pattern } => {
                group([text("'"), brackets(pattern.to_doc(false))])
            }
        }
    }

    pub(crate) fn of_ty_params(ty_params: &[String], kind: ArgSpecKind) -> Self {
        ArgDecl {
            decl: ArgDeclVar::Simple {
                idents: ty_params.to_owned(),
                ty: Some(Expression::just_name("Ty.t")),
            },
            kind,
        }
    }
}
