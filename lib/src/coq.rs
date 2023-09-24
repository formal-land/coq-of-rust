use crate::path::Path;
use crate::render::{
    self, concat, group, hardline, intersperse, line, nest, nil, paren, text, Doc,
};

/// the
pub(crate) const LOCAL_STATE_TRAIT_INSTANCE: &str = "H'";

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
    Hint(Hint),
    Instance(Instance<'a>),
    Line,
    Module(Module<'a>),
    Record(Record<'a>),
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
    nb_repeat: usize,
    items: TopLevel<'a>,
}

#[derive(Clone)]
/// a coq section
pub(crate) struct Section<'a> {
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
/// a definition of a coq record
pub(crate) struct Record<'a> {
    name: String,
    ty: Expression<'a>,
    fields: Vec<FieldDef<'a>>,
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
    params: Vec<ArgDecl<'a>>,
    items: Vec<ClassFieldDef<'a>>,
}

#[derive(Clone)]
/// a global instance of a coq typeclass
pub(crate) struct Instance<'a> {
    refine_attribute: bool,
    name: String,
    parameters: Vec<ArgDecl<'a>>,
    class: Expression<'a>,
    bulid_expr: Expression<'a>,
    proof_lines: Vec<Doc<'a>>,
}

#[derive(Clone)]
/// a hint for auto
pub(crate) struct Hint {
    item_name: String,
    db_name: String,
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
/// a definition of a field in a record definition
pub(crate) struct FieldDef<'a> {
    ident: Option<String>,
    ty: Expression<'a>,
}

#[derive(Clone)]
/// a definition of a field in a typeclass definition
pub(crate) struct ClassFieldDef<'a> {
    ident: Option<String>,
    args: Vec<ArgDecl<'a>>,
    ty: Expression<'a>,
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
    Record {
        fields: Vec<Field<'a>>,
    },
    /// Set constant (the type of our types)
    Set,
    /// a dependent sum of types
    /// (like `Sigma (x : A), B(x)`, defined in CoqOfRust.lib.Notations)
    SigmaType {
        /// a list of arguments of `Sigma`
        args: Vec<ArgDecl<'a>>,
        /// the expression for the resulting type
        image: Box<Expression<'a>>,
    },
    /// a string
    String(String),
    /// Type constant
    Type,
    /// the unit type
    Unit,
    /// a single variable
    Variable {
        /// a list of names (a path) used to refer to the variable
        ident: Path,
        /// a flag, set if implicit arguments are deactivated with '@'
        no_implicit: bool,
    },
    /// a wildcard: '_'
    Wild,
}

/// a field of a record expression
#[derive(Clone)]
pub(crate) struct Field<'a> {
    name: Path,
    args: Vec<ArgDecl<'a>>,
    body: Expression<'a>,
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
    Generalized {
        /// a possibly empty vector of identifiers
        idents: Vec<String>,
        /// a type of the identifiers
        ty: Expression<'a>,
    },
    /// a destructured argument
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
        name: &str,
        ty_params: &[String],
        items: &TopLevel<'a>,
    ) -> Self {
        if ty_params.is_empty() {
            items.to_owned()
        } else {
            TopLevel::add_context_in_section(name, ty_params, items)
        }
    }

    /// creates a section with a context with type variables
    /// with the given variable names
    pub(crate) fn add_context_in_section(
        name: &str,
        ty_params: &[String],
        items: &TopLevel<'a>,
    ) -> Self {
        TopLevel {
            items: vec![TopLevelItem::Section(Section::new(
                name,
                &TopLevel {
                    items: [
                        vec![TopLevelItem::Context(Context::new(&[ArgDecl::new(
                            &ArgDeclVar::Simple {
                                idents: ty_params.iter().map(|arg| arg.to_owned()).collect(),
                                ty: Some(Expression::Set),
                            },
                            ArgSpecKind::Implicit,
                        )]))],
                        items.items.to_owned(),
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
            TopLevelItem::Hint(hint) => hint.to_doc(),
            TopLevelItem::Instance(instance) => instance.to_doc(),
            TopLevelItem::Line => nil(),
            TopLevelItem::Module(module) => module.to_doc(),
            TopLevelItem::Record(record) => record.to_doc(),
            TopLevelItem::Section(section) => section.to_doc(),
        }
    }

    /// creates a module with the translation of the given trait
    pub(crate) fn trait_module(
        name: &'a str,
        ty_params: &[(String, Option<Expression<'a>>)],
        predicates: &[ArgDecl<'a>],
        bounds: &[ArgDecl<'a>],
        items: &[ClassFieldDef<'a>],
        instances: &[Instance<'a>],
    ) -> Self {
        TopLevelItem::Module(Module::new(
            name,
            TopLevel::concat(&[
                TopLevel::locally_unset_primitive_projections_if(
                    items.is_empty(),
                    &[TopLevelItem::Class(Class::new(
                        "Trait",
                        &[
                            vec![ArgDecl::new(
                                &ArgDeclVar::Simple {
                                    idents: vec!["Self".to_string()],
                                    ty: Some(Expression::Set),
                                },
                                ArgSpecKind::Explicit,
                            )],
                            bounds.to_vec(),
                            if ty_params.is_empty() {
                                vec![]
                            } else {
                                vec![ArgDecl::new(
                                    &ArgDeclVar::Simple {
                                        idents: ty_params
                                            .iter()
                                            .map(|(ty, default)| {
                                                match default {
                                                    // @TODO: implement the translation of type parameters with default
                                                    Some(_default) => ["(* TODO *) ", ty].concat(),
                                                    None => ty.to_string(),
                                                }
                                            })
                                            .collect(),
                                        ty: Some(Expression::Set),
                                    },
                                    ArgSpecKind::Implicit,
                                )]
                            },
                            predicates.to_vec(),
                        ]
                        .concat(),
                        items.to_vec(),
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
    pub(crate) fn new(name: &str, items: TopLevel<'a>) -> Self {
        Module {
            name: name.to_string(),
            nb_repeat: 0,
            items,
        }
    }

    pub(crate) fn new_with_repeat(name: &str, nb_repeat: usize, items: TopLevel<'a>) -> Self {
        Module {
            name: name.to_string(),
            nb_repeat,
            items,
        }
    }

    pub(crate) fn to_doc(&self) -> Doc<'a> {
        let inner_module = render::enclose("Module", self.name.to_owned(), self.items.to_doc());
        if self.nb_repeat == 0 {
            inner_module
        } else {
            let wrap_name = format!("Wrap_{}_{}", self.name, self.nb_repeat);
            concat([
                render::enclose("Module", wrap_name.clone(), inner_module),
                hardline(),
                nest([text("Import"), line(), text(wrap_name), text(".")]),
            ])
        }
    }
}

impl<'a> Section<'a> {
    /// produces a new coq section
    pub(crate) fn new(name: &str, items: &TopLevel<'a>) -> Self {
        Section {
            name: name.to_string(),
            items: items.to_owned(),
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

impl<'a> Record<'a> {
    pub(crate) fn new(name: &str, ty: &Expression<'a>, fields: &[FieldDef<'a>]) -> Self {
        Record {
            name: name.to_owned(),
            ty: ty.to_owned(),
            fields: fields.to_owned(),
        }
    }

    pub(crate) fn to_doc(&self) -> Doc<'a> {
        group([
            nest([
                text("Record"),
                line(),
                text(self.name.to_owned()),
                line(),
                text(":"),
                line(),
                self.ty.to_doc(false),
                line(),
                text(":="),
                line(),
                text("{"),
            ]),
            if self.fields.is_empty() {
                text(" ")
            } else {
                concat([
                    nest([
                        hardline(),
                        intersperse(self.fields.iter().map(|field| field.to_doc()), [hardline()]),
                    ]),
                    hardline(),
                ])
            },
            text("}."),
        ])
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
    pub(crate) fn new(name: &str, params: &[ArgDecl<'a>], items: Vec<ClassFieldDef<'a>>) -> Self {
        Class {
            name: name.to_owned(),
            params: params.to_owned(),
            items,
        }
    }

    pub(crate) fn to_doc(&self) -> Doc<'a> {
        group([
            nest([
                nest([
                    text("Class "),
                    text(self.name.to_owned()),
                    if self.params.is_empty() {
                        nil()
                    } else {
                        group([
                            line(),
                            intersperse(self.params.iter().map(|param| param.to_doc()), [line()]),
                        ])
                    },
                    text(" :"),
                    line(),
                    Expression::Type.to_doc(false),
                    text(" := {"),
                ]),
                if self.items.is_empty() {
                    nil()
                } else {
                    hardline()
                },
                intersperse(
                    self.items
                        .iter()
                        .map(|item| item.to_doc())
                        .collect::<Vec<_>>(),
                    [hardline()],
                ),
            ]),
            hardline(),
            text("}."),
        ])
    }
}

impl<'a> Instance<'a> {
    /// produces a new coq instance
    pub(crate) fn new(
        refine_attribute: bool,
        name: &str,
        parameters: &[ArgDecl<'a>],
        class: Expression<'a>,
        bulid_expr: &Expression<'a>,
        proof_lines: Vec<Doc<'a>>,
    ) -> Self {
        Instance {
            refine_attribute,
            name: name.to_owned(),
            parameters: parameters.to_vec(),
            class,
            bulid_expr: bulid_expr.to_owned(),
            proof_lines,
        }
    }

    pub(crate) fn to_doc(&self) -> Doc<'a> {
        concat([
            if self.refine_attribute {
                concat([text("#[refine]"), hardline()])
            } else {
                nil()
            },
            nest([
                nest([
                    text("Global Instance"),
                    line(),
                    text(self.name.to_owned()),
                    if self.parameters.is_empty() {
                        nil()
                    } else {
                        concat([
                            line(),
                            intersperse(self.parameters.iter().map(|p| p.to_doc()), [line()]),
                        ])
                    },
                ]),
                line(),
                nest([text(": "), self.class.to_doc(false), line(), text(":= ")]),
            ]),
            self.bulid_expr.to_doc(false),
            text("."),
            if self.proof_lines.is_empty() {
                nil()
            } else {
                concat([
                    hardline(),
                    intersperse(self.proof_lines.to_owned(), [hardline()]),
                    hardline(),
                    text("Defined."),
                ])
            },
        ])
    }
}

impl Hint {
    pub(crate) fn new(item_name: &str, db_name: &str) -> Self {
        Hint {
            item_name: item_name.to_owned(),
            db_name: db_name.to_owned(),
        }
    }

    pub(crate) fn to_doc<'a>(&self) -> Doc<'a> {
        group([
            text("Global Hint Resolve"),
            line(),
            text(self.item_name.to_owned()),
            line(),
            text(":"),
            line(),
            text(self.db_name.to_owned()),
            text("."),
        ])
    }

    pub(crate) fn standard_resolve() -> Self {
        Hint::new("I", "core")
    }
}

impl<'a> FieldDef<'a> {
    pub(crate) fn new(ident: &Option<String>, ty: &Expression<'a>) -> Self {
        FieldDef {
            ident: ident.to_owned(),
            ty: ty.to_owned(),
        }
    }

    pub(crate) fn to_doc(&self) -> Doc<'a> {
        nest([
            match self.ident.to_owned() {
                Some(name) => text(name),
                None => text("_"),
            },
            line(),
            text(":"),
            line(),
            self.ty.to_doc(false),
            text(";"),
        ])
    }
}

impl<'a> ClassFieldDef<'a> {
    pub(crate) fn new(ident: &Option<String>, args: &[ArgDecl<'a>], ty: &Expression<'a>) -> Self {
        ClassFieldDef {
            ident: ident.to_owned(),
            args: args.to_owned(),
            ty: ty.to_owned(),
        }
    }

    pub(crate) fn to_doc(&self) -> Doc<'a> {
        nest([
            match self.ident.to_owned() {
                Some(name) => text(name),
                None => text("_"),
            },
            if self.args.is_empty() {
                nil()
            } else {
                group([
                    line(),
                    intersperse(self.args.iter().map(|param| param.to_doc()), [line()]),
                ])
            },
            line(),
            text(":"),
            line(),
            self.ty.to_doc(false),
            text(";"),
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
            Self::Record { fields } => concat([
                text("{"),
                if fields.is_empty() {
                    nil()
                } else {
                    nest([
                        hardline(),
                        intersperse(fields.iter().map(|field| field.to_doc()), [hardline()]),
                    ])
                },
                hardline(),
                text("}"),
            ]),
            Self::Set => text("Set"),
            Self::SigmaType { args, image } => paren(
                with_paren,
                concat([
                    nest([
                        text("Sigma"),
                        line(),
                        intersperse(args.iter().map(|arg| arg.to_doc()), [line()]),
                        text(","),
                    ]),
                    line(),
                    image.to_doc(false),
                ]),
            ),
            Self::String(string) => text(format!("\"{string}\"")),
            Self::Type => text("Type"),
            Self::Unit => text("unit"),
            Self::Variable { ident, no_implicit } => {
                concat([if *no_implicit { text("@") } else { nil() }, ident.to_doc()])
            }
            Self::Wild => text("_"),
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
            func: Box::new(self.clone()),
            args: vec![(name.clone(), arg.clone())],
        }
    }

    /// apply the expression as a function to one argument
    pub(crate) fn apply(&self, arg: &Self) -> Self {
        self.apply_arg(&None, arg)
    }

    /// apply the expression as a function to many arguments
    pub(crate) fn apply_many_args(&self, args: &[(Option<String>, Self)]) -> Self {
        Expression::Application {
            func: Box::new(self.to_owned()),
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

impl<'a> Field<'a> {
    pub(crate) fn new(name: &Path, args: &[ArgDecl<'a>], body: &Expression<'a>) -> Self {
        Field {
            name: name.to_owned(),
            args: args.to_owned(),
            body: body.to_owned(),
        }
    }

    pub(crate) fn to_doc(&self) -> Doc<'a> {
        nest([
            group([
                self.name.to_doc(),
                if self.args.is_empty() {
                    nil()
                } else {
                    group([
                        line(),
                        intersperse(self.args.iter().map(|param| param.to_doc()), [line()]),
                    ])
                },
            ]),
            line(),
            text(":="),
            line(),
            self.body.to_doc(false),
            text(";"),
        ])
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
                idents: vec![LOCAL_STATE_TRAIT_INSTANCE.to_string()],
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
            ArgDeclVar::Simple { idents, ty } => brackets(nest([
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
            ArgDeclVar::Destructured { pattern } => {
                group([text("'"), brackets(pattern.to_doc(false))])
            }
        }
    }

    pub(crate) fn of_ty_params(ty_params: &[String], kind: ArgSpecKind) -> Self {
        ArgDecl {
            decl: ArgDeclVar::Simple {
                idents: ty_params.to_owned(),
                ty: Some(Expression::Set),
            },
            kind,
        }
    }

    pub(crate) fn add_var(&self, ident: &str) -> Self {
        ArgDecl {
            decl: match &self.decl {
                ArgDeclVar::Simple { idents, ty } => ArgDeclVar::Simple {
                    idents: [idents.to_owned(), vec![ident.to_owned()]].concat(),
                    ty: ty.to_owned(),
                },
                ArgDeclVar::Generalized { idents, ty } => ArgDeclVar::Generalized {
                    idents: [idents.to_owned(), vec![ident.to_owned()]].concat(),
                    ty: ty.to_owned(),
                },
                ArgDeclVar::Destructured { pattern: _ } => self.decl.to_owned(),
            },
            kind: self.kind.to_owned(),
        }
    }
}
