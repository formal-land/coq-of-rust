use crate::path::Path;
use crate::render::{
    self, concat, curly_brackets, group, hardline, intersperse, line, nest, nil, optional_insert,
    optional_insert_vec, optional_insert_with, paren, text, Doc,
};
use crate::top_level::VariantItem;
use std::marker::PhantomData;
use std::rc::Rc;

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
    Record(Record<'a>),
    Inductive(Inductive<'a>),
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
    is_with_section: bool,
    /// To prevent a collision, in case a module with the same name is already
    /// declared. In this case, we do the appropriate `Import` to complete the
    /// previous module.
    nb_repeat: usize,
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
    fields: Vec<RecordFieldDef<'a>>,
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
    args: Vec<ArgDecl<'a>>,
    items: Vec<ClassFieldDef<'a>>,
}

#[derive(Clone)]
/// a global instance of a coq typeclass
pub(crate) struct Instance<'a> {
    name: String,
    parameters: Vec<ArgDecl<'a>>,
    class: Expression<'a>,
    build_expr: Expression<'a>,
    proof_lines: Vec<Doc<'a>>,
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
    /// a definition with an `exact` tactic
    Ltac {
        args: Vec<String>,
        body: Expression<'a>,
    },
}

#[derive(Clone)]
/// a definition of a field in a record definition
pub(crate) struct RecordFieldDef<'a> {
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
pub(crate) struct IndFieldDef<'a> {
    name: String,
    item: Rc<VariantItem>,
    _phantom_data: std::marker::PhantomData<&'a ()>,
}

#[derive(Clone)]
pub(crate) struct Inductive<'a> {
    name: String,
    ty_params: Vec<String>,
    fields: Vec<IndFieldDef<'a>>,
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
    Match {
        scrutinee: Rc<Expression<'a>>,
        arms: Vec<(Expression<'a>, Expression<'a>)>,
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
    /// a product of two variables (they can be types or numbers)
    Product {
        /// left hand side
        lhs: Rc<Expression<'a>>,
        /// right hand side
        rhs: Rc<Expression<'a>>,
    },
    Record {
        fields: Vec<Field<'a>>,
    },
    RecordField {
        record: Rc<Expression<'a>>,
        field: String,
    },
    RecordUpdate {
        record: Rc<Expression<'a>>,
        field: String,
        update: Rc<Expression<'a>>,
    },
    List {
        exprs: Vec<Expression<'a>>,
    },
    /// For example ltac:(...) or constr:(...)
    ModeWrapper {
        mode: String,
        expr: Rc<Expression<'a>>,
    },
    /// Set constant (the type of our types)
    Set,
    /// a dependent sum of types
    /// (like `Sigma (x : A), B(x)`, defined in CoqOfRust.lib.Notations)
    SigmaType {
        /// a list of arguments of `Sigma`
        args: Vec<ArgDecl<'a>>,
        /// the expression for the resulting type
        image: Rc<Expression<'a>>,
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

    pub(crate) fn new_vec(items: Vec<TopLevelItem<'a>>) -> Self {
        TopLevel { items }
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

    /// creates the context in a section with type variables
    /// with the given variable names
    pub(crate) fn add_context_in_section(
        ty_params: &[String],
        are_ty_params_explicit: bool,
        items: &TopLevel<'a>,
    ) -> Self {
        TopLevel {
            items: [
                // [ty_params]
                optional_insert_vec(
                    ty_params.is_empty(),
                    vec![
                        TopLevelItem::Context(Context::new(&[ArgDecl::new(
                            &ArgDeclVar::Simple {
                                idents: ty_params.iter().map(|arg| arg.to_owned()).collect(),
                                ty: Some(Expression::Set),
                            },
                            if are_ty_params_explicit {
                                ArgSpecKind::Explicit
                            } else {
                                ArgSpecKind::Implicit
                            },
                        )])),
                        TopLevelItem::Line,
                    ],
                ),
                items.items.to_owned(),
            ]
            .concat(),
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
            TopLevelItem::Record(record) => record.to_doc(),
            TopLevelItem::Inductive(inductive) => inductive.to_doc(),
        }
    }

    /// creates a module with the translation of the given trait
    pub(crate) fn trait_module(
        name: &'a str,
        ty_params: &[(String, Option<Expression<'a>>)],
        items: &[ClassFieldDef<'a>],
        instances: &[Instance<'a>],
    ) -> Self {
        TopLevelItem::Module(Module::new(
            name,
            true,
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
                            optional_insert_vec(
                                ty_params.is_empty(),
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
                                )],
                            ),
                        ]
                        .concat(),
                        items.to_vec(),
                    ))],
                ),
                TopLevel {
                    items: instances
                        .iter()
                        .map(|instance| TopLevelItem::Instance(instance.to_owned()))
                        .collect(),
                },
            ]),
        ))
    }

    pub(crate) fn ty_alias_definition(
        name: &str,
        ty_params: Vec<String>,
        ty: &Expression<'a>,
    ) -> Vec<Self> {
        vec![TopLevelItem::Definition(Definition::new(
            name,
            &DefinitionKind::Ltac {
                args: ty_params,
                body: ty.clone(),
            },
        ))]
    }
}

impl<'a> Module<'a> {
    /// produces a new coq module
    pub(crate) fn new(name: &str, is_with_section: bool, items: TopLevel<'a>) -> Self {
        Module {
            name: name.to_string(),
            is_with_section,
            nb_repeat: 0,
            items,
        }
    }

    pub(crate) fn new_with_repeat(
        name: &str,
        is_with_section: bool,
        nb_repeat: usize,
        items: TopLevel<'a>,
    ) -> Self {
        Module {
            name: name.to_string(),
            is_with_section,
            nb_repeat,
            items,
        }
    }

    pub(crate) fn to_doc(&self) -> Doc<'a> {
        let items = self.items.to_doc();
        let items = if self.is_with_section {
            render::enclose("Section", self.name.to_owned(), true, items)
        } else {
            items
        };
        let inner_module = render::enclose(
            if self.is_with_section {
                // We add one space at the end for alignment with the section's name
                "Module "
            } else {
                "Module"
            },
            self.name.to_owned(),
            !self.is_with_section,
            items,
        );
        if self.nb_repeat == 0 {
            inner_module
        } else {
            let wrap_name = format!("Wrap_{}_{}", self.name, self.nb_repeat);
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
                        optional_insert(
                            args.is_empty(),
                            concat([
                                line(),
                                intersperse(args.iter().map(|arg| arg.to_doc()), [line()]),
                            ]),
                        ),
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

impl<'a> Record<'a> {
    pub(crate) fn new(name: &str, ty: &Expression<'a>, fields: &[RecordFieldDef<'a>]) -> Self {
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
                text(" :"),
                line(),
                self.ty.to_doc(false),
                text(" :="),
                line(),
                text("{"),
            ]),
            optional_insert_with(
                self.fields.is_empty(),
                text(" "),
                concat([
                    nest([
                        hardline(),
                        intersperse(self.fields.iter().map(|field| field.to_doc()), [hardline()]),
                    ]),
                    hardline(),
                ]),
            ),
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
    pub(crate) fn new(name: &str, args: &[ArgDecl<'a>], items: Vec<ClassFieldDef<'a>>) -> Self {
        Class {
            name: name.to_owned(),
            args: args.to_owned(),
            items,
        }
    }

    pub(crate) fn to_doc(&self) -> Doc<'a> {
        group([
            nest([
                nest([
                    text("Class "),
                    text(self.name.to_owned()),
                    optional_insert(
                        self.args.is_empty(),
                        group([
                            line(),
                            intersperse(self.args.iter().map(|param| param.to_doc()), [line()]),
                        ]),
                    ),
                    text(" :"),
                    line(),
                    Expression::Type.to_doc(false),
                    text(" := {"),
                ]),
                optional_insert(self.items.is_empty(), hardline()),
                intersperse(
                    {
                        let mut anonymous_item_counter = 0;
                        self.items
                            .iter()
                            .map(|item| {
                                let result = item.to_doc(anonymous_item_counter);
                                if let ClassFieldDef { ident: None, .. } = item {
                                    anonymous_item_counter += 1;
                                }
                                result
                            })
                            .collect::<Vec<_>>()
                    },
                    [hardline()],
                ),
            ]),
            hardline(),
            text("}."),
        ])
    }
}

impl<'a> IndFieldDef<'a> {
    pub(crate) fn new(name: &String, item: Rc<VariantItem>) -> Self {
        IndFieldDef {
            name: name.to_owned(),
            item,
            _phantom_data: PhantomData,
        }
    }

    pub(crate) fn field_to_doc(&self) -> Doc<'a> {
        nest([
            text("|"),
            line(),
            text(self.name.to_owned()),
            match &*self.item {
                VariantItem::Struct { .. } => concat([
                    line(),
                    nest([
                        text("(_ :"),
                        line(),
                        text(format!("{}.t", self.name.to_owned())),
                        text(")"),
                    ]),
                ]),
                VariantItem::Tuple { tys } => concat(tys.iter().map(|ty| {
                    concat([
                        line(),
                        nest([text("(_ :"), line(), ty.to_coq().to_doc(false), text(")")]),
                    ])
                })),
            },
        ])
    }
}

impl<'a> Inductive<'a> {
    pub(crate) fn new(
        name: &String,
        ty_params: &Vec<String>,
        fields: Vec<IndFieldDef<'a>>,
    ) -> Self {
        Inductive {
            name: name.to_owned(),
            ty_params: ty_params.to_owned(),
            fields: fields.to_owned(),
        }
    }

    pub(crate) fn to_doc(&self) -> Doc<'a> {
        concat([
            nest([
                text("Inductive"),
                line(),
                text(self.name.to_owned()),
                concat(self.ty_params.iter().map(|ty_param| {
                    concat([
                        line(),
                        nest([
                            text("("),
                            text(ty_param.to_owned()),
                            text(" :"),
                            line(),
                            text("Set)"),
                        ]),
                    ])
                })),
                text(" :"),
                line(),
                text("Set :="),
            ]),
            hardline(),
            intersperse(self.fields.iter().map(|item| item.field_to_doc()), [line()]),
            text("."),
        ])
    }
}

impl<'a> Instance<'a> {
    /// produces a new coq instance
    pub(crate) fn new(
        name: &str,
        parameters: &[ArgDecl<'a>],
        class: Expression<'a>,
        build_expr: &Expression<'a>,
        proof_lines: Vec<Doc<'a>>,
    ) -> Self {
        Instance {
            name: name.to_owned(),
            parameters: parameters.to_vec(),
            class,
            build_expr: build_expr.to_owned(),
            proof_lines,
        }
    }

    pub(crate) fn to_doc(&self) -> Doc<'a> {
        concat([
            nest([
                nest([
                    text("Global Instance "),
                    text(self.name.to_owned()),
                    optional_insert(self.parameters.is_empty(), {
                        let non_empty_params: Vec<_> =
                            self.parameters.iter().filter(|p| !p.is_empty()).collect();
                        optional_insert(
                            non_empty_params.is_empty(),
                            concat([
                                line(),
                                intersperse(non_empty_params.iter().map(|p| p.to_doc()), [line()]),
                            ]),
                        )
                    }),
                ]),
                text(" :"),
                line(),
                self.class.to_doc(false),
                text(" := "),
            ]),
            self.build_expr.to_doc(false),
            text("."),
            optional_insert(
                self.proof_lines.is_empty(),
                concat([
                    hardline(),
                    intersperse(self.proof_lines.to_owned(), [hardline()]),
                    hardline(),
                    text("Defined."),
                ]),
            ),
        ])
    }
}

impl<'a> RecordFieldDef<'a> {
    pub(crate) fn new(ident: &Option<String>, ty: &Expression<'a>) -> Self {
        RecordFieldDef {
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
            text(" :"),
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

    pub(crate) fn to_doc(&self, anonymous_counter: usize) -> Doc<'a> {
        nest([
            match self.ident.to_owned() {
                Some(name) => text(name),
                None => text(format!("ℒ_{anonymous_counter}")),
            },
            optional_insert(
                self.args.is_empty(),
                group([
                    line(),
                    intersperse(self.args.iter().map(|param| param.to_doc()), [line()]),
                ]),
            ),
            match self.ident {
                Some(_) => text(" :"),
                None => text(" ::"),
            },
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
            Self::Function { parameters, body } => paren(
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
            ),
            Self::Match { scrutinee, arms } => group([
                group([
                    nest([text("match"), line(), scrutinee.to_doc(false)]),
                    line(),
                    text("with"),
                ]),
                concat(arms.iter().map(|(pattern, body)| {
                    concat([
                        line(),
                        nest([
                            text("| "),
                            pattern.to_doc(false),
                            text(" =>"),
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
                args.is_empty(),
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
            Self::List { exprs } => nest([
                text("["),
                intersperse(
                    exprs.iter().map(|expr| expr.to_doc(false)),
                    [text(";"), line()],
                ),
                text("]"),
            ]),
            Self::ModeWrapper { mode, expr } => concat([
                text(mode.to_owned()),
                text(":("),
                expr.to_doc(false),
                text(")"),
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
                concat([optional_insert(!*no_implicit, text("@")), ident.to_doc()])
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

    pub(crate) fn arrows_from(&self, domains: &[Self]) -> Self {
        if domains.is_empty() {
            return self.to_owned();
        }

        Expression::FunctionType {
            domains: domains.to_owned(),
            image: Rc::new(self.to_owned()),
        }
    }

    pub(crate) fn multiply(lhs: Self, rhs: Self) -> Self {
        Expression::Product {
            lhs: Rc::new(lhs),
            rhs: Rc::new(rhs),
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
                ty: Some(Expression::Set),
            },
            kind,
        }
    }
}
