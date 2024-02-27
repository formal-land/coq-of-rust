use crate::env::*;
use crate::path::*;
use crate::pattern::*;
use crate::render::*;
use crate::ty::*;
use core::panic;
use rustc_middle::query::plumbing::IntoQueryParam;
use std::rc::Rc;

/// Struct [MatchArm] represents a pattern-matching branch: [pat] is the
/// matched pattern and [body] the expression on which it is mapped
#[derive(Debug, Eq, Hash, PartialEq)]
pub(crate) struct MatchArm {
    pub(crate) pattern: Rc<Pattern>,
    pub(crate) body: Rc<Expr>,
}

/// [LoopControlFlow] represents the expressions responsible for
/// the flow of control in a loop
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum LoopControlFlow {
    Continue,
    Break,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(crate) enum Purity {
    Pure,
    Effectful,
}

#[derive(Debug, Eq, Hash, PartialEq)]
pub(crate) enum Literal {
    Bool(bool),
    Integer { value: u128, neg: bool },
    Char(char),
    String(String),
    Error,
}

#[derive(Debug, Eq, Hash, PartialEq)]
pub(crate) struct Expr {
    pub(crate) kind: Rc<ExprKind>,
    pub(crate) ty: Option<Rc<CoqType>>,
}

/// Enum [ExprKind] represents the AST of rust terms.
#[derive(Debug, Eq, Hash, PartialEq)]
pub(crate) enum ExprKind {
    LocalVar(String),
    Var(Path),
    Constructor(Path),
    VarWithTy {
        path: Path,
        ty_name: String,
        ty: Rc<CoqType>,
    },
    VarWithTys {
        path: Path,
        tys: Vec<(String, Rc<CoqType>)>,
    },
    AssociatedFunction {
        ty: Rc<CoqType>,
        func: String,
    },
    Literal(Literal, Option<Rc<CoqType>>),
    Call {
        func: Rc<Expr>,
        args: Vec<Rc<Expr>>,
        purity: Purity,
        from_user: bool,
    },
    /// An operator that takes one argument that is supposed to be in monadic
    /// form once the monadic translation is done.
    MonadicOperator {
        name: String,
        arg: Rc<Expr>,
    },
    Lambda {
        args: Vec<(String, Option<Rc<CoqType>>)>,
        body: Rc<Expr>,
        is_for_match: bool,
    },
    Array {
        elements: Vec<Rc<Expr>>,
    },
    Tuple {
        elements: Vec<Rc<Expr>>,
    },
    Let {
        is_monadic: bool,
        name: Option<String>,
        init: Rc<Expr>,
        body: Rc<Expr>,
    },
    If {
        condition: Rc<Expr>,
        success: Rc<Expr>,
        failure: Rc<Expr>,
    },
    Loop {
        body: Rc<Expr>,
    },
    Match {
        scrutinee: Rc<Expr>,
        arms: Vec<Rc<MatchArm>>,
    },
    Index {
        base: Rc<Expr>,
        index: Rc<Expr>,
    },
    ControlFlow(LoopControlFlow),
    StructStruct {
        path: Path,
        fields: Vec<(String, Rc<Expr>)>,
        base: Option<Rc<Expr>>,
        struct_or_variant: StructOrVariant,
        ty: Option<Rc<CoqType>>,
    },
    StructTuple {
        path: Path,
        fields: Vec<Rc<Expr>>,
        struct_or_variant: StructOrVariant,
    },
    StructUnit {
        path: Path,
        struct_or_variant: StructOrVariant,
    },
    Use(Rc<Expr>),
    Return(Rc<Expr>),
    /// Useful for error messages or annotations
    Message(String),
}

impl ExprKind {
    pub(crate) fn tt() -> Rc<Self> {
        Rc::new(ExprKind::LocalVar("tt".to_string())).alloc(Some(CoqType::unit()))
    }
}

impl Expr {
    /// The Coq value [tt] (the inhabitant of the [unit] type) is used as default
    /// value
    pub(crate) fn tt() -> Rc<Self> {
        Rc::new(Expr {
            kind: ExprKind::tt(),
            ty: Some(CoqType::unit().val()),
        })
    }

    pub(crate) fn local_var(name: &str) -> Rc<Expr> {
        Rc::new(Expr {
            kind: Rc::new(ExprKind::LocalVar(name.to_string())),
            ty: None,
        })
    }

    pub(crate) fn has_return(&self) -> bool {
        match self.kind.as_ref() {
            ExprKind::LocalVar(_) => false,
            ExprKind::Var(_) => false,
            ExprKind::Constructor(_) => false,
            ExprKind::VarWithTy {
                path: _,
                ty_name: _,
                ty: _,
            } => false,
            ExprKind::VarWithTys { path: _, tys: _ } => false,
            ExprKind::AssociatedFunction { ty: _, func: _ } => false,
            ExprKind::Literal(_, _) => false,
            ExprKind::Call {
                func,
                args,
                purity: _,
                from_user: _,
            } => func.has_return() || args.iter().any(|arg| arg.has_return()),
            ExprKind::MonadicOperator { name: _, arg } => arg.has_return(),
            ExprKind::Lambda {
                args: _,
                body,
                is_for_match,
            } => *is_for_match && body.has_return(),
            ExprKind::Array { elements } => elements.iter().any(|element| element.has_return()),
            ExprKind::Tuple { elements } => elements.iter().any(|element| element.has_return()),
            ExprKind::Let {
                is_monadic: _,
                name: _,
                init,
                body,
            } => init.has_return() || body.has_return(),
            ExprKind::If {
                condition,
                success,
                failure,
            } => condition.has_return() || success.has_return() || failure.has_return(),
            ExprKind::Loop { body } => body.has_return(),
            ExprKind::Match { scrutinee, arms } => {
                scrutinee.has_return() || arms.iter().any(|arm| arm.body.has_return())
            }
            ExprKind::Index { base, index } => base.has_return() || index.has_return(),
            ExprKind::ControlFlow(_) => false,
            ExprKind::StructStruct {
                path: _,
                fields,
                base,
                struct_or_variant: _,
                ty: _,
            } => {
                fields.iter().any(|(_, field)| field.has_return())
                    || base.iter().any(|base| base.has_return())
            }
            ExprKind::StructTuple {
                path: _,
                fields,
                struct_or_variant: _,
            } => fields.iter().any(|field| field.has_return()),
            ExprKind::StructUnit {
                path: _,
                struct_or_variant: _,
            } => false,
            ExprKind::Use(expr) => expr.has_return(),
            ExprKind::Return(_) => true,
            ExprKind::Message(_) => false,
        }
    }
}

pub(crate) fn apply_on_thir<'a, F, A>(
    env: &Env<'a>,
    local_def_id: impl IntoQueryParam<rustc_span::def_id::LocalDefId>,
    f: F,
) -> Result<A, String>
where
    F: FnOnce(&rustc_middle::thir::Thir<'a>, &rustc_middle::thir::ExprId) -> A,
{
    let thir = env.tcx.thir_body(local_def_id);
    let Ok((thir, expr_id)) = thir else {
        return Result::Err("thir failed to compile".to_string());
    };
    let result = std::panic::catch_unwind(panic::AssertUnwindSafe(|| thir.borrow()));

    match result {
        Ok(thir) => Result::Ok(f(&thir, &expr_id)),
        Err(error) => Result::Err(format!("thir failed to compile: {:?}", error)),
    }
}

pub(crate) fn compile_hir_id(env: &Env, hir_id: rustc_hir::hir_id::HirId) -> Rc<Expr> {
    let local_def_id = hir_id.owner.def_id;
    let result = apply_on_thir(env, local_def_id, |thir, expr_id| {
        crate::thir_expression::compile_expr(env, thir, expr_id)
    });

    match result {
        Ok(expr) => expr,
        Err(error) => Rc::new(Expr {
            kind: Rc::new(ExprKind::Message(error)),
            ty: None,
        }),
    }
}

impl MatchArm {
    fn to_doc(&self) -> Doc {
        return nest([
            nest([
                text("|"),
                line(),
                self.pattern.to_doc(false),
                line(),
                text("=>"),
            ]),
            line(),
            self.body.to_doc(false),
        ]);
    }
}

impl LoopControlFlow {
    pub fn to_doc<'a>(self) -> Doc<'a> {
        match self {
            LoopControlFlow::Break => text("M.break"),
            LoopControlFlow::Continue => text("M.continue"),
        }
    }
}

impl Literal {
    fn to_doc(&self, with_paren: bool) -> Doc {
        match self {
            Literal::Bool(b) => text(format!("{b}")),
            Literal::Integer { value, neg } => {
                paren(
                    with_paren,
                    nest([
                        text("Integer.of_Z"),
                        line(),
                        if *neg {
                            // We always put parenthesis.
                            text(format!("(-{value})"))
                        } else {
                            text(format!("{}", value))
                        },
                    ]),
                )
            }
            Literal::Char(c) => text(format!("\"{c}\"%char")),
            Literal::String(s) => string_to_doc(with_paren, s.as_str()),
            Literal::Error => text("UnsupportedLiteral"),
        }
    }
}

impl Expr {
    pub(crate) fn to_doc(&self, with_paren: bool) -> Doc {
        self.kind.to_doc(with_paren)
    }
}

impl ExprKind {
    pub(crate) fn to_doc(&self, with_paren: bool) -> Doc {
        match self {
            ExprKind::LocalVar(ref name) => text(name),
            ExprKind::Var(path) => path.to_doc(),
            ExprKind::Constructor(path) => path.to_doc(),
            ExprKind::VarWithTy { path, ty_name, ty } => paren(
                with_paren,
                nest([
                    path.to_doc(),
                    line(),
                    nest([
                        text(format!("({ty_name} :=")),
                        line(),
                        ty.to_coq().to_doc(false),
                        text(")"),
                    ]),
                ]),
            ),
            ExprKind::VarWithTys { path, tys } => nest([
                text("ltac:(M.get_method (fun ℐ =>"),
                line(),
                nest([
                    path.to_doc(),
                    concat(tys.iter().map(|(name, ty)| {
                        concat([
                            line(),
                            nest([
                                text("("),
                                text(name),
                                text(" :="),
                                line(),
                                ty.to_coq().to_doc(false),
                                text(")"),
                            ]),
                        ])
                    })),
                    line(),
                    text("(Trait := ℐ)"),
                ]),
                text("))"),
            ]),
            ExprKind::AssociatedFunction { ty, func } => nest([
                ty.to_coq().to_doc(true),
                text("::["),
                text(format!("\"{func}\"")),
                text("]"),
            ]),
            ExprKind::Literal(literal, ty) => match ty {
                None => literal.to_doc(with_paren),
                Some(ty) => paren(
                    with_paren,
                    nest([
                        literal.to_doc(true),
                        text(" :"),
                        line(),
                        ty.to_coq().to_doc(false),
                    ]),
                ),
            },
            ExprKind::Call {
                func,
                args,
                purity,
                from_user,
            } => {
                let inner_with_paren = with_paren || *from_user;
                let inner_application_pure = optional_insert_with(
                    args.is_empty(),
                    func.to_doc(inner_with_paren),
                    paren(
                        inner_with_paren,
                        nest([
                            func.to_doc(true),
                            concat(args.iter().map(|arg| concat([line(), arg.to_doc(true)]))),
                        ]),
                    ),
                );
                let inner_application_effectful = optional_insert_with(
                    args.is_empty(),
                    group([func.to_doc(inner_with_paren), text("(||)")]),
                    paren(
                        inner_with_paren,
                        group([
                            func.to_doc(true),
                            text(" "),
                            concat([
                                text("(|"),
                                nest([
                                    line(),
                                    intersperse(
                                        args.iter().map(|arg| arg.to_doc(false)),
                                        [text(","), line()],
                                    ),
                                ]),
                                line(),
                                text("|)"),
                            ]),
                        ]),
                    ),
                );
                match purity {
                    Purity::Pure => {
                        if *from_user {
                            paren(
                                with_paren,
                                nest([text("M.call"), line(), inner_application_pure]),
                            )
                        } else {
                            inner_application_pure
                        }
                    }
                    Purity::Effectful => {
                        if *from_user {
                            paren(
                                with_paren,
                                group([
                                    text("M.call"),
                                    text(" "),
                                    concat([
                                        text("(|"),
                                        inner_application_pure,
                                        line(),
                                        text("|)"),
                                    ]),
                                ]),
                            )
                        } else {
                            inner_application_effectful
                        }
                    }
                }
            }
            ExprKind::MonadicOperator { name, arg } => {
                paren(with_paren, nest([text(name), line(), arg.to_doc(true)]))
            }
            ExprKind::Lambda {
                args,
                body,
                is_for_match: _,
            } => {
                let body = group([
                    body.to_doc(true),
                    text(" :"),
                    line(),
                    match &body.ty {
                        Some(ret_ty) => ret_ty.clone().to_coq().to_doc(false),
                        None => text("_"),
                    },
                ]);

                if args.is_empty() {
                    paren(with_paren, body)
                } else {
                    paren(
                        with_paren,
                        nest([
                            nest([
                                text("fun"),
                                line(),
                                intersperse(
                                    args.iter().map(|(name, ty)| match ty {
                                        None => text(name),
                                        Some(ty) => nest([
                                            text("("),
                                            text(name),
                                            text(" :"),
                                            line(),
                                            ty.to_coq().to_doc(false),
                                            text(")"),
                                        ]),
                                    }),
                                    [line()],
                                ),
                                text(" =>"),
                            ]),
                            line(),
                            body,
                        ]),
                    )
                }
            }
            ExprKind::Array { elements } => group([
                nest([
                    text("["),
                    optional_insert(elements.is_empty(), line()),
                    intersperse(
                        elements.iter().map(|element| element.to_doc(false)),
                        [text(";"), line()],
                    ),
                ]),
                line(),
                text("]"),
            ]),
            ExprKind::Tuple { elements } => paren(
                true,
                nest([intersperse(
                    elements.iter().map(|element| element.to_doc(false)),
                    [text(","), line()],
                )]),
            ),
            ExprKind::Let {
                is_monadic,
                name,
                init,
                body,
            } => paren(
                with_paren,
                group([
                    nest([
                        nest([
                            nest([
                                text("let"),
                                optional_insert(!*is_monadic, text("*")),
                                line(),
                                text(match name {
                                    Some(name) => name,
                                    None => "_",
                                }),
                            ]),
                            match &init.ty {
                                Some(ty) => concat([text(" :"), line(), ty.to_coq().to_doc(false)]),
                                None => nil(),
                            },
                            text(" :="),
                        ]),
                        line(),
                        init.to_doc(false),
                        text(" in"),
                    ]),
                    hardline(),
                    body.to_doc(false),
                ]),
            ),
            ExprKind::If {
                condition,
                success,
                failure,
            } => paren(
                with_paren,
                group([
                    group([
                        nest([text("if"), line(), condition.to_doc(false)]),
                        line(),
                        text("then"),
                    ]),
                    nest([hardline(), success.to_doc(false)]),
                    hardline(),
                    nest([text("else"), hardline(), failure.to_doc(false)]),
                ]),
            ),
            ExprKind::Loop { body } => paren(
                with_paren,
                nest([text("M.loop"), line(), paren(true, body.to_doc(with_paren))]),
            ),
            ExprKind::Match { scrutinee, arms } => group([
                group([
                    nest([text("match"), line(), scrutinee.to_doc(false)]),
                    line(),
                    text("with"),
                ]),
                hardline(),
                intersperse(arms.iter().map(|arm| arm.to_doc()), [hardline()]),
                hardline(),
                text("end"),
            ]),
            ExprKind::Index { base, index } => {
                nest([base.to_doc(true), text("["), index.to_doc(false), text("]")])
            }
            ExprKind::ControlFlow(lcf_expression) => lcf_expression.to_doc(),
            ExprKind::StructStruct {
                path,
                fields,
                base,
                struct_or_variant,
                ty,
            } => match base {
                None => paren(
                    with_paren && matches!(struct_or_variant, StructOrVariant::Variant { .. }),
                    paren(
                        with_paren,
                        group([
                            nest([
                                match struct_or_variant {
                                    StructOrVariant::Struct => nil(),
                                    StructOrVariant::Variant { .. } => {
                                        concat([path.to_doc(), line()])
                                    }
                                },
                                text("{|"),
                                line(),
                                intersperse(
                                    fields.iter().map(|(name, expr)| {
                                        nest([
                                            path.to_doc(),
                                            text("."),
                                            text(name),
                                            text(" :="),
                                            line(),
                                            expr.to_doc(false),
                                            text(";"),
                                        ])
                                    }),
                                    [line()],
                                ),
                            ]),
                            line(),
                            text("|}"),
                            match &ty {
                                Some(struct_ty) => group([
                                    text(" :"),
                                    line(),
                                    struct_ty.clone().to_coq().to_doc(false),
                                ]),
                                None => nil(),
                            },
                        ]),
                    ),
                ),
                Some(base) => paren(
                    with_paren && !fields.is_empty(),
                    nest([
                        base.to_doc(true),
                        concat(fields.iter().map(|(name, expr)| {
                            concat([
                                line(),
                                group([
                                    nest([
                                        text("<| "),
                                        path.to_doc(),
                                        text("."),
                                        text(name),
                                        text(" :="),
                                        line(),
                                        expr.to_doc(false),
                                    ]),
                                    line(),
                                    text("|>"),
                                ]),
                            ])
                        })),
                    ]),
                ),
            },
            ExprKind::StructTuple {
                path,
                fields,
                struct_or_variant,
            } => paren(
                with_paren && !fields.is_empty(),
                nest([
                    path.to_doc(),
                    match struct_or_variant {
                        StructOrVariant::Struct => text(".Build_t"),
                        StructOrVariant::Variant { .. } => nil(),
                    },
                    concat(fields.iter().map(|arg| concat([line(), arg.to_doc(true)]))),
                ]),
            ),
            ExprKind::StructUnit {
                path,
                struct_or_variant,
            } => concat([
                path.to_doc(),
                match struct_or_variant {
                    StructOrVariant::Struct => text(".Build"),
                    StructOrVariant::Variant { .. } => nil(),
                },
            ]),
            ExprKind::Use(expr) => {
                paren(with_paren, nest([text("use"), line(), expr.to_doc(true)]))
            }
            ExprKind::Return(value) => paren(
                with_paren,
                nest([text("return_"), line(), value.to_doc(true)]),
            ),
            ExprKind::Message(message) => text(format!("\"{message}\"")),
        }
    }
}
