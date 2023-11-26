use core::panic;
use std::rc::Rc;

use crate::env::*;
use crate::path::*;
use crate::pattern::*;
use crate::render::*;
use crate::ty::*;

use rustc_ast::LitKind;
use rustc_hir::BinOpKind;

/// Struct [FreshVars] represents a set of fresh variables
#[derive(Debug)]
pub(crate) struct FreshVars(u64);

impl FreshVars {
    pub(crate) fn new() -> Self {
        FreshVars(0)
    }

    fn next(&self) -> (String, Self) {
        (format!("α{}", self.0), FreshVars(self.0 + 1))
    }
}

/// Struct [MatchArm] represents a pattern-matching branch: [pat] is the
/// matched pattern and [body] the expression on which it is mapped
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) struct MatchArm {
    pub(crate) pat: Pattern,
    pub(crate) body: Expr,
}

/// [LoopControlFlow] represents the expressions responsible for
/// the flow of control in a loop
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) enum LoopControlFlow {
    Continue,
    Break,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) struct Expr {
    pub(crate) kind: ExprKind,
    pub(crate) ty: Option<Rc<CoqType>>,
}

/// Enum [ExprKind] represents the AST of rust terms.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) enum ExprKind {
    Pure(Box<Expr>),
    LocalVar(String),
    Var(Path),
    VarWithTy {
        path: Path,
        ty_name: String,
        ty: Rc<CoqType>,
    },
    VarWithSelfTy {
        path: Path,
        self_ty: Rc<CoqType>,
    },
    AssociatedFunction {
        ty: Rc<CoqType>,
        func: String,
    },
    Literal {
        literal: LitKind,
        neg: bool,
    },
    NonHirLiteral(rustc_middle::ty::ScalarInt),
    Call {
        func: Box<Expr>,
        args: Vec<Expr>,
    },
    /// An operator that takes one argument that is supposed to be in monadic
    /// form once the monadic translation is done.
    MonadicOperator {
        name: String,
        arg: Box<Expr>,
    },
    Lambda {
        args: Vec<Pattern>,
        body: Box<Expr>,
    },
    Array {
        elements: Vec<Expr>,
    },
    Tuple {
        elements: Vec<Expr>,
    },
    Let {
        is_monadic: bool,
        pattern: Box<Pattern>,
        init: Box<Expr>,
        body: Box<Expr>,
    },
    LetIf {
        pat: Box<Pattern>,
        init: Box<Expr>,
    },
    If {
        condition: Box<Expr>,
        success: Box<Expr>,
        failure: Box<Expr>,
    },
    Loop {
        body: Box<Expr>,
    },
    Match {
        scrutinee: Box<Expr>,
        arms: Vec<MatchArm>,
    },
    #[allow(dead_code)]
    IndexedField {
        base: Box<Expr>,
        index: u32,
    },
    NamedField {
        base: Box<Expr>,
        name: String,
    },
    Index {
        base: Box<Expr>,
        index: Box<Expr>,
    },
    ControlFlow(LoopControlFlow),
    StructStruct {
        path: Path,
        fields: Vec<(String, Expr)>,
        base: Option<Box<Expr>>,
        struct_or_variant: StructOrVariant,
    },
    StructTuple {
        path: Path,
        fields: Vec<Expr>,
        struct_or_variant: StructOrVariant,
    },
    #[allow(dead_code)]
    StructUnit {
        path: Path,
    },
    Return(Box<Expr>),
    /// Useful for error messages or annotations
    Message(String),
}

pub(crate) fn compile_bin_op_kind(bin_op_kind: BinOpKind) -> String {
    match bin_op_kind {
        BinOpKind::Add => "add".to_string(),
        BinOpKind::Sub => "sub".to_string(),
        BinOpKind::Mul => "mul".to_string(),
        BinOpKind::Div => "div".to_string(),
        BinOpKind::Rem => "rem".to_string(),
        BinOpKind::And => "andb".to_string(),
        BinOpKind::Or => "or".to_string(),
        BinOpKind::BitXor => "bitxor".to_string(),
        BinOpKind::BitAnd => "bitand".to_string(),
        BinOpKind::BitOr => "bitor".to_string(),
        BinOpKind::Shl => "shl".to_string(),
        BinOpKind::Shr => "shr".to_string(),
        BinOpKind::Eq => "eq".to_string(),
        BinOpKind::Lt => "lt".to_string(),
        BinOpKind::Le => "le".to_string(),
        BinOpKind::Ne => "ne".to_string(),
        BinOpKind::Ge => "ge".to_string(),
        BinOpKind::Gt => "gt".to_string(),
    }
}

impl ExprKind {
    pub(crate) fn tt() -> Self {
        ExprKind::LocalVar("tt".to_string()).alloc(Some(CoqType::unit()))
    }
}

impl Expr {
    /// The Coq value [tt] (the inhabitant of the [unit] type) is used as default
    /// value
    pub(crate) fn tt() -> Self {
        Expr {
            kind: ExprKind::tt(),
            ty: Some(CoqType::unit().val()),
        }
    }

    pub(crate) fn has_return(&self) -> bool {
        match &self.kind {
            ExprKind::Pure(expr) => expr.has_return(),
            ExprKind::LocalVar(_) => false,
            ExprKind::Var(_) => false,
            ExprKind::VarWithTy {
                path: _,
                ty_name: _,
                ty: _,
            } => false,
            ExprKind::VarWithSelfTy {
                path: _,
                self_ty: _,
            } => false,
            ExprKind::AssociatedFunction { ty: _, func: _ } => false,
            ExprKind::Literal { literal: _, neg: _ } => false,
            ExprKind::NonHirLiteral(_) => false,
            ExprKind::Call { func, args } => func.has_return() || args.iter().any(Self::has_return),
            ExprKind::MonadicOperator { name: _, arg } => arg.has_return(),
            ExprKind::Lambda { args: _, body } => body.has_return(),
            ExprKind::Array { elements } => elements.iter().any(Self::has_return),
            ExprKind::Tuple { elements } => elements.iter().any(Self::has_return),
            ExprKind::Let {
                is_monadic: _,
                pattern: _,
                init,
                body,
            } => init.has_return() || body.has_return(),
            ExprKind::LetIf { pat: _, init } => init.has_return(),
            ExprKind::If {
                condition,
                success,
                failure,
            } => condition.has_return() || success.has_return() || failure.has_return(),
            ExprKind::Loop { body } => body.has_return(),
            ExprKind::Match { scrutinee, arms } => {
                scrutinee.has_return()
                    || arms
                        .iter()
                        .any(|MatchArm { pat: _, body }| body.has_return())
            }
            ExprKind::IndexedField { base, index: _ } => base.has_return(),
            ExprKind::NamedField { base, name: _ } => base.has_return(),
            ExprKind::Index { base, index } => base.has_return() || index.has_return(),
            ExprKind::ControlFlow(_) => false,
            ExprKind::StructStruct {
                path: _,
                fields,
                base,
                struct_or_variant: _,
            } => {
                fields.iter().any(|(_, field)| field.has_return())
                    || base.iter().any(|base| base.has_return())
            }
            ExprKind::StructTuple {
                path: _,
                fields,
                struct_or_variant: _,
            } => fields.iter().any(Self::has_return),
            ExprKind::StructUnit { path: _ } => false,
            ExprKind::Return(_) => true,
            ExprKind::Message(_) => false,
        }
    }
}

fn pure(e: Expr) -> Expr {
    Expr {
        ty: e.ty.clone(),
        kind: ExprKind::Pure(Box::new(e)),
    }
}

/// creates a monadic let statement with [e1] as the initializer
/// and the result of [f] as the body
fn monadic_let_in_stmt(
    fresh_vars: FreshVars,
    e1: Expr,
    f: impl FnOnce(FreshVars, Expr) -> (Expr, FreshVars),
) -> (Expr, FreshVars) {
    match e1.kind {
        ExprKind::Pure(e) => f(fresh_vars, *e),
        ExprKind::Let {
            is_monadic,
            pattern,
            init,
            body,
        } => {
            let (body, fresh_vars) = monadic_let_in_stmt(fresh_vars, *body, f);
            (
                Expr {
                    ty: body.ty.clone(),
                    kind: ExprKind::Let {
                        is_monadic,
                        pattern,
                        init,
                        body: Box::new(body),
                    },
                },
                fresh_vars,
            )
        }
        _ => {
            let (var_name, fresh_vars) = fresh_vars.next();
            let (body, fresh_vars) = f(
                fresh_vars,
                Expr {
                    kind: ExprKind::LocalVar(var_name.clone()),
                    ty: None,
                },
            );
            (
                Expr {
                    ty: body.ty.clone(),
                    kind: ExprKind::Let {
                        is_monadic: true,
                        pattern: Box::new(Pattern::Variable(var_name)),
                        init: Box::new(e1),
                        body: Box::new(body),
                    },
                },
                fresh_vars,
            )
        }
    }
}

fn monadic_let(
    fresh_vars: FreshVars,
    e1: Expr,
    f: impl FnOnce(FreshVars, Expr) -> (Expr, FreshVars),
) -> (Expr, FreshVars) {
    let (e1, fresh_vars) = mt_expression(fresh_vars, e1);
    monadic_let_in_stmt(fresh_vars, e1, f)
}

fn monadic_optional_let(
    fresh_vars: FreshVars,
    e1: Option<Box<Expr>>,
    f: impl FnOnce(FreshVars, Option<Box<Expr>>) -> (Expr, FreshVars),
) -> (Expr, FreshVars) {
    match e1 {
        None => f(fresh_vars, None),
        Some(e1) => monadic_let(fresh_vars, *e1, |fresh_vars, e1| {
            f(fresh_vars, Some(Box::new(e1)))
        }),
    }
}

fn monadic_lets(
    fresh_vars: FreshVars,
    es: Vec<Expr>,
    f: Box<dyn FnOnce(FreshVars, Vec<Expr>) -> (Expr, FreshVars)>,
) -> (Expr, FreshVars) {
    match &es[..] {
        [] => f(fresh_vars, vec![]),
        [e1, es @ ..] => monadic_let(fresh_vars, e1.clone(), |fresh_vars, e1| {
            monadic_lets(
                fresh_vars,
                es.to_vec(),
                Box::new(|fresh_vars, es| f(fresh_vars, [vec![e1], es].concat())),
            )
        }),
    }
}

fn is_literal_pure(literal: &LitKind) -> bool {
    matches!(literal, LitKind::Str(_, _))
}

/// Monadic translation of an expression
///
/// The convention is to do transformation in a deep first fashion, so
/// all functions dealing with monadic translation expect that their
/// arguments already have been transformed. Not respecting this rule
/// may lead to infinite loops because of the mutual recursion between
/// the functions. In practice this means translating every subexpression
/// before translating the expression itself.
pub(crate) fn mt_expression(fresh_vars: FreshVars, expr: Expr) -> (Expr, FreshVars) {
    let ty = expr.ty.clone().map(mt_ty);
    match expr.kind {
        ExprKind::Pure(_) => panic!("Expressions should not be monadic yet."),
        ExprKind::LocalVar(_) => (pure(expr), fresh_vars),
        ExprKind::Var(_) => (pure(expr), fresh_vars),
        ExprKind::VarWithTy {
            path,
            ty_name,
            ty: var_ty,
        } => (
            pure(Expr {
                kind: ExprKind::VarWithTy {
                    path,
                    ty_name,
                    ty: mt_ty(var_ty),
                },
                ty,
            }),
            fresh_vars,
        ),
        ExprKind::VarWithSelfTy { path, self_ty } => (
            pure(Expr {
                kind: ExprKind::VarWithSelfTy {
                    path,
                    self_ty: mt_ty(self_ty),
                },
                ty,
            }),
            fresh_vars,
        ),
        ExprKind::AssociatedFunction { .. } => (pure(expr), fresh_vars),
        ExprKind::Literal { ref literal, .. } => (
            if is_literal_pure(literal) {
                pure(expr)
            } else {
                expr
            },
            fresh_vars,
        ),
        ExprKind::NonHirLiteral { .. } => (pure(expr), fresh_vars),
        ExprKind::Call { func, args } => monadic_let(fresh_vars, *func, |fresh_vars, func| {
            monadic_lets(
                fresh_vars,
                args,
                Box::new(|fresh_vars, args| {
                    (
                        Expr {
                            kind: ExprKind::Call {
                                func: Box::new(func),
                                args,
                            },
                            ty,
                        },
                        fresh_vars,
                    )
                }),
            )
        }),
        ExprKind::MonadicOperator { name, arg } => {
            let (arg, fresh_vars) = mt_expression(fresh_vars, *arg);
            (
                Expr {
                    kind: ExprKind::MonadicOperator {
                        name,
                        arg: Box::new(arg),
                    },
                    ty,
                },
                fresh_vars,
            )
        }
        ExprKind::Lambda { args, body } => {
            let (body, _) = mt_expression(FreshVars::new(), *body);
            (
                pure(Expr {
                    kind: ExprKind::Lambda {
                        args,
                        body: Box::new(body),
                    },
                    ty,
                }),
                fresh_vars,
            )
        }
        ExprKind::Array { elements } => monadic_lets(
            fresh_vars,
            elements,
            Box::new(|fresh_vars, elements| {
                (
                    pure(Expr {
                        kind: ExprKind::Array { elements },
                        ty,
                    }),
                    fresh_vars,
                )
            }),
        ),
        ExprKind::Tuple { elements } => monadic_lets(
            fresh_vars,
            elements,
            Box::new(|fresh_vars, elements| {
                (
                    pure(Expr {
                        kind: ExprKind::Tuple { elements },
                        ty,
                    }),
                    fresh_vars,
                )
            }),
        ),
        ExprKind::Let {
            is_monadic,
            pattern,
            init,
            body,
        } => {
            if is_monadic {
                panic!("The let statement should not be monadic yet.")
            }
            let (init, _fresh_vars) = mt_expression(FreshVars::new(), *init);
            let (body, _fresh_vars) = mt_expression(FreshVars::new(), *body);
            let body = Box::new(body);
            let pure_init: Option<Box<Expr>> = get_pure_from_stmt(init.clone());
            (
                match pure_init {
                    Some(pure_init) => Expr {
                        kind: ExprKind::Let {
                            is_monadic: false,
                            pattern,
                            init: pure_init,
                            body,
                        },
                        ty,
                    },
                    None => Expr {
                        kind: ExprKind::Let {
                            is_monadic: true,
                            pattern,
                            init: Box::new(init),
                            body,
                        },
                        ty,
                    },
                },
                fresh_vars,
            )
        }
        ExprKind::LetIf { pat, init } => monadic_let(fresh_vars, *init, |fresh_vars, init| {
            (
                Expr {
                    kind: ExprKind::LetIf {
                        pat,
                        init: Box::new(init),
                    },
                    ty: ty.clone(),
                },
                fresh_vars,
            )
        }),
        ExprKind::If {
            condition,
            success,
            failure,
        } => monadic_let(fresh_vars, *condition, |fresh_vars, condition| {
            let (success, _fresh_vars) = mt_expression(FreshVars::new(), *success);
            let (failure, _fresh_vars) = mt_expression(FreshVars::new(), *failure);
            (
                Expr {
                    kind: ExprKind::If {
                        condition: Box::new(condition),
                        success: Box::new(success),
                        failure: Box::new(failure),
                    },
                    ty: ty.clone(),
                },
                fresh_vars,
            )
        }),
        ExprKind::Loop { body, .. } => {
            let (body, fresh_vars) = mt_expression(fresh_vars, *body);
            (
                Expr {
                    kind: ExprKind::Loop {
                        body: Box::new(body),
                    },
                    ty,
                },
                fresh_vars,
            )
        }
        ExprKind::Match { scrutinee, arms } => {
            monadic_let(fresh_vars, *scrutinee, |fresh_vars, scrutinee| {
                (
                    Expr {
                        kind: ExprKind::Match {
                            scrutinee: Box::new(scrutinee),
                            arms: arms
                                .iter()
                                .map(|MatchArm { pat, body }| {
                                    let (body, _fresh_vars) =
                                        mt_expression(FreshVars::new(), body.clone());
                                    MatchArm {
                                        pat: pat.clone(),
                                        body,
                                    }
                                })
                                .collect(),
                        },
                        ty: ty.clone(),
                    },
                    fresh_vars,
                )
            })
        }
        ExprKind::IndexedField { base, index } => {
            monadic_let(fresh_vars, *base, |fresh_vars, base| {
                (
                    pure(Expr {
                        kind: ExprKind::IndexedField {
                            base: Box::new(base),
                            index,
                        },
                        ty,
                    }),
                    fresh_vars,
                )
            })
        }
        ExprKind::NamedField { base, name } => {
            monadic_let(fresh_vars, *base, |fresh_vars, base| {
                (
                    pure(Expr {
                        kind: ExprKind::NamedField {
                            base: Box::new(base),
                            name,
                        },
                        ty: ty.clone(),
                    }),
                    fresh_vars,
                )
            })
        }
        ExprKind::Index { base, index } => monadic_let(fresh_vars, *base, |fresh_vars, base| {
            (
                pure(Expr {
                    kind: ExprKind::Index {
                        base: Box::new(base),
                        index,
                    },
                    ty,
                }),
                fresh_vars,
            )
        }),
        // control flow expressions are responsible for side effects, so they are monadic already
        ExprKind::ControlFlow(lcf_expression) => (
            Expr {
                kind: ExprKind::ControlFlow(lcf_expression),
                ty,
            },
            fresh_vars,
        ),
        ExprKind::StructStruct {
            path,
            fields,
            base,
            struct_or_variant,
        } => {
            let fields_values: Vec<Expr> = fields.iter().map(|(_, field)| field.clone()).collect();
            monadic_lets(
                fresh_vars,
                fields_values,
                Box::new(move |fresh_vars, fields_values| {
                    monadic_optional_let(fresh_vars, base, |fresh_vars, base| {
                        let fields_names: Vec<String> =
                            fields.iter().map(|(name, _)| name.clone()).collect();
                        (
                            pure(Expr {
                                kind: ExprKind::StructStruct {
                                    path,
                                    fields: fields_names
                                        .iter()
                                        .zip(fields_values.iter())
                                        .map(|(name, value)| (name.clone(), value.clone()))
                                        .collect(),
                                    base,
                                    struct_or_variant,
                                },
                                ty,
                            }),
                            fresh_vars,
                        )
                    })
                }),
            )
        }
        ExprKind::StructTuple {
            path,
            fields,
            struct_or_variant,
        } => monadic_lets(
            fresh_vars,
            fields,
            Box::new(|fresh_vars, fields| {
                (
                    pure(Expr {
                        kind: ExprKind::StructTuple {
                            path,
                            fields,
                            struct_or_variant,
                        },
                        ty,
                    }),
                    fresh_vars,
                )
            }),
        ),
        ExprKind::StructUnit { .. } => (pure(expr), fresh_vars),
        ExprKind::Return(expr) => monadic_let(fresh_vars, *expr, |fresh_vars, expr| {
            (
                Expr {
                    kind: ExprKind::Return(Box::new(expr)),
                    ty,
                },
                fresh_vars,
            )
        }),
        ExprKind::Message(_) => (pure(expr), fresh_vars),
    }
}

/// Get the pure part of a statement, if possible, as a statement.
fn get_pure_from_stmt(statement: Expr) -> Option<Box<Expr>> {
    match statement.kind {
        ExprKind::Pure(e) => Some(e),
        ExprKind::Let {
            is_monadic: true, ..
        } => None,
        ExprKind::Let {
            is_monadic: false,
            pattern,
            init,
            body,
        } => get_pure_from_stmt(*body).map(|body| {
            Box::new(Expr {
                kind: ExprKind::Let {
                    is_monadic: false,
                    pattern,
                    init,
                    body,
                },
                ty: statement.ty,
            })
        }),
        _ => None,
    }
}

pub(crate) fn compile_hir_id(env: &mut Env, hir_id: rustc_hir::hir_id::HirId) -> Expr {
    let local_def_id = hir_id.owner.def_id;
    let thir = env.tcx.thir_body(local_def_id);
    let Ok((thir, expr_id)) = thir else {
        panic!("thir failed to compile");
    };
    let thir = thir.borrow();
    crate::thir_expression::compile_expr(env, &thir, &expr_id)
}

impl MatchArm {
    fn to_doc(&self) -> Doc {
        return nest([
            nest([text("|"), line(), self.pat.to_doc(), line(), text("=>")]),
            line(),
            self.body.to_doc(false),
        ]);
    }
}

impl LoopControlFlow {
    pub fn to_doc(&self) -> Doc {
        match self {
            LoopControlFlow::Break => text("Break"),
            LoopControlFlow::Continue => text("Continue"),
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
            ExprKind::Pure(expr) => paren(
                with_paren,
                nest([text("M.pure"), line(), expr.to_doc(true)]),
            ),
            ExprKind::LocalVar(ref name) => text(name),
            ExprKind::Var(path) => path.to_doc(),
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
            ExprKind::VarWithSelfTy { path, self_ty } => paren(
                with_paren,
                nest([
                    path.to_doc(),
                    line(),
                    nest([
                        text("(Self :="),
                        line(),
                        self_ty.to_coq().to_doc(false),
                        text(")"),
                    ]),
                    line(),
                    nest([
                        text("(Trait :="),
                        line(),
                        text("ltac:(refine _)"),
                        text(")"),
                    ]),
                ]),
            ),
            ExprKind::AssociatedFunction { ty, func } => nest([
                ty.to_coq().to_doc(true),
                text("::["),
                text(format!("\"{func}\"")),
                text("]"),
            ]),
            ExprKind::Literal { literal, neg } => literal_to_doc(with_paren, literal, *neg),
            ExprKind::NonHirLiteral(literal) => text(literal.to_string()),
            ExprKind::Call { func, args } => {
                if args.is_empty() {
                    func.to_doc(with_paren)
                } else {
                    paren(
                        with_paren,
                        nest([
                            func.to_doc(true),
                            concat(args.iter().map(|arg| concat([line(), arg.to_doc(true)]))),
                        ]),
                    )
                }
            }
            ExprKind::MonadicOperator { name, arg } => {
                paren(with_paren, nest([text(name), line(), arg.to_doc(true)]))
            }
            ExprKind::Lambda { args, body } => {
                if args.is_empty() {
                    body.to_doc(with_paren)
                } else {
                    paren(
                        with_paren,
                        nest([
                            nest([
                                text("fun"),
                                line(),
                                intersperse(args.iter().map(|arg| arg.to_doc()), [line()]),
                                text(" =>"),
                            ]),
                            line(),
                            body.to_doc(false),
                        ]),
                    )
                }
            }
            ExprKind::Array { elements } => group([
                nest([
                    text("["),
                    if !elements.is_empty() { line() } else { nil() },
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
                pattern,
                init,
                body,
            } => paren(
                with_paren,
                group([
                    nest([
                        nest([
                            nest([
                                text("let"),
                                if *is_monadic { text("*") } else { nil() },
                                line(),
                                (if !pattern.is_single_binding() {
                                    text("'")
                                } else {
                                    nil()
                                }),
                            ]),
                            pattern.to_doc(),
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
            ExprKind::LetIf { pat, init } => group([
                text("let_if"),
                line(),
                pat.to_doc(),
                line(),
                text(":="),
                line(),
                init.to_doc(false),
            ]),
            ExprKind::If {
                condition,
                success,
                failure,
            } => paren(
                with_paren,
                group([
                    group([
                        nest([
                            text("if"),
                            line(),
                            text("("),
                            condition.to_doc(false),
                            line(),
                            text(": bool)"),
                        ]),
                        line(),
                        text("then"),
                    ]),
                    nest([hardline(), success.to_doc(false)]),
                    hardline(),
                    nest([text("else"), hardline(), failure.to_doc(false)]),
                ]),
            ),
            ExprKind::Loop {
                body, /*loop_source*/
                ..
            } => paren(
                with_paren,
                nest([text("loop"), line(), paren(true, body.to_doc(with_paren))]),
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
            ExprKind::IndexedField { base, index } => paren(
                with_paren,
                nest([
                    base.to_doc(true),
                    text(".["),
                    text(index.to_string()),
                    text("]"),
                ]),
            ),
            ExprKind::NamedField { base, name } => nest([
                base.to_doc(true),
                text(".["),
                text(format!("\"{name}\"")),
                text("]"),
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
            } => group([
                group([
                    nest([
                        match struct_or_variant {
                            StructOrVariant::Struct => nil(),
                            StructOrVariant::Variant => concat([path.to_doc(), line()]),
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
                ]),
                match base {
                    Some(base) => nest([line(), text("with"), line(), base.to_doc(false)]),
                    None => nil(),
                },
            ]),
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
                        StructOrVariant::Variant => nil(),
                    },
                    concat(fields.iter().map(|arg| concat([line(), arg.to_doc(true)]))),
                ]),
            ),
            ExprKind::StructUnit { path } => nest([path.to_doc(), text(".Build")]),
            ExprKind::Return(value) => paren(
                with_paren,
                nest([text("return_"), line(), value.to_doc(true)]),
            ),
            ExprKind::Message(message) => text(format!("\"{message}\"")),
        }
    }
}
