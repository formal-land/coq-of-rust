use core::panic;

use crate::env::*;
use crate::path::*;
use crate::pattern::*;
use crate::render::*;
use crate::ty::*;

use rustc_ast::LitKind;
use rustc_hir::{BinOp, BinOpKind, ExprKind, QPath};

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
#[derive(Clone, Debug)]
pub struct MatchArm {
    pat: Pattern,
    body: Expr,
}

/// Enum [Expr] represents the AST of rust terms.
#[derive(Clone, Debug)]
pub(crate) enum Expr {
    Pure(Box<Expr>),
    LocalVar(String),
    Var(Path),
    AssociatedFunction {
        ty: Box<CoqType>,
        func: String,
    },
    Literal(LitKind),
    AddrOf(Box<Expr>),
    Call {
        func: Box<Expr>,
        args: Vec<Expr>,
    },
    MethodCall {
        object: Box<Expr>,
        func: String,
        args: Vec<Expr>,
    },
    Lambda {
        args: Vec<Pattern>,
        body: Box<Expr>,
    },
    Cast {
        expr: Box<Expr>,
        ty: Box<CoqType>,
    },
    Type {
        expr: Box<Expr>,
        ty: Box<CoqType>,
    },
    Array {
        elements: Vec<Expr>,
    },
    Tuple {
        elements: Vec<Expr>,
    },
    LetIf {
        pat: Pattern,
        init: Box<Expr>,
    },
    If {
        condition: Box<Expr>,
        success: Box<Expr>,
        failure: Box<Expr>,
    },
    Loop {
        body: Box<Stmt>,
        loop_source: String,
    },
    Match {
        scrutinee: Box<Expr>,
        arms: Vec<MatchArm>,
    },
    Block(Box<Stmt>),
    Assign {
        left: Box<Expr>,
        right: Box<Expr>,
    },
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
    StructUnit {
        path: Path,
    },
}

#[derive(Clone, Debug)]
pub(crate) enum Stmt {
    Expr(Box<Expr>),
    Let {
        is_monadic: bool,
        pattern: Box<Pattern>,
        init: Box<Expr>,
        body: Box<Stmt>,
    },
}

fn compile_bin_op(bin_op: &BinOp) -> String {
    match bin_op.node {
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

fn compile_assign_bin_op(bin_op: &BinOp) -> String {
    format!("{}_assign", compile_bin_op(bin_op))
}

fn compile_un_op(un_op: &rustc_hir::UnOp) -> String {
    match un_op {
        rustc_hir::UnOp::Deref => "deref".to_string(),
        rustc_hir::UnOp::Not => "not".to_string(),
        rustc_hir::UnOp::Neg => "neg".to_string(),
    }
}

/// The function [compile_loop_source] converts a hir loop instruction to a
/// string
fn compile_loop_source(loop_source: &rustc_hir::LoopSource) -> String {
    match loop_source {
        rustc_hir::LoopSource::Loop => "loop".to_string(),
        rustc_hir::LoopSource::While => "while".to_string(),
        rustc_hir::LoopSource::ForLoop => "for".to_string(),
    }
}

fn compile_qpath(env: &mut Env, qpath: &QPath) -> Expr {
    match qpath {
        QPath::Resolved(_, path) => Expr::Var(compile_path(env, path)),
        QPath::TypeRelative(ty, segment) => {
            let ty = compile_type(env, ty);
            let func = segment.ident.to_string();
            Expr::AssociatedFunction { ty, func }
        }
        QPath::LangItem(_, _, _) => Expr::LocalVar("LangItem".to_string()),
    }
}

/// The Coq value [tt] (the inhabitant of the [unit] type) is used as default
/// value
fn tt() -> Expr {
    Expr::LocalVar("tt".to_string())
}

fn pure(e: Expr) -> Stmt {
    Stmt::Expr(Box::new(Expr::Pure(Box::new(e))))
}

fn monadic_let_in_stmt(
    fresh_vars: FreshVars,
    e1: Stmt,
    f: impl FnOnce(FreshVars, Expr) -> (Stmt, FreshVars),
) -> (Stmt, FreshVars) {
    match e1 {
        Stmt::Expr(e) => match *e {
            Expr::Pure(e) => f(fresh_vars, *e),
            _ => {
                let (var_name, fresh_vars) = fresh_vars.next();
                let (body, fresh_vars) = f(fresh_vars, Expr::LocalVar(var_name.clone()));
                (
                    Stmt::Let {
                        is_monadic: true,
                        pattern: Box::new(Pattern::Variable(var_name)),
                        init: e,
                        body: Box::new(body),
                    },
                    fresh_vars,
                )
            }
        },
        Stmt::Let {
            is_monadic,
            pattern,
            init,
            body,
        } => {
            let (body, fresh_vars) = monadic_let_in_stmt(fresh_vars, *body, f);
            (
                Stmt::Let {
                    is_monadic,
                    pattern,
                    init,
                    body: Box::new(body),
                },
                fresh_vars,
            )
        }
    }
}

fn monadic_let(
    fresh_vars: FreshVars,
    e1: Expr,
    f: impl FnOnce(FreshVars, Expr) -> (Stmt, FreshVars),
) -> (Stmt, FreshVars) {
    let (e1, fresh_vars) = mt_expression(fresh_vars, e1);
    monadic_let_in_stmt(fresh_vars, e1, f)
}

fn monadic_optional_let(
    fresh_vars: FreshVars,
    e1: Option<Box<Expr>>,
    f: impl FnOnce(FreshVars, Option<Box<Expr>>) -> (Stmt, FreshVars),
) -> (Stmt, FreshVars) {
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
    f: Box<dyn FnOnce(FreshVars, Vec<Expr>) -> (Stmt, FreshVars)>,
) -> (Stmt, FreshVars) {
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

// @TODO finish the translation logic
/// Monadic translation of an expression
///
/// The convention is to do transformation in a deep first fashion, so
/// all functions dealing with monadic translation expect that their
/// arguments already have been transformed. Not respecting this rule
/// may lead to infinite loops because of the mutual recursion between
/// the functions. In practice this means translating every subexpression
/// before translating the expression itself.
pub(crate) fn mt_expression(fresh_vars: FreshVars, expr: Expr) -> (Stmt, FreshVars) {
    match expr {
        Expr::Pure(_) => panic!("Expressions should not be monadic yet."),
        Expr::LocalVar(_) => (pure(expr), fresh_vars),
        Expr::Var(_) => (pure(expr), fresh_vars),
        Expr::AssociatedFunction { .. } => (pure(expr), fresh_vars),
        Expr::Literal(_) => (pure(expr), fresh_vars),
        Expr::AddrOf(e) => monadic_let(fresh_vars, *e, |fresh_vars, e| {
            (pure(Expr::AddrOf(Box::new(e))), fresh_vars)
        }),
        Expr::Call { func, args } => monadic_let(fresh_vars, *func, |fresh_vars, func| {
            monadic_lets(
                fresh_vars,
                args,
                Box::new(|fresh_vars, args| {
                    (
                        Stmt::Expr(Box::new(Expr::Call {
                            func: Box::new(func),
                            args,
                        })),
                        fresh_vars,
                    )
                }),
            )
        }),
        Expr::MethodCall { object, func, args } => {
            monadic_let(fresh_vars, *object, |fresh_vars, object| {
                monadic_lets(
                    fresh_vars,
                    args,
                    Box::new(|fresh_vars, args| {
                        (
                            Stmt::Expr(Box::new(Expr::MethodCall {
                                object: Box::new(object),
                                func,
                                args,
                            })),
                            fresh_vars,
                        )
                    }),
                )
            })
        }
        Expr::Lambda { args, body } => {
            let (body, _) = mt_expression(FreshVars::new(), *body);
            (
                pure(Expr::Lambda {
                    args,
                    body: Box::new(Expr::Block(Box::new(body))),
                }),
                fresh_vars,
            )
        }
        Expr::Cast { expr, ty } => monadic_let(fresh_vars, *expr, |fresh_vars, expr| {
            (
                pure(Expr::Cast {
                    expr: Box::new(expr),
                    ty,
                }),
                fresh_vars,
            )
        }),
        Expr::Type { expr, ty } => monadic_let(fresh_vars, *expr, |fresh_vars, expr| {
            (
                pure(Expr::Type {
                    expr: Box::new(expr),
                    ty,
                }),
                fresh_vars,
            )
        }),
        Expr::Array { elements } => monadic_lets(
            fresh_vars,
            elements,
            Box::new(|fresh_vars, elements| (pure(Expr::Array { elements }), fresh_vars)),
        ),
        Expr::Tuple { elements } => monadic_lets(
            fresh_vars,
            elements,
            Box::new(|fresh_vars, elements| (pure(Expr::Tuple { elements }), fresh_vars)),
        ),
        Expr::LetIf { pat, init } => monadic_let(fresh_vars, *init, |fresh_vars, init| {
            (
                Stmt::Expr(Box::new(Expr::LetIf {
                    pat,
                    init: Box::new(init),
                })),
                fresh_vars,
            )
        }),
        Expr::If {
            condition,
            success,
            failure,
        } => monadic_let(fresh_vars, *condition, |fresh_vars, condition| {
            let (success, _fresh_vars) = mt_expression(FreshVars::new(), *success);
            let (failure, _fresh_vars) = mt_expression(FreshVars::new(), *failure);
            (
                Stmt::Expr(Box::new(Expr::If {
                    condition: Box::new(condition),
                    success: Box::new(Expr::Block(Box::new(success))),
                    failure: Box::new(Expr::Block(Box::new(failure))),
                })),
                fresh_vars,
            )
        }),
        Expr::Loop { body, loop_source } => {
            let body = mt_stmt(*body);
            (
                Stmt::Expr(Box::new(Expr::Loop {
                    body: Box::new(body),
                    loop_source,
                })),
                fresh_vars,
            )
        }
        Expr::Match { scrutinee, arms } => {
            monadic_let(fresh_vars, *scrutinee, |fresh_vars, scrutinee| {
                (
                    Stmt::Expr(Box::new(Expr::Match {
                        scrutinee: Box::new(scrutinee),
                        arms: arms
                            .iter()
                            .map(|MatchArm { pat, body }| {
                                let (body, _fresh_vars) =
                                    mt_expression(FreshVars::new(), body.clone());
                                MatchArm {
                                    pat: pat.clone(),
                                    body: Expr::Block(Box::new(body)),
                                }
                            })
                            .collect(),
                    })),
                    fresh_vars,
                )
            })
        }
        Expr::Block(stmt) => (mt_stmt(*stmt), fresh_vars),
        Expr::Assign { left, right } => monadic_let(fresh_vars, *right, |fresh_vars, right| {
            (
                Stmt::Expr(Box::new(Expr::Assign {
                    left,
                    right: Box::new(right),
                })),
                fresh_vars,
            )
        }),
        Expr::IndexedField { base, index } => monadic_let(fresh_vars, *base, |fresh_vars, base| {
            (
                pure(Expr::IndexedField {
                    base: Box::new(base),
                    index,
                }),
                fresh_vars,
            )
        }),
        Expr::NamedField { base, name } => monadic_let(fresh_vars, *base, |fresh_vars, base| {
            (
                pure(Expr::NamedField {
                    base: Box::new(base),
                    name,
                }),
                fresh_vars,
            )
        }),
        Expr::Index { base, index } => monadic_let(fresh_vars, *base, |fresh_vars, base| {
            (
                pure(Expr::Index {
                    base: Box::new(base),
                    index,
                }),
                fresh_vars,
            )
        }),
        Expr::StructStruct {
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
                    monadic_optional_let(fresh_vars, base, move |fresh_vars, base| {
                        let fields_names: Vec<String> =
                            fields.iter().map(|(name, _)| name.clone()).collect();
                        (
                            pure(Expr::StructStruct {
                                path,
                                fields: fields_names
                                    .iter()
                                    .zip(fields_values.iter())
                                    .map(|(name, value)| (name.clone(), value.clone()))
                                    .collect(),
                                base,
                                struct_or_variant,
                            }),
                            fresh_vars,
                        )
                    })
                }),
            )
        }
        Expr::StructTuple {
            path,
            fields,
            struct_or_variant,
        } => monadic_lets(
            fresh_vars,
            fields,
            Box::new(|fresh_vars, fields| {
                (
                    pure(Expr::StructTuple {
                        path,
                        fields,
                        struct_or_variant,
                    }),
                    fresh_vars,
                )
            }),
        ),
        Expr::StructUnit { .. } => (pure(expr), fresh_vars),
    }
}

/// Get the pure part of a statement, if possible, as a statement.
fn get_pure_from_stmt_as_stmt(statement: Stmt) -> Option<Box<Stmt>> {
    match statement {
        Stmt::Expr(e) => match *e {
            Expr::Pure(e) => Some(Box::new(Stmt::Expr(e))),
            _ => None,
        },
        Stmt::Let {
            is_monadic: true, ..
        } => None,
        Stmt::Let {
            is_monadic: false,
            pattern,
            init,
            body,
        } => get_pure_from_stmt_as_stmt(*body).map(|body| {
            Box::new(Stmt::Let {
                is_monadic: false,
                pattern,
                init,
                body,
            })
        }),
    }
}

fn get_pure_from_stmt_as_expr(statement: Stmt) -> Option<Box<Expr>> {
    get_pure_from_stmt_as_stmt(statement).map(|statement| Box::new(Expr::Block(statement)))
}

fn mt_stmt(stmt: Stmt) -> Stmt {
    match stmt {
        Stmt::Expr(e) => mt_expression(FreshVars::new(), *e).0,
        Stmt::Let {
            is_monadic,
            pattern,
            init,
            body,
        } => {
            if is_monadic {
                panic!("The let statement should not be monadic yet.")
            }
            let (init, _fresh_vars) = mt_expression(FreshVars::new(), *init);
            let body = Box::new(mt_stmt(*body));
            let pure_init: Option<Box<Expr>> = get_pure_from_stmt_as_expr(init.clone());
            match pure_init {
                Some(pure_init) => Stmt::Let {
                    is_monadic: false,
                    pattern,
                    init: pure_init,
                    body,
                },
                None => Stmt::Let {
                    is_monadic: true,
                    pattern,
                    init: Box::new(Expr::Block(Box::new(init))),
                    body,
                },
            }
        }
    }
}

pub(crate) fn compile_expr(env: &mut Env, expr: &rustc_hir::Expr) -> Expr {
    match &expr.kind {
        ExprKind::ConstBlock(_anon_const) => Expr::LocalVar("ConstBlock".to_string()),
        ExprKind::Array(elements) => {
            let elements = elements
                .iter()
                .map(|expr| compile_expr(env, expr))
                .collect();
            Expr::Array { elements }
        }
        ExprKind::Call(func, args) => {
            let args = args.iter().map(|expr| compile_expr(env, expr)).collect();
            match func.kind {
                // Check if we are calling a constructor
                ExprKind::Path(
                    qpath @ rustc_hir::QPath::Resolved(
                        _,
                        path @ rustc_hir::Path {
                            res:
                                rustc_hir::def::Res::Def(
                                    rustc_hir::def::DefKind::Ctor(
                                        rustc_hir::def::CtorOf::Struct
                                        | rustc_hir::def::CtorOf::Variant,
                                        _,
                                    ),
                                    _,
                                ),
                            ..
                        },
                    ),
                ) => Expr::StructTuple {
                    path: compile_path(env, path),
                    fields: args,
                    struct_or_variant: StructOrVariant::of_qpath(env, &qpath),
                },
                _ => {
                    let func = Box::new(compile_expr(env, func));
                    Expr::Call { func, args }
                }
            }
        }
        ExprKind::MethodCall(path_segment, object, args, _) => {
            let object = compile_expr(env, object);
            let func = path_segment.ident.to_string();
            let args: Vec<_> = args.iter().map(|expr| compile_expr(env, expr)).collect();
            Expr::MethodCall {
                object: Box::new(object),
                func,
                args,
            }
        }
        ExprKind::Tup(elements) => {
            let elements = elements
                .iter()
                .map(|expr| compile_expr(env, expr))
                .collect();
            Expr::Tuple { elements }
        }
        ExprKind::Binary(bin_op, expr_left, expr_right) => {
            let expr_left = compile_expr(env, expr_left);
            let expr_right = compile_expr(env, expr_right);
            let func = compile_bin_op(bin_op);
            Expr::MethodCall {
                object: Box::new(expr_left),
                func,
                args: vec![expr_right],
            }
        }
        ExprKind::Unary(un_op, expr) => {
            let expr = compile_expr(env, expr);
            let func = compile_un_op(un_op);
            Expr::MethodCall {
                object: Box::new(expr),
                func,
                args: vec![],
            }
        }
        ExprKind::Lit(lit) => Expr::Literal(lit.node.clone()),
        ExprKind::Cast(expr, ty) => Expr::Cast {
            expr: Box::new(compile_expr(env, expr)),
            ty: compile_type(env, ty),
        },
        ExprKind::Type(expr, ty) => Expr::Type {
            expr: Box::new(compile_expr(env, expr)),
            ty: compile_type(env, ty),
        },
        ExprKind::DropTemps(expr) => compile_expr(env, expr),
        ExprKind::Let(rustc_hir::Let { pat, init, .. }) => {
            let pat = compile_pattern(env, pat);
            let init = Box::new(compile_expr(env, init));
            Expr::LetIf { pat, init }
        }
        ExprKind::If(condition, success, failure) => {
            let condition = Box::new(compile_expr(env, condition));
            let success = Box::new(compile_expr(env, success));

            let failure = match failure {
                Some(expr) => Box::new(compile_expr(env, expr)),
                None => Box::new(tt()),
            };
            Expr::If {
                condition,
                success,
                failure,
            }
        }
        ExprKind::Loop(block, label, loop_source, _) => {
            if let Some(label) = label {
                env.tcx
                    .sess
                    .struct_span_warn(label.ident.span, "Labeled loops are not supported.")
                    .emit();
            }
            let body = Box::new(compile_block(env, block));
            let loop_source = compile_loop_source(loop_source);
            Expr::Loop { body, loop_source }
        }
        ExprKind::Match(scrutinee, arms, _) => {
            let scrutinee = Box::new(compile_expr(env, scrutinee));
            let arms = arms
                .iter()
                .map(|arm| {
                    let pat = compile_pattern(env, arm.pat);
                    let body = compile_expr(env, arm.body);
                    if arm.guard.is_some() {
                        env.tcx
                            .sess
                            .struct_span_warn(
                                arm.span,
                                "Guards on match branches are not supported.",
                            )
                            .help("Use standalone `if` statements instead.")
                            .emit();
                    }
                    MatchArm { pat, body }
                })
                .collect();
            Expr::Match { scrutinee, arms }
        }
        ExprKind::Closure(rustc_hir::Closure { body, .. }) => {
            let body = env.tcx.hir().body(*body);
            let args = body
                .params
                .iter()
                .map(|rustc_hir::Param { pat, .. }| compile_pattern(env, pat))
                .collect();
            let body = Box::new(compile_expr(env, body.value));
            Expr::Lambda { args, body }
        }
        ExprKind::Block(block, label) => {
            if let Some(label) = label {
                env.tcx
                    .sess
                    .struct_span_warn(label.ident.span, "Labeled blocks are not supported.")
                    .emit();
            }
            Expr::Block(Box::new(compile_block(env, block)))
        }
        ExprKind::Assign(left, right, _) => {
            let left = Box::new(compile_expr(env, left));
            let right = Box::new(compile_expr(env, right));
            Expr::Assign { left, right }
        }
        ExprKind::AssignOp(bin_op, left, right) => {
            let func = compile_assign_bin_op(bin_op);
            let left = compile_expr(env, left);
            let right = compile_expr(env, right);
            Expr::MethodCall {
                object: Box::new(left),
                func,
                args: vec![right],
            }
        }
        ExprKind::Field(base, ident) => {
            let base = Box::new(compile_expr(env, base));
            let name = ident.name.to_string();
            let index = name.parse::<u32>();
            match index {
                Ok(index) => Expr::IndexedField { base, index },
                Err(_) => Expr::NamedField { base, name },
            }
        }
        ExprKind::Index(base, index) => {
            let base = Box::new(compile_expr(env, base));
            let index = Box::new(compile_expr(env, index));
            Expr::Index { base, index }
        }
        ExprKind::Path(qpath) => {
            // Check if the path is a constructor.
            if let rustc_hir::QPath::Resolved(_, path) = qpath {
                if let rustc_hir::def::Res::Def(
                    rustc_hir::def::DefKind::Ctor(rustc_hir::def::CtorOf::Struct, _),
                    _,
                ) = path.res
                {
                    // We consider the constructor to be a unit struct,
                    // otherwise it would be in a Call expression.
                    return Expr::StructUnit {
                        path: compile_path(env, path),
                    };
                }
            }
            compile_qpath(env, qpath)
        }
        ExprKind::AddrOf(_, _, expr) => Expr::AddrOf(Box::new(compile_expr(env, expr))),
        ExprKind::Break(_, _) => Expr::LocalVar("Break".to_string()),
        ExprKind::Continue(_) => Expr::LocalVar("Continue".to_string()),
        ExprKind::Ret(expr) => {
            let func = Box::new(Expr::LocalVar("Return".to_string()));
            let args = match expr {
                Some(expr) => vec![compile_expr(env, expr)],
                None => vec![],
            };
            Expr::Call { func, args }
        }
        ExprKind::InlineAsm(_) => Expr::LocalVar("InlineAsm".to_string()),
        ExprKind::Struct(qpath, fields, base) => {
            let path = crate::path::compile_qpath(env, qpath);
            let fields = fields
                .iter()
                .map(|rustc_hir::ExprField { ident, expr, .. }| {
                    let field = ident.name.to_string();
                    let expr = compile_expr(env, expr);
                    (field, expr)
                })
                .collect();
            let base = base.map(|expr| Box::new(compile_expr(env, expr)));
            let struct_or_variant = StructOrVariant::of_qpath(env, qpath);
            Expr::StructStruct {
                path,
                fields,
                base,
                struct_or_variant,
            }
        }
        ExprKind::Repeat(expr, _) => {
            let expr = compile_expr(env, expr);
            Expr::Call {
                func: Box::new(Expr::LocalVar("repeat".to_string())),
                args: vec![expr],
            }
        }
        ExprKind::Yield(expr, _) => {
            let expr = compile_expr(env, expr);
            Expr::Call {
                func: Box::new(Expr::LocalVar("yield".to_string())),
                args: vec![expr],
            }
        }
        ExprKind::OffsetOf(_, _) => todo!(),
        ExprKind::Err(_) => Expr::LocalVar("Err".to_string()),
    }
}

/// The function [compile_stmts] compiles rust *lists* of statements (such as
/// they are found in *blocks*) into coq-of-rust. See:
/// - https://doc.rust-lang.org/reference/expressions/block-expr.html and
///   https://doc.rust-lang.org/stable/nightly-rustc/rustc_hir/hir/struct.Block.html
/// - https://doc.rust-lang.org/reference/statements.html and
///   https://doc.rust-lang.org/stable/nightly-rustc/rustc_hir/hir/struct.Stmt.html
fn compile_stmts(env: &mut Env, stmts: &[rustc_hir::Stmt], expr: Option<&rustc_hir::Expr>) -> Stmt {
    match stmts {
        [stmt, stmts @ ..] => match stmt.kind {
            rustc_hir::StmtKind::Local(rustc_hir::Local { pat, init, .. }) => {
                let pattern = Box::new(compile_pattern(env, pat));
                let init = match init {
                    Some(init) => Box::new(compile_expr(env, init)),
                    None => Box::new(tt()),
                };
                let body = Box::new(compile_stmts(env, stmts, expr));
                Stmt::Let {
                    is_monadic: false,
                    pattern,
                    init,
                    body,
                }
            }
            // We ignore "Item" as we do not know yet how to handle them / what they are for.
            rustc_hir::StmtKind::Item(_) => compile_stmts(env, stmts, expr),
            rustc_hir::StmtKind::Expr(current_expr) | rustc_hir::StmtKind::Semi(current_expr) => {
                let first = Box::new(compile_expr(env, current_expr));
                let second = Box::new(compile_stmts(env, stmts, expr));
                Stmt::Let {
                    is_monadic: false,
                    pattern: Box::new(Pattern::Wild),
                    init: first,
                    body: second,
                }
            }
        },
        [] => Stmt::Expr(Box::new(match expr {
            Some(expr) => compile_expr(env, expr),
            None => tt(),
        })),
    }
}

/// [compile_block] compiles hir blocks into coq-of-rust
/// See the doc for [compile_stmts]
fn compile_block(env: &mut Env, block: &rustc_hir::Block) -> Stmt {
    compile_stmts(env, block.stmts, block.expr)
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

impl Expr {
    pub fn to_doc(&self, with_paren: bool) -> Doc {
        match self {
            Expr::Pure(expr) => paren(with_paren, nest([text("Pure"), line(), expr.to_doc(true)])),
            Expr::LocalVar(ref name) => text(name),
            Expr::Var(path) => path.to_doc(),
            Expr::AssociatedFunction { ty, func } => nest([
                ty.to_doc(true),
                text("::["),
                text(format!("\"{func}\"")),
                text("]"),
            ]),
            Expr::Literal(literal) => literal_to_doc(with_paren, literal),
            Expr::AddrOf(expr) => paren(
                with_paren,
                nest([text("addr_of"), line(), expr.to_doc(true)]),
            ),
            Expr::Call { func, args } => paren(
                with_paren,
                nest([
                    func.to_doc(true),
                    line(),
                    if args.is_empty() {
                        text("tt")
                    } else {
                        intersperse(args.iter().map(|arg| arg.to_doc(true)), [line()])
                    },
                ]),
            ),
            Expr::MethodCall { object, func, args } => paren(
                with_paren && !args.is_empty(),
                nest([
                    object.to_doc(true),
                    text(".["),
                    text(format!("\"{func}\"")),
                    text("]"),
                    concat(args.iter().map(|arg| concat([line(), arg.to_doc(true)]))),
                ]),
            ),
            Expr::Lambda { args, body } => paren(
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
            ),
            Expr::Cast { expr, ty } => paren(
                with_paren,
                nest([
                    text("cast"),
                    line(),
                    expr.to_doc(true),
                    line(),
                    ty.to_doc(true),
                ]),
            ),
            Expr::Type { expr, ty } => nest([
                text("("),
                expr.to_doc(true),
                line(),
                text(": "),
                ty.to_doc(true),
                text(")"),
            ]),
            Expr::Array { elements } => group([
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
            Expr::Tuple { elements } => {
                if elements.is_empty() {
                    text("tt")
                } else {
                    paren(
                        true,
                        nest([intersperse(
                            elements.iter().map(|element| element.to_doc(false)),
                            [text(","), line()],
                        )]),
                    )
                }
            }
            Expr::LetIf { pat, init } => group([
                text("let_if"),
                line(),
                pat.to_doc(),
                line(),
                text(":="),
                line(),
                init.to_doc(false),
            ]),
            Expr::If {
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
            Expr::Loop {
                body, /*loop_source*/
                ..
            } => paren(
                with_paren,
                nest([
                    //text("loop"),
                    text("while"),
                    line(),
                    paren(true, body.to_doc()),
                    /*line(),
                    text("from"),
                    line(),
                    text(loop_source),*/
                ]),
            ),
            Expr::Match { scrutinee, arms } => group([
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
            Expr::Block(stmt) => stmt.to_doc(),
            Expr::Assign { left, right } => paren(
                with_paren,
                nest([
                    text("assign"),
                    line(),
                    left.to_doc(true),
                    line(),
                    right.to_doc(true),
                ]),
            ),
            Expr::IndexedField { base, index } => paren(
                with_paren,
                nest([
                    base.to_doc(true),
                    text(".["),
                    text(index.to_string()),
                    text("]"),
                ]),
            ),
            Expr::NamedField { base, name } => nest([
                base.to_doc(true),
                text(".["),
                text(format!("\"{name}\"")),
                text("]"),
            ]),
            Expr::Index { base, index } => {
                nest([base.to_doc(true), text("["), index.to_doc(false), text("]")])
            }
            Expr::StructStruct {
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
            Expr::StructTuple {
                path,
                fields,
                struct_or_variant,
            } => paren(
                with_paren,
                nest([
                    path.to_doc(),
                    match struct_or_variant {
                        StructOrVariant::Struct => text(".Build_t"),
                        StructOrVariant::Variant => nil(),
                    },
                    line(),
                    if fields.is_empty() {
                        text("tt")
                    } else {
                        intersperse(fields.iter().map(|arg| arg.to_doc(true)), [line()])
                    },
                ]),
            ),
            Expr::StructUnit { path } => nest([path.to_doc(), text(".Build")]),
        }
    }
}

impl Stmt {
    fn to_doc(&self) -> Doc {
        match self {
            Stmt::Expr(expr) => expr.to_doc(false),
            Stmt::Let {
                is_monadic,
                pattern,
                init,
                body,
            } => group([
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
                        pattern.to_doc(),
                        text(" :="),
                    ]),
                    line(),
                    init.to_doc(false),
                    text(" in"),
                ]),
                hardline(),
                body.to_doc(),
            ]),
        }
    }
}
