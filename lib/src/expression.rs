use core::panic;

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

/// Enum [Expr] represents the AST of rust terms.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) enum Expr {
    Pure(Box<Expr>),
    LocalVar(String),
    Var(Path),
    VarWithSelfTy {
        path: Path,
        self_ty: Box<CoqType>,
    },
    AssociatedFunction {
        ty: Box<CoqType>,
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
    TypeAnnotation {
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
        pat: Box<Pattern>,
        init: Box<Expr>,
    },
    If {
        condition: Box<Expr>,
        success: Box<Expr>,
        failure: Box<Expr>,
    },
    Loop {
        body: Box<Stmt>,
    },
    Match {
        scrutinee: Box<Expr>,
        arms: Vec<MatchArm>,
    },
    Block(Box<Stmt>),
    #[allow(dead_code)]
    Assign {
        left: Box<Expr>,
        right: Box<Expr>,
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
    /// Sometimes type expressions appear as parameter to special operators
    Type(Box<CoqType>),
    /// Useful for error messages or annotations
    Message(String),
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) enum Stmt {
    Expr(Box<Expr>),
    Let {
        is_monadic: bool,
        pattern: Box<Pattern>,
        /// Optional type annotation to avoid type inference errors (should be None for monadic lets)
        ty: Option<Box<CoqType>>,
        init: Box<Expr>,
        body: Box<Stmt>,
    },
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

/// The Coq value [tt] (the inhabitant of the [unit] type) is used as default
/// value
pub(crate) fn tt() -> Expr {
    Expr::Call {
        func: Box::new(Expr::LocalVar("M.alloc".to_string())),
        args: vec![Expr::LocalVar("tt".to_string())],
    }
}

fn pure(e: Expr) -> Stmt {
    Stmt::Expr(Box::new(Expr::Pure(Box::new(e))))
}

/// creates a monadic let statement with [e1] as the initializer
/// and the result of [f] as the body
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
                        ty: None,
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
            ty,
            init,
            body,
        } => {
            let (body, fresh_vars) = monadic_let_in_stmt(fresh_vars, *body, f);
            (
                Stmt::Let {
                    is_monadic,
                    pattern,
                    ty,
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
pub(crate) fn mt_expression(fresh_vars: FreshVars, expr: Expr) -> (Stmt, FreshVars) {
    match expr {
        Expr::Pure(_) => panic!("Expressions should not be monadic yet."),
        Expr::LocalVar(_) => (pure(expr), fresh_vars),
        Expr::Var(_) => (pure(expr), fresh_vars),
        Expr::VarWithSelfTy { path, self_ty } => (
            pure(Expr::VarWithSelfTy {
                path,
                self_ty: mt_ty(self_ty),
            }),
            fresh_vars,
        ),
        Expr::AssociatedFunction { .. } => (pure(expr), fresh_vars),
        Expr::Literal { ref literal, .. } => (
            if is_literal_pure(literal) {
                pure(expr)
            } else {
                Stmt::Expr(Box::new(expr))
            },
            fresh_vars,
        ),
        Expr::NonHirLiteral { .. } => (pure(expr), fresh_vars),
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
        Expr::MonadicOperator { name, arg } => {
            let (arg, fresh_vars) = mt_expression(fresh_vars, *arg);
            (
                Stmt::Expr(Box::new(Expr::MonadicOperator {
                    name,
                    arg: Box::new(Expr::Block(Box::new(arg))),
                })),
                fresh_vars,
            )
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
        Expr::TypeAnnotation { expr, ty } => monadic_let(fresh_vars, *expr, |fresh_vars, expr| {
            (
                pure(Expr::TypeAnnotation {
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
        Expr::Loop { body, .. } => {
            let body = mt_stmt(*body);
            (
                Stmt::Expr(Box::new(Expr::Loop {
                    body: Box::new(body),
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
        Expr::Assign { left, right } => monadic_let(fresh_vars, *left, |fresh_vars, left| {
            monadic_let(fresh_vars, *right, |fresh_vars, right| {
                (
                    Stmt::Expr(Box::new(Expr::Assign {
                        left: Box::new(left),
                        right: Box::new(right),
                    })),
                    fresh_vars,
                )
            })
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
                Stmt::Expr(Box::new(Expr::NamedField {
                    base: Box::new(base),
                    name,
                })),
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
        // control flow expressions are responsible for side effects, so they are monadic already
        Expr::ControlFlow(lcf_expression) => (
            Stmt::Expr(Box::new(Expr::ControlFlow(lcf_expression))),
            fresh_vars,
        ),
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
        Expr::Type(_) => (pure(expr), fresh_vars),
        Expr::Message(_) => (pure(expr), fresh_vars),
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
            ty,
            init,
            body,
        } => get_pure_from_stmt_as_stmt(*body).map(|body| {
            Box::new(Stmt::Let {
                is_monadic: false,
                pattern,
                ty,
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
            ty,
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
                    ty,
                    init: pure_init,
                    body,
                },
                None => Stmt::Let {
                    is_monadic: true,
                    pattern,
                    // type annotations do not work in monadic let
                    ty: None,
                    init: Box::new(Expr::Block(Box::new(init))),
                    body,
                },
            }
        }
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
    pub fn to_doc(&self, with_paren: bool) -> Doc {
        match self {
            Expr::Pure(expr) => paren(
                with_paren,
                nest([text("M.pure"), line(), expr.to_doc(true)]),
            ),
            Expr::LocalVar(ref name) => text(name),
            Expr::Var(path) => path.to_doc(),
            Expr::VarWithSelfTy { path, self_ty } => paren(
                with_paren,
                nest([
                    path.to_doc(),
                    line(),
                    nest([text("(Self :="), line(), self_ty.to_doc(false), text(")")]),
                    line(),
                    nest([
                        text("(Trait :="),
                        line(),
                        text("ltac:(refine _)"),
                        text(")"),
                    ]),
                ]),
            ),
            Expr::AssociatedFunction { ty, func } => nest([
                ty.to_doc(true),
                text("::["),
                text(format!("\"{func}\"")),
                text("]"),
            ]),
            Expr::Literal { literal, neg } => literal_to_doc(with_paren, literal, *neg),
            Expr::NonHirLiteral(literal) => text(literal.to_string()),
            Expr::Call { func, args } => {
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
            Expr::MonadicOperator { name, arg } => {
                paren(with_paren, nest([text(name), line(), arg.to_doc(true)]))
            }
            Expr::Lambda { args, body } => {
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
            Expr::TypeAnnotation { expr, ty } => nest([
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
            Expr::Tuple { elements } => paren(
                true,
                nest([intersperse(
                    elements.iter().map(|element| element.to_doc(false)),
                    [text(","), line()],
                )]),
            ),
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
                nest([text("loop"), line(), paren(true, body.to_doc(with_paren))]),
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
            Expr::Block(stmt) => stmt.to_doc(with_paren),
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
            Expr::ControlFlow(lcf_expression) => lcf_expression.to_doc(),
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
            Expr::StructUnit { path } => nest([path.to_doc(), text(".Build")]),
            Expr::Type(ty) => ty.to_doc(with_paren),
            Expr::Message(message) => text(format!("\"{message}\"")),
        }
    }
}

impl Stmt {
    fn to_doc(&self, with_paren: bool) -> Doc {
        match self {
            Stmt::Expr(expr) => expr.to_doc(with_paren),
            Stmt::Let {
                is_monadic,
                pattern,
                ty,
                init,
                body,
            } => paren(
                with_paren,
                group([
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
                            match ty {
                                Some(ty) => concat([text(" :"), line(), ty.to_doc(false)]),
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
        }
    }
}
