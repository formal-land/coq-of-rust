use crate::path::*;
use crate::pattern::*;
use crate::render::*;
use crate::ty::*;

use rustc_ast::LitKind;
use rustc_hir::def::{CtorOf, DefKind, Res};
use rustc_hir::{BinOp, BinOpKind, ExprKind, QPath};
use rustc_middle::ty::TyCtxt;

/// Struct [MatchArm] represents a pattern-matching branch: [pat] is the
/// matched pattern and [body] the expression on which it is mapped
#[derive(Debug)]
pub struct MatchArm {
    pat: Pattern,
    body: Expr,
}

/// Enum [Expr] represents the AST of rust terms.
#[derive(Debug)]
pub(crate) enum Expr {
    LocalVar(String),
    Var(Path),
    AssociatedFunction {
        ty: Box<CoqType>,
        func: String,
    },
    Literal(LitKind),
    AddrOf(Box<Expr>),
    Call {
        monadic: bool,
        func: Box<Expr>,
        args: Vec<Expr>,
    },
    Member {
        object: Box<Expr>,
        member: String,
    },
    Let {
        pat: Pattern,
        init: Box<Expr>,
        body: Box<Expr>,
    },
    Sequence {
        first: Box<Expr>,
        second: Box<Expr>,
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
        body: Box<Expr>,
        loop_source: String,
    },
    Match {
        scrutinee: Box<Expr>,
        arms: Vec<MatchArm>,
    },
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

fn compile_qpath(tcx: &TyCtxt, qpath: &QPath) -> Expr {
    match qpath {
        QPath::Resolved(_, path) => Expr::Var(compile_path(path)),
        QPath::TypeRelative(ty, segment) => {
            let ty = Box::new(compile_type(tcx, ty));
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

pub(crate) fn compile_expr(tcx: TyCtxt, expr: &rustc_hir::Expr) -> Expr {
    match &expr.kind {
        ExprKind::ConstBlock(_anon_const) => Expr::LocalVar("ConstBlock".to_string()),
        ExprKind::Array(elements) => {
            let elements = elements
                .iter()
                .map(|expr| compile_expr(tcx, expr))
                .collect();
            Expr::Array { elements }
        }
        ExprKind::Call(func, args) => {
            let args = args.iter().map(|expr| compile_expr(tcx, expr)).collect();
            match func.kind {
                // Check if we are calling the constructor of a struct
                ExprKind::Path(QPath::Resolved(
                    _,
                    path @ rustc_hir::Path {
                        res: Res::Def(DefKind::Ctor(CtorOf::Struct, _), _),
                        ..
                    },
                )) => Expr::StructTuple {
                    path: compile_path(path),
                    fields: args,
                    struct_or_variant: StructOrVariant::Struct,
                },
                // Check if we are calling the constructor of a variant
                ExprKind::Path(QPath::Resolved(
                    _,
                    path @ rustc_hir::Path {
                        res: Res::Def(DefKind::Ctor(CtorOf::Variant, _), _),
                        ..
                    },
                )) => Expr::StructTuple {
                    path: compile_path(path),
                    fields: args,
                    struct_or_variant: StructOrVariant::Variant,
                },
                _ => {
                    let func = Box::new(compile_expr(tcx, func));
                    Expr::Call {
                        monadic: true,
                        func,
                        args,
                    }
                }
            }
        }
        ExprKind::MethodCall(path_segment, object, args, _) => {
            let object = compile_expr(tcx, object);
            let func = path_segment.ident.to_string();
            let args: Vec<_> = args.iter().map(|expr| compile_expr(tcx, expr)).collect();
            Expr::Call {
                monadic: true,
                func: Box::new(Expr::Member {
                    object: Box::new(object),
                    member: func,
                }),
                args,
            }
        }
        ExprKind::Tup(elements) => {
            let elements = elements
                .iter()
                .map(|expr| compile_expr(tcx, expr))
                .collect();
            Expr::Tuple { elements }
        }
        ExprKind::Binary(bin_op, expr_left, expr_right) => {
            let expr_left = compile_expr(tcx, expr_left);
            let expr_right = compile_expr(tcx, expr_right);
            let func = compile_bin_op(bin_op);
            Expr::Call {
                monadic: true,
                func: Box::new(Expr::Member {
                    object: Box::new(expr_left),
                    member: func,
                }),
                args: vec![expr_right],
            }
        }
        ExprKind::Unary(un_op, expr) => {
            let expr = compile_expr(tcx, expr);
            let func = compile_un_op(un_op);
            Expr::Call {
                monadic: true,
                func: Box::new(Expr::Member {
                    object: Box::new(expr),
                    member: func,
                }),
                args: vec![],
            }
        }
        ExprKind::Lit(lit) => Expr::Literal(lit.node.clone()),
        ExprKind::Cast(expr, ty) => Expr::Cast {
            expr: Box::new(compile_expr(tcx, expr)),
            ty: Box::new(compile_type(&tcx, ty)),
        },
        ExprKind::Type(expr, ty) => Expr::Type {
            expr: Box::new(compile_expr(tcx, expr)),
            ty: Box::new(compile_type(&tcx, ty)),
        },
        ExprKind::DropTemps(expr) => compile_expr(tcx, expr),
        ExprKind::Let(rustc_hir::Let { pat, init, .. }) => {
            let pat = compile_pattern(&tcx, pat);
            let init = Box::new(compile_expr(tcx, init));
            Expr::LetIf { pat, init }
        }
        ExprKind::If(condition, success, failure) => {
            let condition = Box::new(compile_expr(tcx, condition));
            let success = Box::new(compile_expr(tcx, success));
            let failure = match failure {
                Some(expr) => Box::new(compile_expr(tcx, expr)),
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
                tcx.sess
                    .struct_span_warn(label.ident.span, "Labeled loops are not supported.")
                    .emit();
            }
            let body = Box::new(compile_block(tcx, block));
            let loop_source = compile_loop_source(loop_source);
            Expr::Loop { body, loop_source }
        }
        ExprKind::Match(scrutinee, arms, _) => {
            let scrutinee = Box::new(compile_expr(tcx, scrutinee));
            let arms = arms
                .iter()
                .map(|arm| {
                    let pat = compile_pattern(&tcx, arm.pat);
                    let body = compile_expr(tcx, arm.body);
                    if arm.guard.is_some() {
                        tcx.sess
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
            let body = tcx.hir().body(*body);
            let args = body
                .params
                .iter()
                .map(|rustc_hir::Param { pat, .. }| compile_pattern(&tcx, pat))
                .collect();
            let body = Box::new(compile_expr(tcx, body.value));
            Expr::Lambda { args, body }
        }
        ExprKind::Block(block, label) => {
            if let Some(label) = label {
                tcx.sess
                    .struct_span_warn(label.ident.span, "Labeled blocks are not supported.")
                    .emit();
            }
            compile_block(tcx, block)
        }
        ExprKind::Assign(left, right, _) => {
            let left = Box::new(compile_expr(tcx, left));
            let right = Box::new(compile_expr(tcx, right));
            Expr::Assign { left, right }
        }
        ExprKind::AssignOp(bin_op, left, right) => {
            let func = compile_assign_bin_op(bin_op);
            let left = compile_expr(tcx, left);
            let right = compile_expr(tcx, right);
            Expr::Call {
                monadic: true,
                func: Box::new(Expr::Member {
                    object: Box::new(left),
                    member: func,
                }),
                args: vec![right],
            }
        }
        ExprKind::Field(base, ident) => {
            let base = Box::new(compile_expr(tcx, base));
            let name = ident.name.to_string();
            let index = name.parse::<u32>();
            match index {
                Ok(index) => Expr::IndexedField { base, index },
                Err(_) => Expr::NamedField { base, name },
            }
        }
        ExprKind::Index(base, index) => {
            let base = Box::new(compile_expr(tcx, base));
            let index = Box::new(compile_expr(tcx, index));
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
                        path: compile_path(path),
                    };
                }
            }
            compile_qpath(&tcx, qpath)
        }
        ExprKind::AddrOf(_, _, expr) => Expr::AddrOf(Box::new(compile_expr(tcx, expr))),
        ExprKind::Break(_, _) => Expr::LocalVar("M.Break".to_string()),
        ExprKind::Continue(_) => Expr::LocalVar("M.Continue".to_string()),
        ExprKind::Ret(expr) => {
            let func = Box::new(Expr::LocalVar("M.Return".to_string()));
            let args = vec![match expr {
                Some(expr) => compile_expr(tcx, expr),
                None => tt(),
            }];
            Expr::Call {
                monadic: false,
                func,
                args,
            }
        }
        ExprKind::InlineAsm(_) => Expr::LocalVar("InlineAsm".to_string()),
        ExprKind::Struct(qpath, fields, base) => {
            let path = crate::path::compile_qpath(qpath);
            let fields = fields
                .iter()
                .map(|rustc_hir::ExprField { ident, expr, .. }| {
                    let field = ident.name.to_string();
                    let expr = compile_expr(tcx, expr);
                    (field, expr)
                })
                .collect();
            let base = base.map(|expr| Box::new(compile_expr(tcx, expr)));
            let struct_or_variant = StructOrVariant::of_qpath(&tcx, qpath);
            Expr::StructStruct {
                path,
                fields,
                base,
                struct_or_variant,
            }
        }
        ExprKind::Repeat(expr, _) => {
            let expr = compile_expr(tcx, expr);
            Expr::Call {
                monadic: false,
                func: Box::new(Expr::LocalVar("Repeat".to_string())),
                args: vec![expr],
            }
        }
        ExprKind::Yield(expr, _) => {
            let expr = compile_expr(tcx, expr);
            Expr::Call {
                monadic: false,
                func: Box::new(Expr::LocalVar("Yield".to_string())),
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
fn compile_stmts(tcx: TyCtxt, stmts: &[rustc_hir::Stmt], expr: Option<&rustc_hir::Expr>) -> Expr {
    match stmts {
        [stmt, stmts @ ..] => match stmt.kind {
            rustc_hir::StmtKind::Local(rustc_hir::Local { pat, init, .. }) => {
                let pat = compile_pattern(&tcx, pat);
                let init = match init {
                    Some(init) => Box::new(compile_expr(tcx, init)),
                    None => Box::new(tt()),
                };
                let body = Box::new(compile_stmts(tcx, stmts, expr));
                Expr::Let { pat, init, body }
            }
            // We ignore "Item" as we do not know yet how to handle them / what they are for.
            rustc_hir::StmtKind::Item(_) => compile_stmts(tcx, stmts, expr),
            rustc_hir::StmtKind::Expr(current_expr) | rustc_hir::StmtKind::Semi(current_expr) => {
                let first = Box::new(compile_expr(tcx, current_expr));
                let second = Box::new(compile_stmts(tcx, stmts, expr));
                Expr::Sequence { first, second }
            }
        },
        [] => match expr {
            Some(expr) => compile_expr(tcx, expr),
            None => tt(),
        },
    }
}

/// [compile_block] compiles hir blocks into coq-of-rust
/// See the doc for [compile_stmts]
fn compile_block(tcx: TyCtxt, block: &rustc_hir::Block) -> Expr {
    compile_stmts(tcx, block.stmts, block.expr)
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
            Expr::LocalVar(ref name) => text(name),
            Expr::Var(path) => path.to_doc(),
            Expr::AssociatedFunction { ty, func } => nest([
                ty.to_doc(true),
                text("::["),
                text(format!("\"{func}\"")),
                text("]"),
            ]),
            Expr::Literal(literal) => literal_to_doc(with_paren, literal),
            Expr::AddrOf(expr) => expr.to_doc(with_paren),
            Expr::Call {
                monadic,
                func,
                args,
            } => {
                if *monadic {
                    group([
                        func.to_doc(true),
                        if args.is_empty() {
                            text("(||)")
                        } else {
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
                            ])
                        },
                    ])
                } else {
                    paren(
                        with_paren,
                        nest([
                            func.to_doc(true),
                            line(),
                            intersperse(args.iter().map(|arg| arg.to_doc(true)), [line()]),
                        ]),
                    )
                }
            }
            Expr::Member { object, member } => concat([
                object.to_doc(true),
                text(".["),
                text(format!("\"{member}\"")),
                text("]"),
            ]),
            Expr::Let { pat, init, body } => group([
                nest([
                    nest([
                        text("let"),
                        line(),
                        group([
                            (if !pat.is_single_binding() {
                                text("'")
                            } else {
                                nil()
                            }),
                            pat.to_doc(),
                            line(),
                            text(":="),
                        ]),
                    ]),
                    line(),
                    group([init.to_doc(false), text(" in")]),
                ]),
                hardline(),
                body.to_doc(false),
            ]),
            Expr::Sequence { first, second } => group([
                nest([
                    text("let _ : unit :="),
                    line(),
                    first.to_doc(false),
                    text(" in"),
                ]),
                hardline(),
                second.to_doc(false),
            ]),
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
            Expr::Loop { body, loop_source } => paren(
                with_paren,
                nest([
                    text("loop"),
                    line(),
                    body.to_doc(true),
                    line(),
                    text("from"),
                    line(),
                    text(loop_source),
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
