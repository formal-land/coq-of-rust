extern crate rustc_ast;
extern crate rustc_hir;
extern crate rustc_middle;

use crate::path::*;
use crate::pattern::*;
use crate::render::*;
use pretty::RcDoc;

/// Struct [MatchArm] represents a pattern-matching branch: [pat] is the
/// matched pattern and [body] the expression on which it is mapped
#[derive(Debug)]
pub struct MatchArm {
    pat: Pattern,
    body: Expr,
}

/// Enum [Expr] represents the AST of rust terms.
#[derive(Debug)]
pub enum Expr {
    LocalVar(String),
    Var(Path),
    Literal(rustc_ast::LitKind),
    Call {
        func: Box<Expr>,
        args: Vec<Expr>,
    },
    Let {
        pat: Pattern,
        init: Box<Expr>,
        body: Box<Expr>,
    },
    Lambda {
        args: Vec<Pattern>,
        body: Box<Expr>,
    },
    Seq {
        first: Box<Expr>,
        second: Box<Expr>,
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
    AssignOp {
        bin_op: String,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Field {
        base: Box<Expr>,
        field: String,
    },
    Index {
        base: Box<Expr>,
        index: Box<Expr>,
    },
    Struct {
        path: Path,
        fields: Vec<(String, Expr)>,
        base: Option<Box<Expr>>,
    },
}

/// The function [compile_bin_op] converts a hir binary operator to a
/// string
fn compile_bin_op(bin_op: &rustc_hir::BinOp) -> String {
    match bin_op.node {
        rustc_hir::BinOpKind::Add => "add".to_string(),
        rustc_hir::BinOpKind::Sub => "sub".to_string(),
        rustc_hir::BinOpKind::Mul => "mul".to_string(),
        rustc_hir::BinOpKind::Div => "div".to_string(),
        rustc_hir::BinOpKind::Rem => "rem".to_string(),
        rustc_hir::BinOpKind::And => "and".to_string(),
        rustc_hir::BinOpKind::Or => "or".to_string(),
        rustc_hir::BinOpKind::BitXor => "bit_xor".to_string(),
        rustc_hir::BinOpKind::BitAnd => "bit_and".to_string(),
        rustc_hir::BinOpKind::BitOr => "bit_and".to_string(),
        rustc_hir::BinOpKind::Shl => "shl".to_string(),
        rustc_hir::BinOpKind::Shr => "shr".to_string(),
        rustc_hir::BinOpKind::Eq => "eq".to_string(),
        rustc_hir::BinOpKind::Lt => "lt".to_string(),
        rustc_hir::BinOpKind::Le => "le".to_string(),
        rustc_hir::BinOpKind::Ne => "ne".to_string(),
        rustc_hir::BinOpKind::Ge => "ge".to_string(),
        rustc_hir::BinOpKind::Gt => "gt".to_string(),
    }
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

/// The Coq value [tt] (the inhabitant of the [unit] type) is used as default
/// value
fn tt() -> Expr {
    Expr::LocalVar("tt".to_string())
}

pub fn compile_expr(hir: rustc_middle::hir::map::Map, expr: &rustc_hir::Expr) -> Expr {
    match &expr.kind {
        rustc_hir::ExprKind::Box(expr) => compile_expr(hir, expr),
        rustc_hir::ExprKind::ConstBlock(_anon_const) => Expr::LocalVar("ConstBlock".to_string()),
        rustc_hir::ExprKind::Array(elements) => {
            let elements = elements
                .iter()
                .map(|expr| compile_expr(hir, expr))
                .collect();
            Expr::Array { elements }
        }
        rustc_hir::ExprKind::Call(func, args) => {
            let func = Box::new(compile_expr(hir, func));
            let args = args.iter().map(|expr| compile_expr(hir, expr)).collect();
            Expr::Call { func, args }
        }
        rustc_hir::ExprKind::MethodCall(path_segment, object, args, _) => {
            let func = Box::new(Expr::Var(Path::local(path_segment.ident.to_string())));
            let mut object_with_args = vec![compile_expr(hir, object)];
            let args: Vec<_> = args.iter().map(|expr| compile_expr(hir, expr)).collect();
            object_with_args.extend(args);
            Expr::Call {
                func,
                args: object_with_args,
            }
        }
        rustc_hir::ExprKind::Tup(elements) => {
            let elements = elements
                .iter()
                .map(|expr| compile_expr(hir, expr))
                .collect();
            Expr::Tuple { elements }
        }
        rustc_hir::ExprKind::Binary(bin_op, expr_left, expr_right) => {
            let expr_left = compile_expr(hir, expr_left);
            let expr_right = compile_expr(hir, expr_right);
            let func = Box::new(Expr::LocalVar(compile_bin_op(bin_op)));
            Expr::Call {
                func,
                args: vec![expr_left, expr_right],
            }
        }
        rustc_hir::ExprKind::Unary(un_op, expr) => {
            let expr = compile_expr(hir, expr);
            let func = Box::new(Expr::LocalVar(compile_un_op(un_op)));
            Expr::Call {
                func,
                args: vec![expr],
            }
        }
        rustc_hir::ExprKind::Lit(lit) => Expr::Literal(lit.node.clone()),
        rustc_hir::ExprKind::Cast(expr, _ty) => compile_expr(hir, expr),
        rustc_hir::ExprKind::Type(expr, _ty) => compile_expr(hir, expr),
        rustc_hir::ExprKind::DropTemps(expr) => compile_expr(hir, expr),
        rustc_hir::ExprKind::Let(rustc_hir::Let { pat, init, .. }) => {
            let pat = compile_pattern(pat);
            let init = Box::new(compile_expr(hir, init));
            Expr::LetIf { pat, init }
        }
        rustc_hir::ExprKind::If(condition, success, failure) => {
            let condition = Box::new(compile_expr(hir, condition));
            let success = Box::new(compile_expr(hir, success));
            let failure = match failure {
                Some(expr) => Box::new(compile_expr(hir, expr)),
                None => Box::new(tt()),
            };
            Expr::If {
                condition,
                success,
                failure,
            }
        }
        rustc_hir::ExprKind::Loop(block, _, loop_source, _) => {
            let body = Box::new(compile_block(hir, block));
            let loop_source = compile_loop_source(loop_source);
            Expr::Loop { body, loop_source }
        }
        rustc_hir::ExprKind::Match(scrutinee, arms, _) => {
            let scrutinee = Box::new(compile_expr(hir, scrutinee));
            let arms = arms
                .iter()
                .map(|arm| {
                    let pat = compile_pattern(arm.pat);
                    let body = compile_expr(hir, arm.body);
                    MatchArm { pat, body }
                })
                .collect();
            Expr::Match { scrutinee, arms }
        }
        rustc_hir::ExprKind::Closure(rustc_hir::Closure { body, .. }) => {
            let body = hir.body(*body);
            let args = body
                .params
                .iter()
                .map(|rustc_hir::Param { pat, .. }| compile_pattern(pat))
                .collect();
            let body = Box::new(compile_expr(hir, body.value));
            Expr::Lambda { args, body }
        }
        rustc_hir::ExprKind::Block(block, _) => compile_block(hir, block),
        rustc_hir::ExprKind::Assign(left, right, _) => {
            let left = Box::new(compile_expr(hir, left));
            let right = Box::new(compile_expr(hir, right));
            Expr::Assign { left, right }
        }
        rustc_hir::ExprKind::AssignOp(bin_op, left, right) => {
            let func = Box::new(Expr::LocalVar(compile_bin_op(bin_op)));
            // We have to duplicate the code here for memory allocations
            let left_left = compile_expr(hir, left);
            let left_right = compile_expr(hir, left);
            let right = compile_expr(hir, right);
            Expr::Assign {
                left: Box::new(left_left),
                right: Box::new(Expr::Call {
                    func,
                    args: vec![left_right, right],
                }),
            }
        }
        rustc_hir::ExprKind::Field(base, ident) => {
            let base = Box::new(compile_expr(hir, base));
            let field = ident.name.to_string();
            Expr::Field { base, field }
        }
        rustc_hir::ExprKind::Index(base, index) => {
            let base = Box::new(compile_expr(hir, base));
            let index = Box::new(compile_expr(hir, index));
            Expr::Index { base, index }
        }
        rustc_hir::ExprKind::Path(qpath) => {
            let path = compile_qpath(qpath);
            Expr::Var(path)
        }
        rustc_hir::ExprKind::AddrOf(_, _, expr) => compile_expr(hir, expr),
        rustc_hir::ExprKind::Break(_, _) => Expr::LocalVar("Break".to_string()),
        rustc_hir::ExprKind::Continue(_) => Expr::LocalVar("Continue".to_string()),
        rustc_hir::ExprKind::Ret(expr) => {
            let func = Box::new(Expr::LocalVar("Return".to_string()));
            let args = match expr {
                Some(expr) => vec![compile_expr(hir, expr)],
                None => vec![],
            };
            Expr::Call { func, args }
        }
        rustc_hir::ExprKind::InlineAsm(_) => Expr::LocalVar("InlineAsm".to_string()),
        rustc_hir::ExprKind::Struct(qpath, fields, base) => {
            let path = compile_qpath(qpath);
            let fields = fields
                .iter()
                .map(|rustc_hir::ExprField { ident, expr, .. }| {
                    let field = ident.name.to_string();
                    let expr = compile_expr(hir, expr);
                    (field, expr)
                })
                .collect();
            let base = base.map(|expr| Box::new(compile_expr(hir, expr)));
            Expr::Struct { path, fields, base }
        }
        rustc_hir::ExprKind::Repeat(expr, _) => {
            let expr = compile_expr(hir, expr);
            Expr::Call {
                func: Box::new(Expr::LocalVar("repeat".to_string())),
                args: vec![expr],
            }
        }
        rustc_hir::ExprKind::Yield(expr, _) => {
            let expr = compile_expr(hir, expr);
            Expr::Call {
                func: Box::new(Expr::LocalVar("yield".to_string())),
                args: vec![expr],
            }
        }
        rustc_hir::ExprKind::Err => Expr::LocalVar("Err".to_string()),
    }
}

/// The function [compile_stmts] compiles rust *lists* of statements (such as
/// they are found in *blocks*) into coq-of-rust. See:
/// - https://doc.rust-lang.org/reference/expressions/block-expr.html and
///   https://doc.rust-lang.org/stable/nightly-rustc/rustc_hir/hir/struct.Block.html
/// - https://doc.rust-lang.org/reference/statements.html and
///   https://doc.rust-lang.org/stable/nightly-rustc/rustc_hir/hir/struct.Stmt.html
fn compile_stmts(
    hir: rustc_middle::hir::map::Map,
    stmts: &[rustc_hir::Stmt],
    expr: Option<&rustc_hir::Expr>,
) -> Expr {
    match stmts {
        [stmt, stmts @ ..] => match stmt.kind {
            rustc_hir::StmtKind::Local(rustc_hir::Local { pat, init, .. }) => {
                let pat = compile_pattern(pat);
                let init = match init {
                    Some(init) => Box::new(compile_expr(hir, init)),
                    None => Box::new(tt()),
                };
                let body = Box::new(compile_stmts(hir, stmts, expr));
                Expr::Let { pat, init, body }
            }
            rustc_hir::StmtKind::Item(_) => Expr::LocalVar("Stmt_item".to_string()),
            rustc_hir::StmtKind::Expr(current_expr) | rustc_hir::StmtKind::Semi(current_expr) => {
                let first = Box::new(compile_expr(hir, current_expr));
                let second = Box::new(compile_stmts(hir, stmts, expr));
                Expr::Seq { first, second }
            }
        },
        [] => match expr {
            Some(expr) => compile_expr(hir, expr),
            None => tt(),
        },
    }
}

/// [compile_block] compiles hir blocks into coq-of-rust
/// See the doc for [compile_stmts]
fn compile_block(hir: rustc_middle::hir::map::Map, block: &rustc_hir::Block) -> Expr {
    compile_stmts(hir, block.stmts, block.expr)
}

impl MatchArm {
    fn to_doc(&self) -> RcDoc<()> {
        return indent(RcDoc::concat([
            RcDoc::concat([
                RcDoc::text("|"),
                RcDoc::space(),
                self.pat.to_doc(),
                RcDoc::space(),
                RcDoc::text("=>"),
            ])
            .group(),
            RcDoc::line(),
            self.body.to_doc(false),
        ]))
        .group();
    }
}

impl Expr {
    pub fn to_doc(&self, with_paren: bool) -> RcDoc<()> {
        match self {
            Expr::LocalVar(ref name) => RcDoc::text(name),
            Expr::Var(path) => path.to_doc(),
            Expr::Literal(literal) => literal_to_doc(literal),
            Expr::Call { func, args } => indent(paren(
                with_paren,
                RcDoc::concat([
                    func.to_doc(true),
                    RcDoc::line(),
                    if args.is_empty() {
                        RcDoc::text("tt")
                    } else {
                        RcDoc::intersperse(args.iter().map(|arg| arg.to_doc(true)), RcDoc::line())
                    },
                ]),
            ))
            .group(),
            Expr::Let { pat, init, body } => RcDoc::concat([
                RcDoc::text("let"),
                RcDoc::space(),
                pat.to_doc(),
                RcDoc::space(),
                RcDoc::text(":="),
                RcDoc::space(),
                init.to_doc(false),
                RcDoc::space(),
                RcDoc::text("in"),
                RcDoc::hardline(),
                body.to_doc(false),
            ]),
            Expr::Lambda { args, body } => paren(
                with_paren,
                RcDoc::concat([
                    RcDoc::text("fun"),
                    RcDoc::space(),
                    RcDoc::intersperse(args.iter().map(|arg| arg.to_doc()), RcDoc::space()),
                    RcDoc::space(),
                    RcDoc::text("=>"),
                    RcDoc::space(),
                    body.to_doc(false),
                ]),
            ),
            Expr::Seq { first, second } => RcDoc::concat([
                first.to_doc(false),
                RcDoc::space(),
                RcDoc::text(";;"),
                RcDoc::hardline(),
                second.to_doc(false),
            ]),

            Expr::Array { elements } => bracket(RcDoc::intersperse(
                elements.iter().map(|element| element.to_doc(false)),
                RcDoc::text(";"),
            )),
            Expr::Tuple { elements } => paren(
                true,
                RcDoc::intersperse(
                    elements.iter().map(|element| element.to_doc(false)),
                    RcDoc::concat([RcDoc::text(","), RcDoc::space()]),
                ),
            ),
            Expr::LetIf { pat, init } => RcDoc::concat([
                RcDoc::text("let_if"),
                RcDoc::space(),
                pat.to_doc(),
                RcDoc::space(),
                RcDoc::text(":="),
                RcDoc::space(),
                init.to_doc(false),
            ]),

            Expr::If {
                condition,
                success,
                failure,
            } => paren(
                with_paren,
                RcDoc::concat([
                    (indent(RcDoc::concat([
                        RcDoc::text("if"),
                        RcDoc::space(),
                        condition.to_doc(false),
                        RcDoc::space(),
                        RcDoc::text("then").append(RcDoc::hardline()),
                        success.to_doc(false).group(),
                    ])))
                    .group(),
                    RcDoc::hardline(),
                    indent(RcDoc::concat([
                        RcDoc::text("else"),
                        RcDoc::hardline(),
                        failure.to_doc(false).group(),
                    ]))
                    .group(),
                ]),
            )
            .group(),
            Expr::Loop { body, loop_source } => paren(
                with_paren,
                RcDoc::concat([
                    RcDoc::text("loop"),
                    RcDoc::space(),
                    body.to_doc(true),
                    RcDoc::space(),
                    RcDoc::text("from"),
                    RcDoc::space(),
                    RcDoc::text(loop_source),
                ]),
            ),
            Expr::Match { scrutinee, arms } => RcDoc::concat([
                RcDoc::text("match"),
                RcDoc::space(),
                scrutinee.to_doc(false),
                RcDoc::space(),
                RcDoc::text("with"),
                RcDoc::hardline(),
                RcDoc::intersperse(arms.iter().map(|arm| arm.to_doc()), RcDoc::hardline()),
                RcDoc::hardline(),
                RcDoc::text("end"),
            ])
            .group(),
            Expr::Assign { left, right } => paren(
                with_paren,
                RcDoc::concat([
                    RcDoc::text("assign"),
                    RcDoc::space(),
                    left.to_doc(false),
                    RcDoc::space(),
                    RcDoc::text(":="),
                    RcDoc::space(),
                    right.to_doc(false),
                ]),
            ),
            Expr::AssignOp {
                bin_op,
                left,
                right,
            } => paren(
                with_paren,
                RcDoc::concat([
                    RcDoc::text("assign"),
                    RcDoc::space(),
                    left.to_doc(false),
                    RcDoc::space(),
                    RcDoc::text(":="),
                    RcDoc::space(),
                    left.to_doc(false),
                    RcDoc::space(),
                    RcDoc::text(bin_op),
                    RcDoc::space(),
                    right.to_doc(false),
                ]),
            ),
            Expr::Field { base, field } => {
                RcDoc::concat([base.to_doc(true), RcDoc::text("."), RcDoc::text(field)])
            }
            Expr::Index { base, index } => base.to_doc(true).append(bracket(index.to_doc(false))),
            Expr::Struct { path, fields, base } => RcDoc::concat([
                RcDoc::concat([
                    indent(RcDoc::concat([
                        RcDoc::text("{|"),
                        RcDoc::line(),
                        RcDoc::intersperse(
                            fields.iter().map(|(name, expr)| {
                                indent(RcDoc::concat([
                                    path.to_doc(),
                                    RcDoc::text("."),
                                    RcDoc::text(name),
                                    RcDoc::line(),
                                    RcDoc::text(":="),
                                    RcDoc::line(),
                                    expr.to_doc(false),
                                    RcDoc::text(";"),
                                ]))
                                .group()
                            }),
                            RcDoc::line(),
                        ),
                    ])),
                    RcDoc::line(),
                    RcDoc::text("|}"),
                ])
                .group(),
                match base {
                    Some(base) => RcDoc::concat([
                        RcDoc::line(),
                        RcDoc::text("with"),
                        RcDoc::line(),
                        base.to_doc(false),
                    ]),
                    None => RcDoc::nil(),
                },
            ])
            .group(),
        }
    }
}
