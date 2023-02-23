use crate::path::*;
use crate::pattern::*;
use crate::render::*;
use rustc_ast::LitKind;
use rustc_hir::{BinOp, BinOpKind};
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
pub enum Expr {
    LocalVar(String),
    Var(Path),
    Literal(LitKind),
    Call {
        func: Box<Expr>,
        args: Vec<Expr>,
    },
    MethodCall {
        func: String,
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
    IndexedField {
        base: Box<Expr>,
        index: u32,
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
fn compile_bin_op(bin_op: &BinOp) -> String {
    match bin_op.node {
        BinOpKind::Add => "add".to_string(),
        BinOpKind::Sub => "sub".to_string(),
        BinOpKind::Mul => "mul".to_string(),
        BinOpKind::Div => "div".to_string(),
        BinOpKind::Rem => "rem".to_string(),
        BinOpKind::And => "andb".to_string(),
        BinOpKind::Or => "or".to_string(),
        BinOpKind::BitXor => "bit_xor".to_string(),
        BinOpKind::BitAnd => "bit_and".to_string(),
        BinOpKind::BitOr => "bit_or".to_string(),
        BinOpKind::Shl => "shl".to_string(),
        BinOpKind::Shr => "shr".to_string(),
        BinOpKind::Eq => "eqb".to_string(),
        BinOpKind::Lt => "lt".to_string(),
        BinOpKind::Le => "le".to_string(),
        BinOpKind::Ne => "ne".to_string(),
        BinOpKind::Ge => "ge".to_string(),
        BinOpKind::Gt => "gt".to_string(),
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

pub fn compile_expr(tcx: TyCtxt, expr: &rustc_hir::Expr) -> Expr {
    match &expr.kind {
        rustc_hir::ExprKind::Box(expr) => compile_expr(tcx, expr),
        rustc_hir::ExprKind::ConstBlock(_anon_const) => Expr::LocalVar("ConstBlock".to_string()),
        rustc_hir::ExprKind::Array(elements) => {
            let elements = elements
                .iter()
                .map(|expr| compile_expr(tcx, expr))
                .collect();
            Expr::Array { elements }
        }
        rustc_hir::ExprKind::Call(func, args) => {
            let func = Box::new(compile_expr(tcx, func));
            let args = args.iter().map(|expr| compile_expr(tcx, expr)).collect();
            Expr::Call { func, args }
        }
        rustc_hir::ExprKind::MethodCall(path_segment, object, args, _) => {
            let func = path_segment.ident.to_string();
            let mut object_with_args = vec![compile_expr(tcx, object)];
            let args: Vec<_> = args.iter().map(|expr| compile_expr(tcx, expr)).collect();
            object_with_args.extend(args);
            Expr::MethodCall {
                func,
                args: object_with_args,
            }
        }
        rustc_hir::ExprKind::Tup(elements) => {
            let elements = elements
                .iter()
                .map(|expr| compile_expr(tcx, expr))
                .collect();
            Expr::Tuple { elements }
        }
        rustc_hir::ExprKind::Binary(bin_op, expr_left, expr_right) => {
            let expr_left = compile_expr(tcx, expr_left);
            let expr_right = compile_expr(tcx, expr_right);
            let func = Box::new(Expr::LocalVar(compile_bin_op(bin_op)));
            Expr::Call {
                func,
                args: vec![expr_left, expr_right],
            }
        }
        rustc_hir::ExprKind::Unary(un_op, expr) => {
            let expr = compile_expr(tcx, expr);
            let func = Box::new(Expr::LocalVar(compile_un_op(un_op)));
            Expr::Call {
                func,
                args: vec![expr],
            }
        }
        rustc_hir::ExprKind::Lit(lit) => Expr::Literal(lit.node.clone()),
        rustc_hir::ExprKind::Cast(expr, _ty) => compile_expr(tcx, expr),
        rustc_hir::ExprKind::Type(expr, _ty) => compile_expr(tcx, expr),
        rustc_hir::ExprKind::DropTemps(expr) => compile_expr(tcx, expr),
        rustc_hir::ExprKind::Let(rustc_hir::Let { pat, init, .. }) => {
            let pat = compile_pattern(pat);
            let init = Box::new(compile_expr(tcx, init));
            Expr::LetIf { pat, init }
        }
        rustc_hir::ExprKind::If(condition, success, failure) => {
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
        rustc_hir::ExprKind::Loop(block, _, loop_source, _) => {
            let body = Box::new(compile_block(tcx, block));
            let loop_source = compile_loop_source(loop_source);
            Expr::Loop { body, loop_source }
        }
        rustc_hir::ExprKind::Match(scrutinee, arms, _) => {
            let scrutinee = Box::new(compile_expr(tcx, scrutinee));
            let arms = arms
                .iter()
                .map(|arm| {
                    let pat = compile_pattern(arm.pat);
                    let body = compile_expr(tcx, arm.body);
                    MatchArm { pat, body }
                })
                .collect();
            Expr::Match { scrutinee, arms }
        }
        rustc_hir::ExprKind::Closure(rustc_hir::Closure { body, .. }) => {
            let body = tcx.hir().body(*body);
            let args = body
                .params
                .iter()
                .map(|rustc_hir::Param { pat, .. }| compile_pattern(pat))
                .collect();
            let body = Box::new(compile_expr(tcx, body.value));
            Expr::Lambda { args, body }
        }
        rustc_hir::ExprKind::Block(block, _) => compile_block(tcx, block),
        rustc_hir::ExprKind::Assign(left, right, _) => {
            let left = Box::new(compile_expr(tcx, left));
            let right = Box::new(compile_expr(tcx, right));
            Expr::Assign { left, right }
        }
        rustc_hir::ExprKind::AssignOp(bin_op, left, right) => {
            let func = Box::new(Expr::LocalVar(compile_bin_op(bin_op)));
            // We have to duplicate the code here for memory allocations
            let left_left = compile_expr(tcx, left);
            let left_right = compile_expr(tcx, left);
            let right = compile_expr(tcx, right);
            Expr::Assign {
                left: Box::new(left_left),
                right: Box::new(Expr::Call {
                    func,
                    args: vec![left_right, right],
                }),
            }
        }
        rustc_hir::ExprKind::Field(base, ident) => {
            let base = Box::new(compile_expr(tcx, base));
            let index = ident.name.to_string().parse::<u32>();
            match index {
                Ok(index) => Expr::IndexedField { base, index },
                Err(_) => {
                    let field = ident.name.to_string();
                    Expr::Field { base, field }
                }
            }
        }
        rustc_hir::ExprKind::Index(base, index) => {
            let base = Box::new(compile_expr(tcx, base));
            let index = Box::new(compile_expr(tcx, index));
            Expr::Index { base, index }
        }
        rustc_hir::ExprKind::Path(qpath) => {
            let path = compile_qpath(qpath);
            Expr::Var(path)
        }
        rustc_hir::ExprKind::AddrOf(_, _, expr) => compile_expr(tcx, expr),
        rustc_hir::ExprKind::Break(_, _) => Expr::LocalVar("Break".to_string()),
        rustc_hir::ExprKind::Continue(_) => Expr::LocalVar("Continue".to_string()),
        rustc_hir::ExprKind::Ret(expr) => {
            let func = Box::new(Expr::LocalVar("Return".to_string()));
            let args = match expr {
                Some(expr) => vec![compile_expr(tcx, expr)],
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
                    let expr = compile_expr(tcx, expr);
                    (field, expr)
                })
                .collect();
            let base = base.map(|expr| Box::new(compile_expr(tcx, expr)));
            Expr::Struct { path, fields, base }
        }
        rustc_hir::ExprKind::Repeat(expr, _) => {
            let expr = compile_expr(tcx, expr);
            Expr::Call {
                func: Box::new(Expr::LocalVar("repeat".to_string())),
                args: vec![expr],
            }
        }
        rustc_hir::ExprKind::Yield(expr, _) => {
            let expr = compile_expr(tcx, expr);
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
fn compile_stmts(tcx: TyCtxt, stmts: &[rustc_hir::Stmt], expr: Option<&rustc_hir::Expr>) -> Expr {
    match stmts {
        [stmt, stmts @ ..] => match stmt.kind {
            rustc_hir::StmtKind::Local(rustc_hir::Local { pat, init, .. }) => {
                let pat = compile_pattern(pat);
                let init = match init {
                    Some(init) => Box::new(compile_expr(tcx, init)),
                    None => Box::new(tt()),
                };
                let body = Box::new(compile_stmts(tcx, stmts, expr));
                Expr::Let { pat, init, body }
            }
            rustc_hir::StmtKind::Item(_) => Expr::LocalVar("Stmt_item".to_string()),
            rustc_hir::StmtKind::Expr(current_expr) | rustc_hir::StmtKind::Semi(current_expr) => {
                let first = Box::new(compile_expr(tcx, current_expr));
                let second = Box::new(compile_stmts(tcx, stmts, expr));
                Expr::Seq { first, second }
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
            Expr::Literal(literal) => literal_to_doc(literal),
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
            Expr::MethodCall { func, args } => paren(
                with_paren,
                nest([
                    text("method"),
                    line(),
                    text(format!("\"{}\"", func.to_string())),
                    concat(args.iter().map(|arg| concat([line(), arg.to_doc(true)]))),
                ]),
            ),
            Expr::Let { pat, init, body } => group([
                nest([
                    nest([
                        text("let"),
                        line(),
                        group([pat.to_doc(), line(), text(":=")]),
                    ]),
                    line(),
                    group([init.to_doc(false), text(" in")]),
                ]),
                hardline(),
                body.to_doc(false),
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
            Expr::Seq { first, second } => group([
                group([first.to_doc(false), text(" ;;")]),
                hardline(),
                second.to_doc(false),
            ]),

            Expr::Array { elements } => bracket(intersperse(
                elements.iter().map(|element| element.to_doc(false)),
                [text(";")],
            )),
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
                        nest([text("if"), line(), condition.to_doc(false)]),
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
                    left.to_doc(false),
                    line(),
                    text(":="),
                    line(),
                    right.to_doc(false),
                ]),
            ),
            Expr::AssignOp {
                bin_op,
                left,
                right,
            } => paren(
                with_paren,
                nest([
                    text("assign"),
                    line(),
                    left.to_doc(false),
                    line(),
                    text(":="),
                    line(),
                    left.to_doc(false),
                    line(),
                    text(bin_op),
                    line(),
                    right.to_doc(false),
                ]),
            ),
            Expr::Field { base, field } => nest([base.to_doc(true), text("."), text(field)]),
            Expr::IndexedField { base, index } => paren(
                with_paren,
                nest([
                    text("IndexedField.get"),
                    line(),
                    nest([
                        text("(index"),
                        line(),
                        text(":="),
                        line(),
                        text(index.to_string()),
                        text(")"),
                    ]),
                    line(),
                    base.to_doc(true),
                ]),
            ),
            Expr::Index { base, index } => nest([base.to_doc(true), bracket(index.to_doc(false))]),
            Expr::Struct { path, fields, base } => group([
                group([
                    nest([
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
        }
    }
}
