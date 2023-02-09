// NOTE: For the example to compile, you will need to first run the following:
//   rustup component add rustc-dev llvm-tools-preview

// version: 1.62.0-nightly (7c4b47696 2022-04-30)

extern crate rustc_ast;
extern crate rustc_ast_pretty;
extern crate rustc_error_codes;
extern crate rustc_errors;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;

use pretty::RcDoc;

use std::path::{Path, PathBuf};
use std::{fmt, fs, path, process, str};
use walkdir::WalkDir;

use crate::coq_of_rust::render::{bracket, literal_to_doc, paren};

use rustc_errors::registry;
use rustc_session::config::{self, CheckCfg};
use rustc_span::source_map;

#[derive(Debug)]
struct FLPath {
    segments: Vec<String>,
}
impl fmt::Display for FLPath {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let segments = self.segments.join("/");
        write!(f, "{segments}")
    }
}

/// The enum [Pat] represents the patterns which can be matched
#[derive(Debug)]
enum Pat {
    Wild,
    Struct(FLPath, Vec<(String, Pat)>),
    TupleStruct(FLPath, Vec<Pat>),
    Or(Vec<Pat>),
    Path(FLPath),
    Tuple(Vec<Pat>),
    Lit(rustc_ast::LitKind),
}

/// Struct [MatchArm] represents a pattern-matching branch: [pat] is the
/// matched pattern and [body] the expression on which it is mapped
#[derive(Debug)]
struct MatchArm {
    pat: Pat,
    body: Expr,
}

/// Enum [Expr] represents the AST of rust terms.
#[derive(Debug)]
enum Expr {
    LocalVar(String),
    Var(FLPath),
    Literal(rustc_ast::LitKind),
    App {
        func: Box<Expr>,
        args: Vec<Expr>,
    },
    Let {
        pat: Pat,
        init: Box<Expr>,
        body: Box<Expr>,
    },
    Lambda {
        args: Vec<Pat>,
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
        pat: Pat,
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
        path: FLPath,
        fields: Vec<(String, Expr)>,
        base: Option<Box<Expr>>,
    },
}

/// Representation of top-level hir [Item]s in coq-of-rust
/// See https://doc.rust-lang.org/reference/items.html
#[derive(Debug)]
enum TopLevelItem {
    Definition {
        name: String,
        args: Vec<String>,
        body: Expr,
    },
    Module {
        name: String,
        body: TopLevel,
    },
    Error(String),
}

#[derive(Debug)]
struct TopLevel(Vec<TopLevelItem>);

pub const INDENT_SPACE_OFFSET: isize = 2;
pub const LINE_WIDTH: usize = 80;

/// [compile_error] prints a message to stderr and outputs a value
fn compile_error<A>(value: A, message: String) -> A {
    eprintln!("{message}");
    value
}

fn compile_path(path: &rustc_hir::Path) -> FLPath {
    FLPath {
        segments: path
            .segments
            .iter()
            .map(|segment| segment.ident.name.to_string())
            .collect(),
    }
}

fn compile_qpath(qpath: &rustc_hir::QPath) -> FLPath {
    match qpath {
        rustc_hir::QPath::Resolved(_, path) => compile_path(path),
        rustc_hir::QPath::TypeRelative(_, segment) => FLPath {
            segments: vec![segment.ident.name.to_string()],
        },
        rustc_hir::QPath::LangItem(lang_item, _, _) => FLPath {
            segments: vec![lang_item.name().to_string()],
        },
    }
}

/// The function [compile_pat] translates a hir pattern to a coq-of-rust pattern.
fn compile_pat(pat: &rustc_hir::Pat) -> Pat {
    match &pat.kind {
        rustc_hir::PatKind::Wild => Pat::Wild,
        rustc_hir::PatKind::Binding(_, _, ident, _) => Pat::Path(FLPath {
            segments: vec![ident.name.to_string()],
        }),
        rustc_hir::PatKind::Struct(qpath, pats, _) => {
            let path = compile_qpath(qpath);
            let pats = pats
                .iter()
                .map(|pat| (pat.ident.name.to_string(), compile_pat(pat.pat)))
                .collect();
            Pat::Struct(path, pats)
        }
        rustc_hir::PatKind::TupleStruct(qpath, pats, _) => {
            let path = compile_qpath(qpath);
            let pats = pats.iter().map(compile_pat).collect();
            Pat::TupleStruct(path, pats)
        }
        rustc_hir::PatKind::Or(pats) => Pat::Or(pats.iter().map(compile_pat).collect()),
        rustc_hir::PatKind::Path(qpath) => Pat::Path(compile_qpath(qpath)),
        rustc_hir::PatKind::Tuple(pats, _) => Pat::Tuple(pats.iter().map(compile_pat).collect()),
        rustc_hir::PatKind::Box(pat) => compile_pat(pat),
        rustc_hir::PatKind::Ref(pat, _) => compile_pat(pat),
        rustc_hir::PatKind::Lit(expr) => match expr.kind {
            rustc_hir::ExprKind::Lit(ref lit) => Pat::Lit(lit.node.clone()),
            _ => compile_error(Pat::Wild, "Expected a literal".to_string()),
        },
        rustc_hir::PatKind::Range(_, _, _) => {
            compile_error(Pat::Wild, "Pattern range not supported".to_string())
        }
        rustc_hir::PatKind::Slice(_, _, _) => {
            compile_error(Pat::Wild, "Pattern slice not supported".to_string())
        }
    }
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
        _ => compile_error("Binary".to_string(), "Binary not supported".to_string()),
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

fn compile_expr(hir: rustc_middle::hir::map::Map, expr: &rustc_hir::Expr) -> Expr {
    match &expr.kind {
        rustc_hir::ExprKind::Box(expr) => compile_expr(hir, expr),
        rustc_hir::ExprKind::ConstBlock(_anon_const) => compile_error(
            Expr::LocalVar("ConstBlock".to_string()),
            "ConstBlock not supported".to_string(),
        ),
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
            Expr::App { func, args }
        }
        rustc_hir::ExprKind::MethodCall(_path_segment, func, args, _span) => {
            let func = Box::new(compile_expr(hir, func));
            let args = args.iter().map(|expr| compile_expr(hir, expr)).collect();
            Expr::App { func, args }
        }
        rustc_hir::ExprKind::Tup(elements) => {
            let elements = elements
                .iter()
                .map(|expr| compile_expr(hir, expr))
                .collect();
            Expr::Tuple { elements }
        }
        rustc_hir::ExprKind::Binary(bin_op, expr_left, expr_right) => {
            let expr_left = Box::new(compile_expr(hir, expr_left));
            let expr_right = Box::new(compile_expr(hir, expr_right));
            let func = Box::new(Expr::LocalVar(compile_bin_op(bin_op)));
            Expr::App {
                func,
                args: vec![*expr_left, *expr_right],
            }
        }
        rustc_hir::ExprKind::Unary(_un_op, expr) => {
            let expr = Box::new(compile_expr(hir, expr));
            let func = Box::new(Expr::LocalVar("unary".to_string()));
            Expr::App {
                func,
                args: vec![*expr],
            }
        }
        rustc_hir::ExprKind::Lit(lit) => Expr::Literal(lit.node.clone()),
        rustc_hir::ExprKind::Cast(expr, _ty) => compile_expr(hir, expr),
        rustc_hir::ExprKind::Type(expr, _ty) => compile_expr(hir, expr),
        rustc_hir::ExprKind::DropTemps(expr) => compile_expr(hir, expr),
        rustc_hir::ExprKind::Let(rustc_hir::Let { pat, init, .. }) => {
            let pat = compile_pat(pat);
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
                    let pat = compile_pat(arm.pat);
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
                .map(|rustc_hir::Param { pat, .. }| compile_pat(pat))
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
            let bin_op = compile_bin_op(bin_op);
            let left = Box::new(compile_expr(hir, left));
            let right = Box::new(compile_expr(hir, right));
            Expr::AssignOp {
                bin_op,
                left,
                right,
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
        rustc_hir::ExprKind::Break(_, _) => compile_error(
            Expr::LocalVar("Break".to_string()),
            "Unsupported break".to_string(),
        ),
        rustc_hir::ExprKind::Continue(_) => compile_error(
            Expr::LocalVar("Continue".to_string()),
            "Unsupported continue".to_string(),
        ),
        rustc_hir::ExprKind::Ret(expr) => {
            let func = Box::new(Expr::LocalVar("Return".to_string()));
            let args = match expr {
                Some(expr) => vec![compile_expr(hir, expr)],
                None => vec![],
            };
            Expr::App { func, args }
        }
        rustc_hir::ExprKind::InlineAsm(_) => compile_error(
            Expr::LocalVar("InlineAsm".to_string()),
            "Unsupported inline asm".to_string(),
        ),
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
            Expr::App {
                func: Box::new(Expr::LocalVar("repeat".to_string())),
                args: vec![expr],
            }
        }
        rustc_hir::ExprKind::Yield(expr, _) => {
            let expr = compile_expr(hir, expr);
            Expr::App {
                func: Box::new(Expr::LocalVar("yield".to_string())),
                args: vec![expr],
            }
        }
        rustc_hir::ExprKind::Err => compile_error(
            Expr::LocalVar("Err".to_string()),
            "Unsupported error".to_string(),
        ),
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
                let pat = compile_pat(pat);
                let init = match init {
                    Some(init) => Box::new(compile_expr(hir, init)),
                    None => Box::new(tt()),
                };
                let body = Box::new(compile_stmts(hir, stmts, expr));
                Expr::Let { pat, init, body }
            }
            rustc_hir::StmtKind::Item(_) => compile_error(
                Expr::LocalVar("Stmt_item".to_string()),
                "Unsupported stmt kind".to_string(),
            ),
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

/// [compile_top_level_item] compiles hir [Item]s into coq-of-rust (optional)
/// items.
/// - See https://doc.rust-lang.org/stable/nightly-rustc/rustc_hir/struct.Item.html
///   and the doc for [TopLevelItem]
/// - [rustc_middle::hir::map::Map] is intuitively the type for hir environments
/// - Method [body] allows retrievient the body of an identifier [body_id] in an
///   hir environment [hir]
fn compile_top_level_item(
    hir: rustc_middle::hir::map::Map,
    item: &rustc_hir::Item,
) -> Option<TopLevelItem> {
    match &item.kind {
        rustc_hir::ItemKind::ExternCrate(_) => None,
        rustc_hir::ItemKind::Use(_, _) => None,
        rustc_hir::ItemKind::Static(_, _, body_id) => {
            let expr = hir.body(*body_id).value;
            Some(TopLevelItem::Definition {
                name: item.ident.name.to_string(),
                args: vec![],
                body: compile_expr(hir, expr),
            })
        }
        rustc_hir::ItemKind::Const(_, body_id) => {
            let expr = hir.body(*body_id).value;
            Some(TopLevelItem::Definition {
                name: item.ident.name.to_string(),
                args: vec![],
                body: compile_expr(hir, expr),
            })
        }
        rustc_hir::ItemKind::Fn(_fn_sig, _, body_id) => {
            let expr = hir.body(*body_id).value;
            Some(TopLevelItem::Definition {
                name: item.ident.name.to_string(),
                args: vec![],
                body: compile_expr(hir, expr),
            })
        }
        rustc_hir::ItemKind::Macro(_, _) => None,
        rustc_hir::ItemKind::Mod(module) => {
            let items = module
                .item_ids
                .iter()
                .filter_map(|item_id| {
                    let item = hir.item(*item_id);
                    compile_top_level_item(hir, item)
                })
                .collect();
            Some(TopLevelItem::Module {
                name: item.ident.name.to_string(),
                body: TopLevel(items),
            })
        }
        rustc_hir::ItemKind::ForeignMod { .. } => {
            Some(TopLevelItem::Error("ForeignMod".to_string()))
        }
        rustc_hir::ItemKind::GlobalAsm(_) => Some(TopLevelItem::Error("GlobalAsm".to_string())),
        rustc_hir::ItemKind::TyAlias(_, _) => Some(TopLevelItem::Error("TyAlias".to_string())),
        rustc_hir::ItemKind::OpaqueTy(_) => Some(TopLevelItem::Error("OpaqueTy".to_string())),
        rustc_hir::ItemKind::Enum(_, _) => Some(TopLevelItem::Error("Enum".to_string())),
        rustc_hir::ItemKind::Struct(_, _) => Some(TopLevelItem::Error("Struct".to_string())),
        rustc_hir::ItemKind::Union(_, _) => Some(TopLevelItem::Error("Union".to_string())),
        rustc_hir::ItemKind::Trait(_, _, _, _, _) => Some(TopLevelItem::Error("Trait".to_string())),
        rustc_hir::ItemKind::TraitAlias(_, _) => {
            Some(TopLevelItem::Error("TraitAlias".to_string()))
        }
        rustc_hir::ItemKind::Impl(_) => Some(TopLevelItem::Error("Impl".to_string())),
    }
}

fn compile_top_level(tcx: rustc_middle::ty::TyCtxt) -> TopLevel {
    let hir = tcx.hir();
    TopLevel(
        hir.items()
            .filter_map(|item_id| {
                let item = hir.item(item_id);
                compile_top_level_item(hir, item)
            })
            .collect(),
    )
}

impl FLPath {
    fn to_doc(&self) -> RcDoc<()> {
        RcDoc::intersperse(self.segments.iter().map(RcDoc::text), RcDoc::text("."))
    }
}

impl Pat {
    fn to_doc(&self) -> RcDoc<()> {
        match self {
            Pat::Wild => RcDoc::text("_"),
            Pat::Struct(path, fields) => {
                let in_brackets_doc = bracket(RcDoc::intersperse(
                    fields.iter().map(|(name, expr)| {
                        RcDoc::concat([
                            RcDoc::text(name),
                            RcDoc::space(),
                            RcDoc::text(":"),
                            RcDoc::space(),
                            expr.to_doc(),
                        ])
                    }),
                    RcDoc::text(","),
                ));
                return RcDoc::concat([path.to_doc(), RcDoc::space(), in_brackets_doc]);
            }
            Pat::TupleStruct(path, fields) => {
                let signature_in_parentheses_doc = paren(
                    true,
                    RcDoc::intersperse(fields.iter().map(|field| field.to_doc()), RcDoc::text(",")),
                );
                return RcDoc::concat([
                    path.to_doc(),
                    RcDoc::space(),
                    signature_in_parentheses_doc,
                ]);
            }
            Pat::Or(pats) => paren(
                true,
                RcDoc::intersperse(pats.iter().map(|pat| pat.to_doc()), RcDoc::text("|")),
            ),
            Pat::Path(path) => path.to_doc(),
            Pat::Tuple(pats) => paren(
                true,
                RcDoc::intersperse(pats.iter().map(|pat| pat.to_doc()), RcDoc::text(",")),
            ),
            Pat::Lit(literal) => RcDoc::text(format!("{literal:?}")),
        }
    }
}

impl MatchArm {
    fn to_doc(&self) -> RcDoc<()> {
        return RcDoc::concat([
            self.pat.to_doc(),
            RcDoc::space(),
            RcDoc::text("=>"),
            RcDoc::space(),
            self.body.to_doc(false),
        ]);
    }
}

impl Expr {
    fn to_doc(&self, with_paren: bool) -> RcDoc<()> {
        match self {
            Expr::LocalVar(ref name) => RcDoc::text(name),

            Expr::Var(path) => path.to_doc(),

            Expr::Literal(literal) => literal_to_doc(literal),
            Expr::App { func, args } => paren(
                with_paren,
                RcDoc::concat([
                    func.to_doc(true),
                    RcDoc::space(),
                    RcDoc::intersperse(args.iter().map(|arg| arg.to_doc(true)), RcDoc::space()),
                ]),
            ),
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
                    RcDoc::text(","),
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
                    (RcDoc::concat([
                        RcDoc::text("if"),
                        RcDoc::space(),
                        condition.to_doc(false),
                        RcDoc::space(),
                        RcDoc::text("then").append(RcDoc::hardline()),
                        success.to_doc(false).group(),
                    ]))
                    .nest(INDENT_SPACE_OFFSET)
                    .group(),
                    RcDoc::hardline(),
                    RcDoc::concat([
                        RcDoc::text("else"),
                        RcDoc::hardline(),
                        failure.to_doc(false).group(),
                    ])
                    .nest(INDENT_SPACE_OFFSET)
                    .group(),
                ]),
            ),
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
                RcDoc::space(),
                RcDoc::intersperse(arms.iter().map(|arm| arm.to_doc()), RcDoc::space()),
                RcDoc::space(),
                RcDoc::text("end"),
            ]),
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
            Expr::Struct { path, fields, base } => {
                let struct_signature_doc = RcDoc::concat([
                    RcDoc::text("struct"),
                    RcDoc::space(),
                    path.to_doc(),
                    RcDoc::space(),
                    RcDoc::text("{"),
                    RcDoc::intersperse(
                        fields.iter().map(|(name, expr)| {
                            RcDoc::concat([
                                RcDoc::text(name),
                                RcDoc::space(),
                                RcDoc::text(":="),
                                RcDoc::space(),
                                expr.to_doc(false),
                            ])
                        }),
                        RcDoc::text(";"),
                    ),
                    RcDoc::text("}"),
                    RcDoc::space(),
                    match base {
                        Some(base) => {
                            RcDoc::concat([RcDoc::text("with"), RcDoc::space(), base.to_doc(false)])
                        }
                        None => RcDoc::nil(),
                    },
                ]);

                return paren(with_paren, struct_signature_doc);
            }
        }
    }
}

impl TopLevelItem {
    fn to_doc(&self) -> RcDoc {
        match self {
            TopLevelItem::Definition { name, args, body } => RcDoc::concat([
                RcDoc::text("Definition"),
                RcDoc::space(),
                RcDoc::text(name),
                RcDoc::intersperse(args.iter().map(RcDoc::text), RcDoc::space()),
                RcDoc::space(),
                RcDoc::text(":="),
                RcDoc::hardline()
                    .append(body.to_doc(false))
                    .nest(INDENT_SPACE_OFFSET)
                    .group(),
                RcDoc::text("."),
            ])
            .group(),
            TopLevelItem::Module { name, body } => RcDoc::concat([
                RcDoc::text("Module"),
                RcDoc::space(),
                RcDoc::text(name),
                RcDoc::space(),
                RcDoc::text(":="),
                RcDoc::hardline()
                    .append(body.to_doc())
                    .nest(INDENT_SPACE_OFFSET)
                    .group(),
                RcDoc::text("."),
            ])
            .group(),

            TopLevelItem::Error(message) => RcDoc::concat([
                RcDoc::text("Error"),
                RcDoc::space(),
                RcDoc::text(message),
                RcDoc::text("."),
            ])
            .group(),
        }
    }
}

impl TopLevel {
    fn to_doc(&self) -> RcDoc {
        RcDoc::intersperse(
            self.0.iter().map(|item| item.to_doc()),
            RcDoc::hardline().append(RcDoc::hardline()),
        )
    }

    fn to_pretty(&self, width: usize) -> String {
        let mut w = Vec::new();
        self.to_doc().render(width, &mut w).unwrap();
        String::from_utf8(w).unwrap()
    }
}

fn change_to_coq_extension(path: &Path) -> PathBuf {
    let mut new_path = path.to_path_buf();
    new_path.set_extension("v");
    return new_path;
}
pub fn run(src_folder: &Path) {
    let dst_folder = Path::new("coq_translation");

    for entry in WalkDir::new(src_folder) {
        let entry = entry.unwrap();
        let src_path = entry.path();

        // calculate the relative path from the source to the destination directory
        let relative_path = src_path.strip_prefix(src_folder).unwrap();
        let dst_path = dst_folder.join(relative_path);

        // if the entry is a directory, create it in the destination directory
        if src_path.is_dir() {
            fs::create_dir_all(&dst_path).unwrap();
        } else {
            // if the entry is a file, create a Coq version of it and write it to the destination directory
            let contents = fs::read_to_string(src_path).unwrap();
            let translation = create_translation_to_coq(
                src_path.file_name().unwrap().to_str().unwrap().to_string(),
                contents,
            );
            fs::write(
                dst_folder.join(change_to_coq_extension(relative_path)),
                translation,
            )
            .unwrap();
        }
    }
}

fn create_translation_to_coq(input_file_name: String, contents: String) -> String {
    let filename = input_file_name.clone();
    let out = process::Command::new("rustc")
        .arg("--print=sysroot")
        .current_dir(".")
        .output()
        .unwrap();
    let sysroot = str::from_utf8(&out.stdout).unwrap().trim();
    let config = rustc_interface::Config {
        opts: config::Options {
            maybe_sysroot: Some(path::PathBuf::from(sysroot)),
            ..config::Options::default()
        },
        input: config::Input::Str {
            name: source_map::FileName::Custom(input_file_name),
            input: contents.to_string(),
        },
        crate_cfg: rustc_hash::FxHashSet::default(),
        crate_check_cfg: CheckCfg::default(),
        input_path: None,
        output_dir: None,
        output_file: None,
        file_loader: None,
        lint_caps: rustc_hash::FxHashMap::default(),
        parse_sess_created: None,
        register_lints: None,
        override_queries: None,
        make_codegen_backend: None,
        registry: registry::Registry::new(rustc_error_codes::DIAGNOSTICS),
    };
    let now = std::time::Instant::now();
    let result = rustc_interface::run_compiler(config, |compiler| {
        compiler.enter(|queries| {
            queries.global_ctxt().unwrap().take().enter(|tcx| {
                let top_level = compile_top_level(tcx);
                let top_level_str = top_level.to_pretty(LINE_WIDTH).to_string();
                top_level_str
            })
        })
    });
    println!(
        "{} ms have passed to translate: {}",
        now.elapsed().as_millis(),
        filename
    );
    return result;
}

#[cfg(test)]
mod tests {
    use std::fs;
    use std::io::Read;

    /// Look above (search string ".snapshot") to see how .snapshot files are generated
    /// Note that the function [gen_snap_tests] tests all the files of the directory
    /// examples-from-rust-book, but however, it is regarded by [cargo test] as
    /// a *unique* unitary test
    #[test]
    fn gen_snap_tests() -> () {
        let dir = std::path::Path::new("examples-from-rust-book");

        for entry in fs::read_dir(dir).unwrap() {
            let entry = entry.unwrap();
            let path = entry.path();

            let file_parent = path.parent().unwrap();
            let file_stem = path.file_stem().unwrap();
            if path.is_file() && path.extension().unwrap() == "v" {
                print!("Scanning file {}\n", file_stem.to_str().unwrap()); // ignored during tests
                let snap_path = file_parent.to_str().unwrap().to_string()
                    + "/"
                    + file_stem.to_str().unwrap()
                    + ".snapshot";
                let mut snap_file = fs::File::open(snap_path).unwrap();
                let mut snap_contents = String::new();
                snap_file.read_to_string(&mut snap_contents).unwrap();
                let mut file = fs::File::open(&path).unwrap();
                let mut contents = String::new();
                file.read_to_string(&mut contents).unwrap();
                assert_eq!(
                    contents,
                    snap_contents,
                    "The test failed on {}\n",
                    file_stem.to_str().unwrap()
                );
            }
        }
    }
}
