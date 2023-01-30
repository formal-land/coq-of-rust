#![feature(rustc_private)]

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

use std::{path, process, str};

use rustc_ast_pretty::pprust::item_to_string;
use rustc_errors::registry;
use rustc_session::config::{self, CheckCfg};
use rustc_span::source_map;

#[derive(Debug)]
struct Path {
    segments: Vec<String>,
}

#[derive(Debug)]
enum Pat {
    Wild,
    // Binding(BindingAnnotation, HirId, Ident, Option<&'hir Pat<'hir>>),
    // Struct(QPath<'hir>, &'hir [PatField<'hir>], bool),
    // TupleStruct(QPath<'hir>, &'hir [Pat<'hir>], DotDotPos),
    Or(Vec<Pat>),
    Path(Path),
    Tuple(Vec<Pat>),
    // Box(&'hir Pat<'hir>),
    // Ref(&'hir Pat<'hir>, Mutability),
    Lit(rustc_ast::LitKind),
    // Range(Option<&'hir Expr<'hir>>, Option<&'hir Expr<'hir>>, RangeEnd),
    // Slice(&'hir [Pat<'hir>], Option<&'hir Pat<'hir>>, &'hir [Pat<'hir>]),
}

#[derive(Debug)]
struct MatchArm {
    pat: Pat,
    body: Expr,
}

#[derive(Debug)]
enum Expr {
    LocalVar(String),
    Var(Path),
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
        failure: Option<Box<Expr>>,
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

#[derive(Debug)]
enum TopLevelItem {
    Definition {
        name: String,
        args: Vec<String>,
        body: Expr,
    },
}

#[derive(Debug)]
struct TopLevel {
    items: Vec<TopLevelItem>,
}
/*
impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Expr::LocalVar(name) => write!(f, "{}", name),
            Expr::Literal(lit) => write!(f, "{:?}", lit),
            Expr::App { func, args } => {
                write!(f, "{}(", func)?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", arg)?;
                }
                write!(f, ")")
            }
            Expr::Let { name, value, body } => {
                write!(f, "let {} = {} in {}", name, value, body)
            }
            Expr::Lambda { name, body } => write!(f, "fun {} => {}", name, body),
            Expr::Seq { first, second } => write!(f, "{}; {}", first, second),
            Expr::Array { elements } => {
                write!(f, "[")?;
                for (i, element) in elements.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", element)?;
                }
                write!(f, "]")
            }
            Expr::Tuple { elements } => {
                write!(f, "(")?;
                for (i, element) in elements.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", element)?;
                }
                write!(f, ")")
            }
            Expr::LetIf { pat, value } => write!(f, "let {} = {} in ()", pat, value),
        }
    }
}

impl fmt::Display for TopLevelItem {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TopLevelItem::Definition { name, args, body } => {
                write!(f, "def {}(", name)?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", arg)?;
                }
                write!(f, ") = {}", body)
            }
        }
    }
}

impl fmt::Display for TopLevel {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (i, item) in self.items.iter().enumerate() {
            if i > 0 {
                write!(f, "\n")?;
            }
            write!(f, "{}", item)?;
        }
        Ok(())
    }
}*/

fn compile_error<A>(value: A, message: String) -> A {
    eprintln!("{}", message);
    value
}

fn compile_path(path: &rustc_hir::Path) -> Path {
    Path {
        segments: path
            .segments
            .iter()
            .map(|segment| segment.ident.name.to_string())
            .collect(),
    }
}

fn compile_qpath(qpath: &rustc_hir::QPath) -> Path {
    match qpath {
        rustc_hir::QPath::Resolved(_, path) => compile_path(path),
        rustc_hir::QPath::TypeRelative(_, segment) => Path {
            segments: vec![segment.ident.name.to_string()],
        },
        rustc_hir::QPath::LangItem(lang_item, _, _) => Path {
            segments: vec![lang_item.name().to_string()],
        },
    }
}

fn compile_pat(pat: &rustc_hir::Pat) -> Pat {
    match &pat.kind {
        rustc_hir::PatKind::Wild => Pat::Wild,
        // rustc_hir::PatKind::Lit(lit) => Pat::Lit(lit.node.clone()),
        rustc_hir::PatKind::Or(pats) => Pat::Or(pats.iter().map(|pat| compile_pat(pat)).collect()),
        rustc_hir::PatKind::Path(qpath) => Pat::Path(compile_qpath(qpath)),
        rustc_hir::PatKind::Tuple(pats, _) => {
            Pat::Tuple(pats.iter().map(|pat| compile_pat(pat)).collect())
        }
        _ => compile_error(Pat::Wild, "Pattern not supported".to_string()),
    }
}

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

fn compile_loop_source(loop_source: &rustc_hir::LoopSource) -> String {
    match loop_source {
        rustc_hir::LoopSource::Loop => "loop".to_string(),
        rustc_hir::LoopSource::While => "while".to_string(),
        rustc_hir::LoopSource::ForLoop => "for".to_string(),
    }
}

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
            let func = Box::new(Expr::LocalVar(compile_bin_op(&bin_op)));
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
            let failure = failure.map(|expr| Box::new(compile_expr(hir, expr)));
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
                    let pat = compile_pat(&arm.pat);
                    let body = compile_expr(hir, &arm.body);
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
            format!("Unsupported break"),
        ),
        rustc_hir::ExprKind::Continue(_) => compile_error(
            Expr::LocalVar("Continue".to_string()),
            format!("Unsupported continue"),
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
            format!("Unsupported inline asm"),
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
            format!("Unsupported error"),
        ),
    }
}

fn compile_stmts(
    hir: rustc_middle::hir::map::Map,
    stmts: &[rustc_hir::Stmt],
    expr: Option<&rustc_hir::Expr>,
) -> Expr {
    // stmts.iter().map(|stmt| compile_stmt(stmt)).collect()
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
                format!("Unsupported stmt kind"),
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

fn compile_block(hir: rustc_middle::hir::map::Map, block: &rustc_hir::Block) -> Expr {
    compile_stmts(hir, block.stmts, block.expr)
}

fn compile_top_level_item(
    hir: rustc_middle::hir::map::Map,
    item: &rustc_hir::Item,
) -> TopLevelItem {
    match &item.kind {
        rustc_hir::ItemKind::Fn(_fn_sig, _, body_id) => {
            let expr = hir.body(*body_id).value;

            TopLevelItem::Definition {
                name: item.ident.name.to_string(),
                args: vec![],
                body: compile_expr(hir, expr),
            }
        }
        _ => compile_error(
            TopLevelItem::Definition {
                name: item.ident.name.to_string(),
                args: vec![],
                body: Expr::LocalVar("TODO".to_string()),
            },
            format!("Unsupported item kind"),
        ),
    }
}

fn compile_top_level(tcx: rustc_middle::ty::TyCtxt) -> TopLevel {
    let hir = tcx.hir();

    TopLevel {
        items: hir
            .items()
            .map(|item_id| {
                let item = hir.item(item_id);

                compile_top_level_item(hir, item)
            })
            .collect(),
    }
}

fn main() {
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
            name: source_map::FileName::Custom("main.rs".to_string()),
            input: r#"
const message: &str = "Hello, World!";

fn main() {
    println!("{message}");

    // All have type `Option<i32>`
    let number = Some(7);
    let letter: Option<i32> = None;
    let emoticon: Option<i32> = None;

    // The `if let` construct reads: "if `let` destructures `number` into
    // `Some(i)`, evaluate the block (`{}`).
    if let Some(i) = number {
        println!("Matched {:?}!", i);
    }

    // If you need to specify a failure, use an else:
    if let Some(i) = letter {
        println!("Matched {:?}!", i);
    } else {
        // Destructure failed. Change to the failure case.
        println!("Didn't match a number. Let's go with a letter!");
    }

    // Provide an altered failing condition.
    let i_like_letters = false;

    if let Some(i) = emoticon {
        println!("Matched {:?}!", i);
    // Destructure failed. Evaluate an `else if` condition to see if the
    // alternate failure branch should be taken:
    } else if i_like_letters {
        println!("Didn't match a number. Let's go with a letter!");
    } else {
        // The condition evaluated false. This branch is the default:
        println!("I don't like letters. Let's go with an emoticon :)!");
    }
}
"#
            .to_string(),
        },
        // diagnostic_output: rustc_session::DiagnosticOutput::Default,
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
        registry: registry::Registry::new(&rustc_error_codes::DIAGNOSTICS),
    };
    rustc_interface::run_compiler(config, |compiler| {
        compiler.enter(|queries| {
            // TODO: add this to -Z unpretty
            let ast_krate = queries.parse().unwrap().take();
            for item in ast_krate.items {
                println!("item {}", item_to_string(&item));
            }

            // Analyze the crate and inspect the types under the cursor.
            queries.global_ctxt().unwrap().take().enter(|tcx| {
                // Every compilation contains a single crate.
                let hir_krate = tcx.hir();

                let top_level = compile_top_level(tcx);
                println!("Coq AST: {:#?}", top_level);
                // println!("Printed Coq:\n```coq\n{}\n```", top_level);

                // Iterate over the top-level items in the crate, looking for the main function.
                for id in hir_krate.items() {
                    let item = hir_krate.item(id);
                    // Use pattern-matching to find a specific node inside the main function.
                    if let rustc_hir::ItemKind::Fn(_, _, body_id) = item.kind {
                        print!("in function id {body_id:?}:");
                        let expr = &tcx.hir().body(body_id).value;
                        if let rustc_hir::ExprKind::Block(block, _) = expr.kind {
                            if let rustc_hir::StmtKind::Local(local) = block.stmts[0].kind {
                                if let Some(expr) = local.init {
                                    let hir_id = expr.hir_id; // hir_id identifies the string "Hello, world!"
                                    let def_id = tcx.hir().local_def_id(item.hir_id()); // def_id identifies the main function
                                    let ty = tcx.typeck(def_id).node_type(hir_id);
                                    println!("type {expr:#?}: {ty:?}");
                                }
                            }
                        }
                    }
                }
            })
        });
    });
}

// #[derive(Debug)]
// struct WithMut {
//     first: i32,
//     second: i32,
// }

// fn increment(n: &mut i32) -> &mut i32 {
//     *n = *n + 1;
//     n
// }

// fn increment_in_mut(s: &WithMut) -> WithMut {
//     WithMut {
//         first: s.first + 1,
//         ..*s
//     }
// }

// fn main() {
//     println!("Hello, world!");
//     let mut n = 12;
//     let n = increment(&mut n);
//     // println!("increment: {}", );
//     println!("n: {}", n);
//     let s = WithMut {first: 10, second: 11};
//     println!("s: {:?}", s);
//     let s = increment_in_mut(&s);
//     println!("s: {:?}", s);
// }
