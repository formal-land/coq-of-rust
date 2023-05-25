use crate::path::*;
use crate::pattern::*;
use crate::render::*;
use crate::ty::*;

use rustc_ast::LitKind;
use rustc_hir::{BinOp, BinOpKind, ExprKind, QPath};
use rustc_middle::ty::TyCtxt;

/// Struct [FreshVars] represents a set of fresh variables
#[derive(Debug)]
pub struct FreshVars(u64);

impl Default for FreshVars {
    fn default() -> Self {
        Self::new()
    }
}

impl FreshVars {
    pub fn new() -> Self {
        FreshVars(0)
    }

    fn next(&mut self) -> String {
        let x = self.0;
        self.0 += 1;
        format!("α{}", x)
    }

    fn reset(&mut self) {
        self.0 = 0
    }
}

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
    Let {
        modifier: &'static str,
        /// this is appended to the let keyword during the translation
        /// use "" for normal let, "*" for monadic, etc
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

pub fn mt_boxed_expression(mut bexpr: Box<Expr>, fresh_vars: &mut FreshVars) -> Box<Expr> {
    *bexpr = mt_expression(*bexpr, fresh_vars);
    bexpr
}

pub fn mt_expressions(exprs: Vec<Expr>, fresh_vars: &mut FreshVars) -> Vec<Expr> {
    exprs
        .into_iter()
        .map(|expr| mt_expression(expr, fresh_vars))
        .collect()
}

/// Monadic transalte function call
///
/// MT(f(a, b, ...))
/// -----------------
/// let f' = MT(f);
/// let a' = MT(a);
/// let b'; = MT(b);
/// ...
/// f'(a', b', ...)
fn mt_call(func: Expr, args: Vec<Expr>, fresh_vars: &mut FreshVars) -> Expr {
    let mut let_vars: Vec<(Pattern, Expr)> = vec![];
    // Create one variable for the function
    let fname = fresh_vars.next();
    // Create one variable for each argument, take
    // the oportunity to apply mt_expression into it
    let args = args
        .into_iter()
        .map(|expr| {
            let vname = fresh_vars.next();
            let_vars.push((Pattern::Variable(vname.clone()), expr));
            Expr::Var(Path::local(vname))
        })
        .collect();
    // We're creating a (let ... (let ... (let ... fcall))) expression,
    // this is the body of the most nested let. It is the function call
    // with all arguments (including the function itself) bound to variables
    let fcall = Expr::Call {
        func: Box::new(Expr::Var(Path::local(fname.clone()))),
        args,
    };
    // the nested lets
    let nested_lets = let_vars.into_iter().rev().fold(fcall, |acc, (pat, expr)| {
        mt_let("*", pat, expr, acc, fresh_vars)
    });
    // f(Pure a)
    // the outter let
    mt_let("*", Pattern::Variable(fname), func, nested_lets, fresh_vars)
}

fn pure(e: Expr) -> Expr {
    Expr::Pure(Box::new(e))
}

/// let a = (let b = c in d) in e
/// ----------------------------------
/// let b = c in
/// let a = d in
/// e
fn mt_let(
    modifier: &'static str,
    pat: Pattern,
    init: Expr,
    body: Expr,
    fresh_vars: &mut FreshVars,
) -> Expr {
    match init {
        Expr::Let {
            modifier: "*",
            pat: inner_pat,
            init: inner_init,
            body: inner_body,
        } => mt_let(
            "*",
            inner_pat,
            mt_expression(*inner_init, fresh_vars),
            mt_let("*", pat, *inner_body, body, fresh_vars),
            fresh_vars,
        ),
        init => Expr::Let {
            modifier,
            pat,
            init: Box::new(init),
            body: Box::new(body),
        },
    }
}

fn mt_match(scrutinee: Expr, arms: Vec<MatchArm>, fresh_vars: &mut FreshVars) -> Expr {
    let vname = fresh_vars.next();
    let pat = Pattern::Variable(vname.clone());
    Expr::Let {
        modifier: "*",
        pat,
        init: Box::new(scrutinee),
        body: Box::new(Expr::Match {
            scrutinee: Box::new(Expr::LocalVar(vname)),
            arms,
        }),
    }
}

// @TODO add the translation logic (right now is just an ineficient identity)
pub fn mt_expression(expr: Expr, fresh_vars: &mut FreshVars) -> Expr {
    match expr {
        Expr::Pure(x) => Expr::Pure(x),
        Expr::LocalVar(x) => pure(Expr::LocalVar(x)),
        Expr::Var(x) => pure(Expr::Var(x)),
        // @TODO how to transform associated function?
        Expr::AssociatedFunction { ty, func } => Expr::AssociatedFunction { ty, func },
        Expr::Literal(x) => pure(Expr::Literal(x)),
        Expr::AddrOf(box_expr) => pure(Expr::AddrOf(mt_boxed_expression(box_expr, fresh_vars))),
        Expr::Call { func, args } => mt_call(
            mt_expression(*func, fresh_vars),
            mt_expressions(args, fresh_vars),
            fresh_vars,
        ),
        // @TODO I guess method call transformation should be similar to
        // function application transformation
        Expr::MethodCall { object, func, args } => Expr::MethodCall {
            object: mt_boxed_expression(object, fresh_vars),
            func,
            args: mt_expressions(args, fresh_vars),
        },
        Expr::Let {
            modifier,
            pat,
            init,
            body,
        } => mt_let(
            modifier,
            pat,
            mt_expression(*init, fresh_vars),
            mt_expression(*body, fresh_vars),
            fresh_vars,
        ),
        Expr::Lambda { args, body } => pure(Expr::Lambda {
            args,
            body: mt_boxed_expression(body, fresh_vars),
        }),
        Expr::Seq { first, second } => Expr::Let {
            modifier: "*",
            pat: Pattern::Variable(String::from("_")),
            init: mt_boxed_expression(first, fresh_vars),
            body: {
                fresh_vars.reset();
                mt_boxed_expression(second, fresh_vars)
            },
        },
        Expr::Cast { expr, ty } => Expr::Cast {
            expr: mt_boxed_expression(expr, fresh_vars),
            ty,
        },
        Expr::Type { expr, ty } => Expr::Type {
            expr: mt_boxed_expression(expr, fresh_vars),
            ty,
        },
        Expr::Array { elements } => Expr::Array {
            elements: mt_expressions(elements, fresh_vars),
        },
        Expr::Tuple { elements } => Expr::Tuple {
            elements: mt_expressions(elements, fresh_vars),
        },
        Expr::LetIf { pat, init } => Expr::LetIf {
            pat,
            init: mt_boxed_expression(init, fresh_vars),
        },
        Expr::If {
            condition,
            success,
            failure,
        } => {
            let vname = fresh_vars.next();
            Expr::Let {
                modifier: "*",
                pat: Pattern::Variable(vname.clone()),
                init: mt_boxed_expression(condition, fresh_vars),
                body: Box::new(Expr::If {
                    condition: Box::new(Expr::LocalVar(vname)),
                    success: mt_boxed_expression(success, fresh_vars),
                    failure: mt_boxed_expression(failure, fresh_vars),
                }),
            }
        }
        Expr::Loop { body, loop_source } => Expr::Loop {
            body: mt_boxed_expression(body, fresh_vars),
            loop_source,
        },
        Expr::Match { scrutinee, arms } => mt_match(
            mt_expression(*scrutinee, fresh_vars),
            arms.into_iter()
                .map(|arm| MatchArm {
                    body: mt_expression(arm.body, fresh_vars),
                    ..arm
                })
                .collect(),
            fresh_vars,
        ),
        Expr::Assign { left, right } => Expr::Assign {
            left: mt_boxed_expression(left, fresh_vars),
            right: mt_boxed_expression(right, fresh_vars),
        },
        Expr::IndexedField { base, index } => Expr::IndexedField {
            base: mt_boxed_expression(base, fresh_vars),
            index,
        },
        Expr::NamedField { base, name } => Expr::NamedField {
            base: mt_boxed_expression(base, fresh_vars),
            name,
        },
        Expr::Index { base, index } => Expr::Index {
            base: mt_boxed_expression(base, fresh_vars),
            index,
        },
        Expr::StructStruct {
            path,
            fields,
            base,
            struct_or_variant,
        } => Expr::StructStruct {
            path,
            fields: fields
                .into_iter()
                .map(|(s, field)| (s, mt_expression(field, fresh_vars)))
                .collect(),
            base: base.map(|b| mt_boxed_expression(b, fresh_vars)),
            struct_or_variant,
        },
        Expr::StructTuple { path, fields } => Expr::StructTuple {
            path,
            fields: mt_expressions(fields, fresh_vars),
        },
        Expr::StructUnit { path } => Expr::StructUnit { path },
    }
}

pub fn compile_expr(tcx: TyCtxt, expr: &rustc_hir::Expr) -> Expr {
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
                // Check if we are calling a constructor
                ExprKind::Path(rustc_hir::QPath::Resolved(
                    _,
                    path @ rustc_hir::Path {
                        res:
                            rustc_hir::def::Res::Def(
                                rustc_hir::def::DefKind::Ctor(rustc_hir::def::CtorOf::Struct, _),
                                _,
                            ),
                        ..
                    },
                )) => Expr::StructTuple {
                    path: compile_path(path),
                    fields: args,
                },
                _ => {
                    let func = Box::new(compile_expr(tcx, func));
                    Expr::Call { func, args }
                }
            }
        }
        ExprKind::MethodCall(path_segment, object, args, _) => {
            let object = compile_expr(tcx, object);
            let func = path_segment.ident.to_string();
            let args: Vec<_> = args.iter().map(|expr| compile_expr(tcx, expr)).collect();
            Expr::MethodCall {
                object: Box::new(object),
                func,
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
            Expr::MethodCall {
                object: Box::new(expr_left),
                func,
                args: vec![expr_right],
            }
        }
        ExprKind::Unary(un_op, expr) => {
            let expr = compile_expr(tcx, expr);
            let func = compile_un_op(un_op);
            Expr::MethodCall {
                object: Box::new(expr),
                func,
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
            Expr::MethodCall {
                object: Box::new(left),
                func,
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
        ExprKind::Break(_, _) => Expr::LocalVar("Break".to_string()),
        ExprKind::Continue(_) => Expr::LocalVar("Continue".to_string()),
        ExprKind::Ret(expr) => {
            let func = Box::new(Expr::LocalVar("Return".to_string()));
            let args = match expr {
                Some(expr) => vec![compile_expr(tcx, expr)],
                None => vec![],
            };
            Expr::Call { func, args }
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
                func: Box::new(Expr::LocalVar("repeat".to_string())),
                args: vec![expr],
            }
        }
        ExprKind::Yield(expr, _) => {
            let expr = compile_expr(tcx, expr);
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
                Expr::Let {
                    modifier: "",
                    pat,
                    init,
                    body,
                }
            }
            // We ignore "Item" as we do not know yet how to handle them / what they are for.
            rustc_hir::StmtKind::Item(_) => compile_stmts(tcx, stmts, expr),
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
            Expr::Pure(x) => paren(with_paren, nest([text("Pure "), x.to_doc(false)])),
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
            Expr::Let {
                modifier,
                pat,
                init,
                body,
            } => group([
                nest([
                    nest([
                        text(format!("let{}", modifier)),
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
            Expr::StructTuple { path, fields } => paren(
                with_paren,
                nest([
                    path.to_doc(),
                    text(".Build_t"),
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
