extern crate rustc_ast;
extern crate rustc_hir;

use crate::path::*;
use crate::render::*;
use pretty::RcDoc;

/// The enum [Pat] represents the patterns which can be matched
#[derive(Debug)]
pub enum Pattern {
    Wild,
    Struct(Path, Vec<(String, Pattern)>),
    TupleStruct(Path, Vec<Pattern>),
    Or(Vec<Pattern>),
    Path(Path),
    Tuple(Vec<Pattern>),
    Lit(rustc_ast::LitKind),
}

/// The function [compile_pattern] translates a hir pattern to a coq-of-rust pattern.
pub fn compile_pattern(pat: &rustc_hir::Pat) -> Pattern {
    match &pat.kind {
        rustc_hir::PatKind::Wild => Pattern::Wild,
        rustc_hir::PatKind::Binding(_, _, ident, _) => {
            Pattern::Path(Path::local(ident.name.to_string()))
        }
        rustc_hir::PatKind::Struct(qpath, pats, _) => {
            let path = compile_qpath(qpath);
            let pats = pats
                .iter()
                .map(|pat| (pat.ident.name.to_string(), compile_pattern(pat.pat)))
                .collect();
            Pattern::Struct(path, pats)
        }
        rustc_hir::PatKind::TupleStruct(qpath, pats, _) => {
            let path = compile_qpath(qpath);
            let pats = pats.iter().map(compile_pattern).collect();
            Pattern::TupleStruct(path, pats)
        }
        rustc_hir::PatKind::Or(pats) => Pattern::Or(pats.iter().map(compile_pattern).collect()),
        rustc_hir::PatKind::Path(qpath) => Pattern::Path(compile_qpath(qpath)),
        rustc_hir::PatKind::Tuple(pats, _) => {
            Pattern::Tuple(pats.iter().map(compile_pattern).collect())
        }
        rustc_hir::PatKind::Box(pat) => compile_pattern(pat),
        rustc_hir::PatKind::Ref(pat, _) => compile_pattern(pat),
        rustc_hir::PatKind::Lit(expr) => match expr.kind {
            rustc_hir::ExprKind::Lit(ref lit) => Pattern::Lit(lit.node.clone()),
            _ => Pattern::Wild,
        },
        rustc_hir::PatKind::Range(_, _, _) => Pattern::Wild,
        rustc_hir::PatKind::Slice(_, _, _) => Pattern::Wild,
    }
}

impl Pattern {
    pub fn to_doc(&self) -> RcDoc<()> {
        match self {
            Pattern::Wild => RcDoc::text("_"),
            Pattern::Struct(path, fields) => {
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
            Pattern::TupleStruct(path, fields) => {
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
            Pattern::Or(pats) => paren(
                true,
                RcDoc::intersperse(pats.iter().map(|pat| pat.to_doc()), RcDoc::text("|")),
            ),
            Pattern::Path(path) => path.to_doc(),
            Pattern::Tuple(pats) => paren(
                true,
                RcDoc::intersperse(pats.iter().map(|pat| pat.to_doc()), RcDoc::text(",")),
            ),
            Pattern::Lit(literal) => RcDoc::text(format!("{literal:?}")),
        }
    }
}
