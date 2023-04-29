use crate::path::*;
use crate::render::*;

use rustc_ast::LitKind;
use rustc_hir::{Pat, PatKind};

/// The enum [Pat] represents the patterns which can be matched
#[derive(Debug)]
pub enum Pattern {
    Wild,
    Binding(String),
    StructStruct(Path, Vec<(String, Pattern)>, StructOrVariant),
    StructTuple(Path, Vec<Pattern>, StructOrVariant),
    Or(Vec<Pattern>),
    Path(Path),
    Tuple(Vec<Pattern>),
    Lit(LitKind),
}

/// The function [compile_pattern] translates a hir pattern to a coq-of-rust pattern.
pub fn compile_pattern(pat: &Pat) -> Pattern {
    match &pat.kind {
        PatKind::Wild => Pattern::Wild,
        PatKind::Binding(_, _, ident, _) => Pattern::Binding(ident.name.to_string()),
        PatKind::Struct(qpath, pats, _) => {
            let path = compile_qpath(qpath);
            let pats = pats
                .iter()
                .map(|pat| (pat.ident.name.to_string(), compile_pattern(pat.pat)))
                .collect();
            let struct_or_variant = StructOrVariant::of_qpath(qpath);
            Pattern::StructStruct(path, pats, struct_or_variant)
        }
        PatKind::TupleStruct(qpath, pats, _) => {
            let path = compile_qpath(qpath);
            let pats = pats.iter().map(compile_pattern).collect();
            let struct_or_variant = StructOrVariant::of_qpath(qpath);
            Pattern::StructTuple(path, pats, struct_or_variant)
        }
        PatKind::Or(pats) => Pattern::Or(pats.iter().map(compile_pattern).collect()),
        PatKind::Path(qpath) => Pattern::Path(compile_qpath(qpath)),
        PatKind::Tuple(pats, _) => Pattern::Tuple(pats.iter().map(compile_pattern).collect()),
        PatKind::Box(pat) => compile_pattern(pat),
        PatKind::Ref(pat, _) => compile_pattern(pat),
        PatKind::Lit(expr) => match expr.kind {
            rustc_hir::ExprKind::Lit(ref lit) => Pattern::Lit(lit.node.clone()),
            _ => Pattern::Wild,
        },
        PatKind::Range(_, _, _) => Pattern::Wild,
        PatKind::Slice(_, _, _) => Pattern::Wild,
    }
}

impl Pattern {
    /// Returns wether a pattern is a single binding, to know if we need a quote
    /// in the "let" in Coq.
    pub fn is_single_binding(&self) -> bool {
        matches!(self, Pattern::Binding(_))
    }

    pub fn to_doc(&self) -> Doc {
        match self {
            Pattern::Wild => text("_"),
            Pattern::Binding(name) => text(name),
            Pattern::StructStruct(path, fields, struct_or_variant) => group([
                match struct_or_variant {
                    StructOrVariant::Struct => nil(),
                    StructOrVariant::Variant => path.to_doc(),
                },
                if fields.is_empty() {
                    nil()
                } else {
                    concat([
                        match struct_or_variant {
                            StructOrVariant::Struct => nil(),
                            StructOrVariant::Variant => line(),
                        },
                        nest([
                            text("{|"),
                            line(),
                            intersperse(
                                fields.iter().map(|(name, pattern)| {
                                    nest([
                                        path.to_doc(),
                                        text("."),
                                        text(name),
                                        line(),
                                        text(":="),
                                        line(),
                                        pattern.to_doc(),
                                        text(";"),
                                    ])
                                }),
                                [line()],
                            ),
                        ]),
                        line(),
                        text("|}"),
                    ])
                },
            ]),
            Pattern::StructTuple(path, fields, struct_or_variant) => {
                return nest([
                    path.to_doc(),
                    match struct_or_variant {
                        StructOrVariant::Variant => nil(),
                        StructOrVariant::Struct => text(".Build_t"),
                    },
                    line(),
                    nest([intersperse(
                        fields.iter().map(|field| field.to_doc()),
                        [line()],
                    )]),
                ]);
            }
            Pattern::Or(pats) => paren(
                true,
                intersperse(pats.iter().map(|pat| pat.to_doc()), [text("|")]),
            ),
            Pattern::Path(path) => path.to_doc(),
            Pattern::Tuple(pats) => paren(
                true,
                nest([intersperse(
                    pats.iter().map(|pat| pat.to_doc()),
                    [text(","), line()],
                )]),
            ),
            Pattern::Lit(literal) => text(format!("{literal:?}")),
        }
    }
}
