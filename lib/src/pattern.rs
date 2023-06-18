use crate::env::*;
use crate::path::*;
use crate::render::*;

use rustc_ast::{LitIntType, LitKind};
use rustc_hir::{ExprKind, Pat, PatKind, RangeEnd};
use rustc_span::source_map::Spanned;

/// The enum [Pat] represents the patterns which can be matched
#[derive(Clone, Debug)]
pub(crate) enum Pattern {
    Wild,
    Variable(String),
    Binding(String, Box<Pattern>),
    StructStruct(Path, Vec<(String, Pattern)>, StructOrVariant),
    StructTuple(Path, Vec<Pattern>, StructOrVariant),
    Or(Vec<Pattern>),
    Path(Path),
    Tuple(Vec<Pattern>),
    Lit(LitKind),
}

/// The function [compile_pattern] translates a hir pattern to a coq-of-rust pattern.
pub(crate) fn compile_pattern(env: &Env, pat: &Pat) -> Pattern {
    match &pat.kind {
        PatKind::Wild => Pattern::Wild,
        PatKind::Binding(_, _, ident, pat) => {
            let name = ident.name.to_string();
            match pat {
                None => Pattern::Variable(ident.name.to_string()),
                Some(pat) => Pattern::Binding(name, Box::new(compile_pattern(env, pat))),
            }
        }
        PatKind::Struct(qpath, pats, _) => {
            let path = compile_qpath(env, qpath);
            let pats = pats
                .iter()
                .map(|pat| (pat.ident.name.to_string(), compile_pattern(env, pat.pat)))
                .collect();
            let struct_or_variant = StructOrVariant::of_qpath(env, qpath);
            Pattern::StructStruct(path, pats, struct_or_variant)
        }
        PatKind::TupleStruct(qpath, pats, _) => {
            let path = compile_qpath(env, qpath);
            let pats = pats.iter().map(|pat| compile_pattern(env, pat)).collect();
            let struct_or_variant = StructOrVariant::of_qpath(env, qpath);
            Pattern::StructTuple(path, pats, struct_or_variant)
        }
        PatKind::Or(pats) => {
            Pattern::Or(pats.iter().map(|pat| compile_pattern(env, pat)).collect())
        }
        PatKind::Path(qpath) => Pattern::Path(compile_qpath(env, qpath)),
        PatKind::Tuple(pats, dot_dot_pos) => {
            let mut pats = pats
                .iter()
                .map(|pat| compile_pattern(env, pat))
                .collect::<Vec<_>>();
            match dot_dot_pos.as_opt_usize() {
                None => (),
                Some(0) => pats.insert(0, Pattern::Wild),
                Some(_) => {
                    env.tcx
                        .sess
                        .struct_span_warn(
                            pat.span,
                            "Only leading `..` patterns are supported in tuple patterns.",
                        )
                        .help("Use underscore `_` patterns instead.")
                        .emit();
                }
            }
            Pattern::Tuple(pats)
        }
        PatKind::Box(pat) => compile_pattern(env, pat),
        PatKind::Ref(pat, _) => compile_pattern(env, pat),
        PatKind::Lit(expr) => match expr.kind {
            ExprKind::Lit(lit) => Pattern::Lit(lit.node.clone()),
            _ => {
                env.tcx
                    .sess
                    .struct_span_warn(
                        pat.span,
                        "Only literal expressions in patterns are supported.",
                    )
                    .help("Use an `if` statement instead.")
                    .emit();
                Pattern::Wild
            }
        },
        PatKind::Range(start, end, inclusion) => match (start, end) {
            (Some(start), Some(end)) => match (start.kind, end.kind) {
                (
                    ExprKind::Lit(Spanned {
                        node: LitKind::Int(start, _),
                        ..
                    }),
                    ExprKind::Lit(Spanned {
                        node: LitKind::Int(end, _),
                        ..
                    }),
                ) => {
                    let range = *start..=match inclusion {
                        RangeEnd::Included => *end,
                        RangeEnd::Excluded => *end - 1,
                    };
                    Pattern::Or(
                        range
                            .map(|i| Pattern::Lit(LitKind::Int(i, LitIntType::Unsuffixed)))
                            .collect(),
                    )
                }
                _ => {
                    env.tcx
                        .sess
                        .struct_span_warn(
                            pat.span,
                            "Only ranges on literal integers are supported.",
                        )
                        .help("Use an `if` statement instead.")
                        .emit();
                    Pattern::Wild
                }
            },
            (None, None) => Pattern::Wild,
            _ => {
                env.tcx
                    .sess
                    .struct_span_warn(
                        pat.span,
                        "Range patterns with an open bound are not supported.",
                    )
                    .help("Use an `if` statement instead.")
                    .emit();
                Pattern::Wild
            }
        },
        PatKind::Slice(_, _, _) => Pattern::Wild,
    }
}

impl Pattern {
    /// Returns wether a pattern is a single binding, to know if we need a quote
    /// in the "let" in Coq.
    pub fn is_single_binding(&self) -> bool {
        matches!(self, Pattern::Variable(_) | Pattern::Wild)
    }

    pub fn to_doc(&self) -> Doc {
        match self {
            Pattern::Wild => text("_"),
            Pattern::Variable(name) => text(name),
            Pattern::Binding(name, pat) => nest([
                text("("),
                pat.to_doc(),
                text(" as"),
                line(),
                text(name),
                text(")"),
            ]),
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
            Pattern::Lit(literal) => literal_to_doc(false, literal),
        }
    }
}
