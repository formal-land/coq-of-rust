use crate::path::*;
use crate::render::*;

use rustc_ast::LitKind;
use rustc_hir::{Pat, PatKind};

#[derive(Debug)]
pub enum StructOrVariant {
    Struct,
    Variant,
}

impl StructOrVariant {
    /// Returns wether a qpath refers to a struct or a variant.
    fn of_qpath(qpath: &rustc_hir::QPath) -> StructOrVariant {
        match qpath {
            rustc_hir::QPath::Resolved(_, path) => match path.res {
                rustc_hir::def::Res::Def(rustc_hir::def::DefKind::Struct, _) => {
                    StructOrVariant::Struct
                }
                rustc_hir::def::Res::Def(rustc_hir::def::DefKind::Variant, _) => {
                    StructOrVariant::Variant
                }
                _ => panic!("Unexpected path resolution: {:?}", path.res),
            },
            rustc_hir::QPath::TypeRelative(..) => panic!("Unhandled qpath: {qpath:?}"),
            rustc_hir::QPath::LangItem(lang_item, ..) => match lang_item {
                rustc_hir::LangItem::OptionNone => StructOrVariant::Variant,
                rustc_hir::LangItem::OptionSome => StructOrVariant::Variant,
                rustc_hir::LangItem::ResultOk => StructOrVariant::Variant,
                rustc_hir::LangItem::ResultErr => StructOrVariant::Variant,
                rustc_hir::LangItem::ControlFlowContinue => StructOrVariant::Variant,
                rustc_hir::LangItem::ControlFlowBreak => StructOrVariant::Variant,
                _ => panic!("Unhandled lang item: {lang_item:?}. TODO: add support for this item"),
            },
        }
    }
}

/// The enum [Pat] represents the patterns which can be matched
#[derive(Debug)]
pub enum Pattern {
    Wild,
    Binding(String),
    Struct(Path, Vec<(String, Pattern)>, StructOrVariant),
    TupleStruct(Path, Vec<Pattern>),
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
            Pattern::Struct(path, pats, struct_or_variant)
        }
        PatKind::TupleStruct(qpath, pats, _) => {
            let path = compile_qpath(qpath);
            let pats = pats.iter().map(compile_pattern).collect();
            Pattern::TupleStruct(path, pats)
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
            Pattern::Struct(path, fields, struct_or_variant) => group([
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
            Pattern::TupleStruct(path, fields) => {
                return nest([
                    path.to_doc(),
                    text(".Build_t"),
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
