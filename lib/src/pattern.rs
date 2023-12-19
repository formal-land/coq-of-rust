use crate::path::*;
use crate::render::*;

use rustc_ast::LitKind;

/// The enum [Pat] represents the patterns which can be matched
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) enum Pattern {
    Wild,
    Variable(String),
    Binding(String, Box<Pattern>),
    StructStruct(Path, Vec<(String, Pattern)>, StructOrVariant),
    StructTuple(Path, Vec<Pattern>, StructOrVariant),
    Or(Vec<Pattern>),
    Tuple(Vec<Pattern>),
    #[allow(dead_code)]
    Lit(LitKind),
    // TODO: modify if necessary to fully implement the case of Slice in compile_pattern below
    Slice {
        init_patterns: Vec<Pattern>,
        slice_pattern: Option<Box<Pattern>>,
    },
}

impl Pattern {
    /// Returns wether a pattern is a single binding, to know if we need a quote
    /// in the "let" in Coq.
    pub(crate) fn is_single_binding(&self) -> bool {
        matches!(self, Pattern::Variable(_) | Pattern::Wild)
    }

    pub(crate) fn get_bindings(&self) -> Vec<String> {
        match self {
            Pattern::Wild => vec![],
            Pattern::Variable(name) => vec![name.clone()],
            Pattern::Binding(name, pattern) => {
                vec![vec![name.clone()], pattern.get_bindings()].concat()
            }
            Pattern::StructStruct(_, fields, _) => fields
                .iter()
                .flat_map(|(_, pattern)| pattern.get_bindings())
                .collect(),
            Pattern::StructTuple(_, patterns, _) => {
                patterns.iter().flat_map(Pattern::get_bindings).collect()
            }
            Pattern::Or(patterns) => optional_insert_vec(
                patterns.is_empty(),
                patterns.first().unwrap().get_bindings(),
            ),
            Pattern::Tuple(patterns) => patterns.iter().flat_map(Pattern::get_bindings).collect(),
            Pattern::Lit(_) => vec![],
            Pattern::Slice {
                init_patterns,
                slice_pattern,
            } => vec![
                init_patterns
                    .iter()
                    .flat_map(Pattern::get_bindings)
                    .collect(),
                match slice_pattern {
                    None => vec![],
                    Some(pattern) => pattern.get_bindings(),
                },
            ]
            .concat(),
        }
    }

    pub(crate) fn to_doc(&self) -> Doc {
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
                optional_insert(
                    fields.is_empty(),
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
                    ]),
                ),
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
            Pattern::Tuple(pats) => paren(
                true,
                nest([intersperse(
                    pats.iter().map(|pat| pat.to_doc()),
                    [text(","), line()],
                )]),
            ),
            Pattern::Lit(literal) => literal_to_doc(false, literal, false),
            Pattern::Slice {
                init_patterns,
                slice_pattern,
            } => {
                let pats: Vec<Doc> = init_patterns.iter().map(|pat| pat.to_doc()).collect();
                match slice_pattern {
                    Some(slice_pattern) => nest([
                        text("("),
                        intersperse(
                            [pats, vec![slice_pattern.to_doc()]].concat(),
                            [text("::"), line()],
                        ),
                        text(")"),
                    ]),
                    None => nest([text("["), intersperse(pats, [text(";"), line()]), text("]")]),
                }
            }
        }
    }
}
