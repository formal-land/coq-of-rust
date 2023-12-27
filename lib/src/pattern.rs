use crate::path::*;
use crate::render::*;
use rustc_ast::LitKind;
use std::rc::Rc;

/// The enum [Pat] represents the patterns which can be matched
#[derive(Debug, Eq, Hash, PartialEq)]
pub(crate) enum Pattern {
    Wild,
    Binding {
        name: String,
        is_with_ref: bool,
        pattern: Option<Rc<Pattern>>,
    },
    StructStruct(Path, Vec<(String, Rc<Pattern>)>, StructOrVariant),
    StructTuple(Path, Vec<Rc<Pattern>>, StructOrVariant),
    Deref(Rc<Pattern>),
    Or(Vec<Rc<Pattern>>),
    Tuple(Vec<Rc<Pattern>>),
    #[allow(dead_code)]
    Lit(LitKind),
    // TODO: modify if necessary to fully implement the case of Slice in compile_pattern below
    Slice {
        init_patterns: Vec<Rc<Pattern>>,
        slice_pattern: Option<Rc<Pattern>>,
    },
}

impl Pattern {
    /// Returns wether a pattern is a single binding, to know if we need a quote
    /// in the "let" in Coq.
    pub(crate) fn is_single_binding(&self) -> bool {
        matches!(self, Pattern::Binding { pattern: None, .. } | Pattern::Wild)
    }

    pub(crate) fn get_bindings(&self) -> Vec<String> {
        match self {
            Pattern::Wild => vec![],
            Pattern::Binding {
                name,
                is_with_ref: _,
                pattern,
            } => vec![
                vec![name.clone()],
                pattern
                    .as_ref()
                    .map_or(vec![], |pattern| pattern.get_bindings()),
            ]
            .concat(),
            Pattern::StructStruct(_, fields, _) => fields
                .iter()
                .flat_map(|(_, pattern)| pattern.get_bindings())
                .collect(),
            Pattern::StructTuple(_, patterns, _) => patterns
                .iter()
                .flat_map(|pattern| pattern.get_bindings())
                .collect(),
            Pattern::Deref(pattern) => pattern.get_bindings(),
            Pattern::Or(patterns) => optional_insert_vec(
                patterns.is_empty(),
                patterns.first().unwrap().get_bindings(),
            ),
            Pattern::Tuple(patterns) => patterns
                .iter()
                .flat_map(|pattern| pattern.get_bindings())
                .collect(),
            Pattern::Lit(_) => vec![],
            Pattern::Slice {
                init_patterns,
                slice_pattern,
            } => vec![
                init_patterns
                    .iter()
                    .flat_map(|pattern| pattern.get_bindings())
                    .collect(),
                match slice_pattern {
                    None => vec![],
                    Some(pattern) => pattern.get_bindings(),
                },
            ]
            .concat(),
        }
    }

    pub(crate) fn to_doc(&self, with_paren: bool) -> Doc {
        match self {
            Pattern::Wild => text("_"),
            Pattern::Binding {
                name,
                is_with_ref: _,
                pattern,
            } => match pattern {
                None => text(name),
                Some(pattern) => nest([
                    text("("),
                    pattern.to_doc(false),
                    text(" as"),
                    line(),
                    text(name),
                    text(")"),
                ]),
            },
            Pattern::StructStruct(path, fields, struct_or_variant) => paren(
                with_paren
                    && matches!(struct_or_variant, StructOrVariant::Variant)
                    && !fields.is_empty(),
                group([
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
                                            pattern.to_doc(false),
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
            ),
            Pattern::StructTuple(path, fields, struct_or_variant) => paren(
                with_paren && !fields.is_empty(),
                nest([
                    path.to_doc(),
                    match struct_or_variant {
                        StructOrVariant::Variant => nil(),
                        StructOrVariant::Struct => text(".Build_t"),
                    },
                    concat(
                        fields
                            .iter()
                            .map(|field| concat([line(), field.to_doc(true)])),
                    ),
                ]),
            ),
            Pattern::Deref(pattern) => pattern.to_doc(with_paren),
            Pattern::Or(pats) => paren(
                with_paren,
                nest([intersperse(
                    pats.iter().map(|pat| pat.to_doc(true)),
                    [text(" |"), line()],
                )]),
            ),
            Pattern::Tuple(pats) => paren(
                true,
                nest([intersperse(
                    pats.iter().map(|pat| pat.to_doc(false)),
                    [text(","), line()],
                )]),
            ),
            Pattern::Lit(literal) => literal_to_doc(false, literal, false),
            Pattern::Slice {
                init_patterns,
                slice_pattern,
            } => {
                let pats: Vec<Doc> = init_patterns.iter().map(|pat| pat.to_doc(false)).collect();
                match slice_pattern {
                    Some(slice_pattern) => nest([
                        text("("),
                        intersperse(
                            [pats, vec![slice_pattern.to_doc(false)]].concat(),
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
