use crate::path::*;
use crate::render::*;
use itertools::Itertools;
use rustc_ast::LitKind;
use std::rc::Rc;
use std::vec;

/// The enum [Pat] represents the patterns which can be matched
#[derive(Debug, Eq, Hash, PartialEq)]
pub(crate) enum Pattern {
    Wild,
    Binding {
        name: String,
        /// Wether the reference is mutable, if any
        is_with_ref: Option<bool>,
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
    /// Because the function from the standard library returns nothing instead
    /// of an empty iterator when the input is empty.
    fn multi_cartesian_product_with_empty_case<A: Iterator>(
        iterator: A,
    ) -> Vec<Vec<<A::Item as IntoIterator>::Item>>
    where
        A: Sized,
        A::Item: IntoIterator,
        <A::Item as IntoIterator>::IntoIter: Clone,
        <A::Item as IntoIterator>::Item: Clone,
    {
        let combinations = iterator.multi_cartesian_product().collect::<Vec<_>>();
        if combinations.is_empty() {
            vec![vec![]]
        } else {
            combinations
        }
    }

    pub(crate) fn flatten_ors(self: &Rc<Pattern>) -> Vec<Rc<Pattern>> {
        match self.as_ref() {
            Pattern::Wild => vec![self.clone()],
            Pattern::Binding {
                name,
                is_with_ref,
                pattern,
            } => match pattern {
                None => vec![self.clone()],
                Some(pattern) => pattern
                    .flatten_ors()
                    .into_iter()
                    .map(|pattern| {
                        Rc::new(Pattern::Binding {
                            name: name.clone(),
                            is_with_ref: *is_with_ref,
                            pattern: Some(pattern),
                        })
                    })
                    .collect(),
            },
            Pattern::StructStruct(path, fields, struct_or_variant) => {
                Pattern::multi_cartesian_product_with_empty_case(fields.iter().map(
                    |(name, pattern)| {
                        pattern
                            .flatten_ors()
                            .into_iter()
                            .map(|pattern| (name.clone(), pattern))
                    },
                ))
                .into_iter()
                .map(|fields| {
                    Rc::new(Pattern::StructStruct(
                        path.clone(),
                        fields,
                        *struct_or_variant,
                    ))
                })
                .collect()
            }
            Pattern::StructTuple(path, patterns, struct_or_variant) => {
                Pattern::multi_cartesian_product_with_empty_case(
                    patterns.iter().map(|pattern| pattern.flatten_ors()),
                )
                .into_iter()
                .map(|patterns| {
                    Rc::new(Pattern::StructTuple(
                        path.clone(),
                        patterns,
                        *struct_or_variant,
                    ))
                })
                .collect()
            }
            Pattern::Deref(pattern) => pattern
                .flatten_ors()
                .into_iter()
                .map(|pattern| Rc::new(Pattern::Deref(pattern)))
                .collect(),
            Pattern::Or(patterns) => patterns
                .iter()
                .flat_map(|pattern| pattern.flatten_ors())
                .collect(),
            Pattern::Tuple(patterns) => Pattern::multi_cartesian_product_with_empty_case(
                patterns.iter().map(|pattern| pattern.flatten_ors()),
            )
            .into_iter()
            .map(|patterns| Rc::new(Pattern::Tuple(patterns)))
            .collect(),
            Pattern::Lit(_) => vec![self.clone()],
            Pattern::Slice {
                init_patterns,
                slice_pattern,
            } => Pattern::multi_cartesian_product_with_empty_case(
                init_patterns
                    .iter()
                    .map(|init_pattern| init_pattern.flatten_ors()),
            )
            .into_iter()
            .flat_map(|init_patterns| match slice_pattern {
                None => vec![Rc::new(Pattern::Slice {
                    init_patterns,
                    slice_pattern: None,
                })],
                Some(slice_pattern) => slice_pattern
                    .flatten_ors()
                    .into_iter()
                    .map(|slice_pattern| {
                        Rc::new(Pattern::Slice {
                            init_patterns: init_patterns.clone(),
                            slice_pattern: Some(slice_pattern),
                        })
                    })
                    .collect(),
            })
            .collect(),
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
                    && matches!(struct_or_variant, StructOrVariant::Variant { .. })
                    && !fields.is_empty(),
                group([
                    match struct_or_variant {
                        StructOrVariant::Struct => nil(),
                        StructOrVariant::Variant { .. } => path.to_doc(),
                    },
                    optional_insert(
                        fields.is_empty(),
                        concat([
                            match struct_or_variant {
                                StructOrVariant::Struct => nil(),
                                StructOrVariant::Variant { .. } => line(),
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
                        StructOrVariant::Variant { .. } => nil(),
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
