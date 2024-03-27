use crate::expression::*;
use crate::path::*;
use itertools::Itertools;
use std::rc::Rc;
use std::vec;

/// The enum [Pat] represents the patterns which can be matched
#[derive(Debug)]
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
    Literal(Rc<Literal>),
    Slice {
        prefix_patterns: Vec<Rc<Pattern>>,
        slice_pattern: Option<Rc<Pattern>>,
        suffix_patterns: Vec<Rc<Pattern>>,
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
            Pattern::Literal(_) => vec![self.clone()],
            Pattern::Slice {
                prefix_patterns,
                slice_pattern,
                suffix_patterns,
            } => Pattern::multi_cartesian_product_with_empty_case(
                prefix_patterns
                    .iter()
                    .map(|prefix_pattern| prefix_pattern.flatten_ors()),
            )
            .into_iter()
            .zip(Pattern::multi_cartesian_product_with_empty_case(
                suffix_patterns
                    .iter()
                    .map(|suffix_pattern| suffix_pattern.flatten_ors()),
            ))
            .flat_map(|(prefix_patterns, suffix_patterns)| match slice_pattern {
                None => vec![Rc::new(Pattern::Slice {
                    prefix_patterns,
                    slice_pattern: None,
                    suffix_patterns,
                })],
                Some(slice_pattern) => slice_pattern
                    .flatten_ors()
                    .into_iter()
                    .map(|slice_pattern| {
                        Rc::new(Pattern::Slice {
                            prefix_patterns: prefix_patterns.clone(),
                            slice_pattern: Some(slice_pattern),
                            suffix_patterns: suffix_patterns.clone(),
                        })
                    })
                    .collect(),
            })
            .collect(),
        }
    }
}
