use crate::env::emit_warning_with_note;
use crate::env::Env;
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
    StructRecord(Path, Vec<(String, Rc<Pattern>)>),
    StructTuple(Path, Vec<Rc<Pattern>>),
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
            Pattern::StructRecord(path, fields) => {
                Pattern::multi_cartesian_product_with_empty_case(fields.iter().map(
                    |(name, pattern)| {
                        pattern
                            .flatten_ors()
                            .into_iter()
                            .map(|pattern| (name.clone(), pattern))
                    },
                ))
                .into_iter()
                .map(|fields| Rc::new(Pattern::StructRecord(path.clone(), fields)))
                .collect()
            }
            Pattern::StructTuple(path, patterns) => {
                Pattern::multi_cartesian_product_with_empty_case(
                    patterns.iter().map(|pattern| pattern.flatten_ors()),
                )
                .into_iter()
                .map(|patterns| Rc::new(Pattern::StructTuple(path.clone(), patterns)))
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

    /// This function is a bit redundant with [crate::thir_pattern::compile_pattern]. It is used to
    /// translate the patterns in HIR form, that appear only in function parameters. In particular,
    /// these patterns should always be exhaustive, so we do not need to handle all the cases.
    pub(crate) fn compile(env: &Env, pattern: &rustc_hir::Pat) -> Rc<Pattern> {
        match pattern.kind {
            rustc_hir::PatKind::Wild => Rc::new(Pattern::Wild),
            rustc_hir::PatKind::Binding(binding_annotation, _, ident, sub_pattern) => {
                Rc::new(Pattern::Binding {
                    name: ident.to_string(),
                    is_with_ref: matches!(
                        binding_annotation,
                        rustc_hir::BindingAnnotation(rustc_hir::ByRef::Yes, _)
                    ),
                    pattern: sub_pattern.map(|sub_pattern| Pattern::compile(env, sub_pattern)),
                })
            }
            rustc_hir::PatKind::Struct(qpath, fields, _) => {
                let path = compile_qpath(env, pattern.hir_id, &qpath);
                let fields = fields
                    .iter()
                    .map(|field| (field.ident.to_string(), Pattern::compile(env, field.pat)))
                    .collect();

                Rc::new(Pattern::StructRecord(path, fields))
            }
            rustc_hir::PatKind::TupleStruct(qpath, fields, _) => {
                let path = compile_qpath(env, pattern.hir_id, &qpath);
                let fields = fields
                    .iter()
                    .map(|field| Pattern::compile(env, field))
                    .collect();

                Rc::new(Pattern::StructTuple(path, fields))
            }
            rustc_hir::PatKind::Or(pats) => {
                let patterns = pats.iter().map(|pat| Pattern::compile(env, pat)).collect();

                Rc::new(Pattern::Or(patterns))
            }
            rustc_hir::PatKind::Never => Rc::new(Pattern::Or(vec![])),
            rustc_hir::PatKind::Path(qpath) => {
                let path = compile_qpath(env, pattern.hir_id, &qpath);

                Rc::new(Pattern::StructTuple(path, vec![]))
            }
            rustc_hir::PatKind::Tuple(pats, _) => {
                let patterns = pats.iter().map(|pat| Pattern::compile(env, pat)).collect();

                Rc::new(Pattern::Tuple(patterns))
            }
            rustc_hir::PatKind::Box(sub_pattern) | rustc_hir::PatKind::Ref(sub_pattern, _) => {
                Rc::new(Pattern::Deref(Pattern::compile(env, sub_pattern)))
            }
            rustc_hir::PatKind::Lit(_)
            | rustc_hir::PatKind::Range(_, _, _)
            | rustc_hir::PatKind::Slice(_, _, _) => {
                emit_warning_with_note(
                    env,
                    &pattern.span,
                    "We do not handle this kind of pattern here.",
                    "This should not happen as function parameter patterns should be exhaustive.",
                );

                Rc::new(Pattern::Literal(Rc::new(Literal::Error)))
            }
        }
    }
}
