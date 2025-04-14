use crate::env::emit_warning_with_note;
use crate::env::Env;
use crate::expression::*;
use crate::path::*;
use crate::ty::*;
use serde::Serialize;
use std::rc::Rc;
use std::vec;

/// This enum represents the patterns which can be matched
#[derive(Debug, Serialize)]
pub(crate) enum Pattern {
    Wild,
    Binding {
        name: String,
        ty: Rc<CoqType>,
        is_with_ref: bool,
        pattern: Option<Rc<Pattern>>,
    },
    StructRecord(Rc<Path>, Vec<(String, Rc<Pattern>)>),
    StructTuple(Rc<Path>, Vec<Rc<Pattern>>),
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
    /// This function is a bit redundant with [crate::thir_pattern::compile_pattern]. It is used to
    /// translate the patterns in HIR form, that appear only in function parameters. In particular,
    /// these patterns should always be exhaustive, so we do not need to handle all the cases.
    pub(crate) fn compile(env: &Env, pattern: &rustc_hir::Pat) -> Rc<Pattern> {
        match pattern.kind {
            rustc_hir::PatKind::Wild => Rc::new(Pattern::Wild),
            rustc_hir::PatKind::Binding(binding_annotation, _, ident, sub_pattern) => {
                Rc::new(Pattern::Binding {
                    name: to_valid_coq_name(IsValue::Yes, ident.as_str()),
                    ty: CoqType::path(&[
                        "Type for variables in patterns in function parameters is not handled",
                    ]),
                    is_with_ref: matches!(
                        binding_annotation,
                        rustc_hir::BindingMode(rustc_hir::ByRef::Yes(_), _)
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
            | rustc_hir::PatKind::Deref(_)
            | rustc_hir::PatKind::Range(_, _, _)
            | rustc_hir::PatKind::Slice(_, _, _)
            | rustc_hir::PatKind::Err(_) => {
                emit_warning_with_note(
                    env,
                    &pattern.span,
                    "We do not handle this kind of pattern here.",
                    Some("This should not happen as function parameter patterns should be exhaustive."),
                );

                Rc::new(Pattern::Literal(Rc::new(Literal::Error)))
            }
        }
    }

    /// We return a vector, and we know that each variable of this vector is unique
    /// as we can only bound a variable once in a pattern.
    pub(crate) fn get_free_vars(&self) -> Vec<(String, Rc<CoqType>)> {
        match self {
            Pattern::Wild => vec![],
            Pattern::Binding {
                name,
                ty,
                is_with_ref: _,
                pattern,
            } => {
                let mut free_vars = vec![(name.clone(), ty.clone())];

                if let Some(pattern) = pattern {
                    free_vars.extend(pattern.get_free_vars());
                }

                free_vars
            }
            Pattern::StructRecord(_, fields) => fields
                .iter()
                .flat_map(|(_, pattern)| pattern.get_free_vars())
                .collect(),
            Pattern::StructTuple(_, patterns) => patterns
                .iter()
                .flat_map(|pattern| pattern.get_free_vars())
                .collect(),
            Pattern::Deref(pattern) => pattern.get_free_vars(),
            Pattern::Or(patterns) => match &patterns[..] {
                [] => vec![],
                // All branches must have the same free variables.
                [pattern, ..] => pattern.get_free_vars(),
            },
            Pattern::Tuple(patterns) => patterns
                .iter()
                .flat_map(|pattern| pattern.get_free_vars())
                .collect(),
            Pattern::Literal(_) => vec![],
            Pattern::Slice {
                prefix_patterns,
                slice_pattern,
                suffix_patterns,
            } => prefix_patterns
                .iter()
                .flat_map(|pattern| pattern.get_free_vars())
                .chain(
                    slice_pattern
                        .as_ref()
                        .map_or(vec![], |pattern| pattern.get_free_vars()),
                )
                .chain(
                    suffix_patterns
                        .iter()
                        .flat_map(|pattern| pattern.get_free_vars()),
                )
                .collect(),
        }
    }
}
