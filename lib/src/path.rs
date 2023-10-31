use crate::env::*;
use crate::render::*;
use rustc_hir::def::{CtorOf, DefKind, Res};
use rustc_hir::{LangItem, QPath};
use std::fmt;
use std::vec;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct Path {
    pub(crate) segments: Vec<String>,
}

impl fmt::Display for Path {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let segments = self.segments.join("::");
        write!(f, "{segments}")
    }
}

impl Path {
    pub fn local(name: String) -> Path {
        Path {
            segments: vec![to_valid_coq_name(name)],
        }
    }

    fn prefix_last_by_impl(&mut self) {
        let last = self.segments.pop().unwrap();
        self.segments.push(format!("Impl{last}"));
    }

    pub(crate) fn new<S: ToString>(segments: &[S]) -> Self {
        Path {
            segments: segments.iter().map(|s| s.to_string()).collect(),
        }
    }

    pub(crate) fn to_doc<'a>(&self) -> Doc<'a> {
        // clone to be able to consume
        let segments = self.segments.clone();
        // consume (by into_iter) to let the result live arbitrarily long
        intersperse(segments, [text(".")])
    }

    pub(crate) fn to_name(&self) -> String {
        self.segments.join("_")
    }

    pub(crate) fn concat(paths: &[Self]) -> Self {
        Path {
            segments: paths
                .iter()
                .flat_map(|path| path.segments.to_owned())
                .collect(),
        }
    }
}

fn compile_path_without_env(path: &rustc_hir::Path) -> Path {
    Path {
        segments: path
            .segments
            .iter()
            .map(|segment| to_valid_coq_name(segment.ident.name.to_string()))
            .collect(),
    }
}

pub(crate) fn compile_def_id(env: &Env, def_id: rustc_hir::def_id::DefId) -> Path {
    let crate_name: String = env.tcx.crate_name(def_id.krate).to_string();
    let path_items = env.tcx.def_path(def_id);
    let mut segments = vec![crate_name];
    segments.extend(
        path_items
            .data
            .iter()
            .filter_map(|item| item.data.get_opt_name())
            .map(|name| to_valid_coq_name(name.to_string())),
    );
    Path { segments }
}

pub(crate) fn compile_path(env: &Env, path: &rustc_hir::Path) -> Path {
    if let Some(def_id) = path.res.opt_def_id() {
        // The type parameters should not have an absolute name, as they are not
        // not declared at top-level.
        if let Res::Def(DefKind::TyParam, _) = path.res {
            return compile_path_without_env(path);
        }
        return compile_def_id(env, def_id);
    }
    compile_path_without_env(path)
}

/// compilation of [QPath] in [LangItem] variant
fn compile_lang_item(lang_item: &LangItem) -> Path {
    Path {
        segments: match lang_item {
            LangItem::FormatArgument => vec!["format_argument".to_string()],
            LangItem::FormatArguments => vec!["format_arguments".to_string()],
            LangItem::Option => vec![
                "core".to_string(),
                "option".to_string(),
                "Option".to_string(),
            ],
            LangItem::OptionSome => {
                vec![
                    "core".to_string(),
                    "option".to_string(),
                    "Option".to_string(),
                    "Some".to_string(),
                ]
            }
            LangItem::OptionNone => {
                vec![
                    "core".to_string(),
                    "option".to_string(),
                    "Option".to_string(),
                    "None".to_string(),
                ]
            }
            LangItem::Range => {
                vec!["std".to_string(), "ops".to_string(), "Range".to_string()]
            }
            // all the unimplemented variants
            // TODO: provide implementation for all the variants
            _ => vec![
                "LanguageItem".to_string(),
                to_valid_coq_name(lang_item.name().to_string()),
            ],
        },
    }
}

pub(crate) fn compile_qpath(env: &Env, qpath: &QPath) -> Path {
    match qpath {
        QPath::Resolved(_, path) => compile_path(env, path),
        QPath::TypeRelative(ty, segment) => {
            let ty = match ty.kind {
                rustc_hir::TyKind::Path(QPath::Resolved(_, path)) => match path.res {
                    // SelfTyAlias and SelfTyParam are only local aliases (named `Self`)
                    // and cannot be used directly in qualified paths in Coq
                    Res::SelfTyAlias { .. } | Res::SelfTyParam { .. } => None,
                    Res::Def(DefKind::TyParam, _) => Some((compile_path(env, path), true)),
                    // the rest of paths should refer to implementations of types,
                    // so we prepend their names with `Impl_`
                    _ => {
                        let mut path = compile_path(env, path);
                        path.prefix_last_by_impl();
                        Some((path, false))
                    }
                },
                _ => Some((Path::local("ComplexTypePath".to_string()), false)),
            };
            match ty {
                Some((path, is_param)) => {
                    if is_param {
                        Path {
                            segments: vec![format!(
                                "{}::type[\"{}\"]",
                                to_valid_coq_name(path.to_string()),
                                to_valid_coq_name(segment.ident.name.to_string()),
                            )],
                        }
                    } else {
                        Path {
                            segments: vec![
                                to_valid_coq_name(path.to_string()),
                                to_valid_coq_name(segment.ident.name.to_string()),
                            ],
                        }
                    }
                }
                None => Path {
                    segments: vec![to_valid_coq_name(segment.ident.name.to_string())],
                },
            }
        }
        QPath::LangItem(lang_item, _, _) => compile_lang_item(lang_item),
    }
}

#[allow(dead_code)]
/// returns generics for the given path
pub(crate) fn get_path_generics<'a>(
    env: &Env<'a>,
    path: &rustc_hir::Path,
) -> Option<&'a rustc_middle::ty::Generics> {
    path.res
        .opt_def_id()
        .map(|def_id| env.tcx.generics_of(def_id))
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) enum StructOrVariant {
    Struct,
    Variant,
}

impl StructOrVariant {
    /// Returns wether a qpath refers to a struct or a variant.
    pub(crate) fn of_qpath(env: &Env, qpath: &QPath) -> StructOrVariant {
        let emit_warn_unsupported = || {
            env.tcx
                .sess
                .struct_span_warn(
                    qpath.span(),
                    "Cannot determine if this is a `struct` or an `enum`.",
                )
                .note("It should be supported in future versions.")
                .emit();
        };
        match qpath {
            QPath::Resolved(_, path) => match path.res {
                Res::Def(DefKind::Struct | DefKind::Ctor(CtorOf::Struct, _), _) => {
                    StructOrVariant::Struct
                }
                Res::Def(DefKind::Variant | DefKind::Ctor(CtorOf::Variant, _), _) => {
                    StructOrVariant::Variant
                }
                Res::SelfTyAlias { .. } => StructOrVariant::Struct,
                _ => {
                    emit_warn_unsupported();
                    StructOrVariant::Variant
                }
            },
            QPath::TypeRelative(..) => {
                emit_warn_unsupported();
                StructOrVariant::Struct
            }
            QPath::LangItem(lang_item, ..) => match lang_item {
                LangItem::OptionNone => StructOrVariant::Variant,
                LangItem::OptionSome => StructOrVariant::Variant,
                LangItem::ResultOk => StructOrVariant::Variant,
                LangItem::ResultErr => StructOrVariant::Variant,
                LangItem::ControlFlowContinue => StructOrVariant::Variant,
                LangItem::ControlFlowBreak => StructOrVariant::Variant,
                LangItem::RangeFrom => StructOrVariant::Variant,
                LangItem::RangeFull => StructOrVariant::Variant,
                LangItem::RangeInclusiveStruct => StructOrVariant::Variant,
                LangItem::RangeInclusiveNew => StructOrVariant::Variant,
                LangItem::Range => StructOrVariant::Struct,
                LangItem::RangeToInclusive => StructOrVariant::Variant,
                LangItem::RangeTo => StructOrVariant::Variant,
                _ => {
                    emit_warn_unsupported();
                    StructOrVariant::Struct
                }
            },
        }
    }
}

pub(crate) fn to_valid_coq_name(str: String) -> String {
    if str == "Type" {
        return "Type_".to_string();
    }
    if str == "Set" {
        return "Set_".to_string();
    }
    if str == "Unset" {
        return "Unset_".to_string();
    }
    let str = str::replace(&str, "$", "_");
    let str = str::replace(&str, "{{root}}", "CoqOfRust");
    str::replace(&str, "::", ".")
}
