use crate::env::*;
use crate::render::*;
use rustc_hir::def::{CtorOf, DefKind, Res};
use rustc_hir::{LangItem, QPath};
use std::fmt;
use std::vec;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Path {
    segments: Vec<String>,
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

    pub fn last(&self) -> &String {
        self.segments.last().unwrap()
    }

    pub fn base_before_last(&self) -> Path {
        Path {
            segments: self.segments[..self.segments.len() - 1].to_vec(),
        }
    }

    fn prefix_last_by_impl(&mut self) {
        let last = self.segments.pop().unwrap();
        self.segments.push(format!("Impl{last}"));
    }
}

fn compile_path_without_env(path: &rustc_hir::Path) -> Path {
    //eprintln!("++> {:?}\n", path); // TODO: remove
    Path {
        segments: path
            .segments
            .iter()
            .map(|segment| to_valid_coq_name(segment.ident.name.to_string()))
            .collect(),
    }
}

pub(crate) fn compile_path(env: &Env, path: &rustc_hir::Path) -> Path {
    //eprintln!("{:?}\n", path); // TODO: remove

    /*match path.res {
        Res::Def(def_kind, def_id) => {
            match def_kind {
                DefKind::TyParam => compile_path_without_env(path),
                _ => {
                    let crate_name: String = env.tcx.crate_name(def_id.krate).to_string();
                    let path_items = env.tcx.def_path(def_id);
                    let mut segments = vec![crate_name];
                    //eprintln!("##> {:?}\n", segments); // TODO: remove
                    segments.extend(
                        path_items
                            .data
                            .iter()
                            .filter_map(|item| item.data.get_opt_name())
                            .map(|name| to_valid_coq_name(name.to_string())),
                    );
                    Path { segments }
                }
            }
        }
        Res::SelfTyAlias { .. } => Path {
            segments: vec!["It_is_here!".to_string()],
        },
        _ => compile_path_without_env(path),
    }*/

    if let Some(def_if) = path.res.opt_def_id() {
        // The type parameters should not have an absolute name, as they are not
        // not declared at top-level.
        if let Res::Def(DefKind::TyParam, _) = path.res {
            return compile_path_without_env(path);
        }
        let crate_name: String = env.tcx.crate_name(def_if.krate).to_string();
        let path_items = env.tcx.def_path(def_if);
        let mut segments = vec![crate_name];
        //eprintln!("##> {:?}\n", segments); // TODO: remove
        segments.extend(
            path_items
                .data
                .iter()
                .filter_map(|item| item.data.get_opt_name())
                .map(|name| to_valid_coq_name(name.to_string())),
        );
        return Path { segments };
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
            //eprintln!("-> {:?}\n", segment); // TODO: remove
            let ty = match ty.kind {
                rustc_hir::TyKind::Path(QPath::Resolved(_, path)) => match path.res {
                    Res::SelfTyAlias { .. } => Path { segments: vec![] },
                    _ => {
                        let mut path = compile_path(env, path);
                        path.prefix_last_by_impl();
                        path
                    }
                },
                _ => Path::local("ComplexTypePath".to_string()),
            };
            Path {
                segments: vec![ty.to_string(), segment.ident.name.to_string()]
                    .iter()
                    .map(|segment| to_valid_coq_name(segment.to_string()))
                    .collect(),
            }
        }
        QPath::LangItem(lang_item, _, _) => compile_lang_item(lang_item),
    }
}

#[derive(Clone, Debug)]
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
    let str = str::replace(&str, "$", "_");
    let str = str::replace(&str, "{{root}}", "Root");
    str::replace(&str, "::", ".")
}

impl Path {
    pub(crate) fn to_doc<'a>(&self) -> Doc<'a> {
        // clone to be able to consume
        let segments = self.segments.clone();
        // consume (by into_iter) to let the result live arbitrarily long
        intersperse(segments.into_iter().map(text), [text(".")])
    }

    pub(crate) fn to_name(&self) -> String {
        self.segments.join("_")
    }
}
