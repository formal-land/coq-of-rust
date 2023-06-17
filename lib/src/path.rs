use crate::env::*;
use crate::render::*;
use rustc_hir::def::{CtorOf, DefKind, Res};
use rustc_hir::{LangItem, QPath};
use rustc_middle::ty::TyCtxt;
use std::fmt;

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

fn compile_path_without_env<Res>(path: &rustc_hir::Path<Res>) -> Path {
    Path {
        segments: path
            .segments
            .iter()
            .map(|segment| to_valid_coq_name(segment.ident.name.to_string()))
            .collect(),
    }
}

pub(crate) fn compile_path<Res>(env: &Env, path: &rustc_hir::Path<Res>) -> Path {
    if let [segment] = path.segments {
        if let Some(path) = env.use_types.get(&segment.ident.name.to_string()) {
            return path.clone();
        }
    }
    compile_path_without_env(path)
}

pub(crate) fn compile_qpath(env: &Env, qpath: &QPath) -> Path {
    match qpath {
        QPath::Resolved(_, path) => compile_path(env, path),
        QPath::TypeRelative(ty, segment) => {
            let ty = match ty.kind {
                rustc_hir::TyKind::Path(QPath::Resolved(_, path)) => {
                    let mut path = compile_path(env, path);
                    path.prefix_last_by_impl();
                    path
                }
                _ => Path::local("ComplexTypePath".to_string()),
            };
            Path {
                segments: vec![ty.to_string(), segment.ident.name.to_string()]
                    .iter()
                    .map(|segment| to_valid_coq_name(segment.to_string()))
                    .collect(),
            }
        }
        QPath::LangItem(lang_item, _, _) => Path {
            segments: vec![to_valid_coq_name(lang_item.name().to_string())],
        },
    }
}

#[derive(Clone, Debug)]
pub enum StructOrVariant {
    Struct,
    Variant,
}

impl StructOrVariant {
    /// Returns wether a qpath refers to a struct or a variant.
    pub(crate) fn of_qpath(tcx: &TyCtxt, qpath: &QPath) -> StructOrVariant {
        let emit_warn_unsupported = || {
            tcx.sess
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
                LangItem::Range => StructOrVariant::Variant,
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

pub fn to_valid_coq_name(str: String) -> String {
    let str = str::replace(&str, "$", "_");
    let str = str::replace(&str, "{{root}}", "Root");
    str::replace(&str, "::", ".")
}

impl Path {
    pub fn to_doc(&self) -> Doc {
        intersperse(self.segments.iter().map(text), [text(".")])
    }

    pub fn to_name(&self) -> String {
        self.segments.join("_")
    }
}
