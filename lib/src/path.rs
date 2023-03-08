use crate::render::*;
use rustc_hir::QPath;
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

pub fn compile_path<Res>(path: &rustc_hir::Path<Res>) -> Path {
    Path {
        segments: path
            .segments
            .iter()
            .map(|segment| to_valid_coq_name(segment.ident.name.to_string()))
            .collect(),
    }
}

pub fn compile_qpath(qpath: &QPath) -> Path {
    match qpath {
        QPath::Resolved(_, path) => compile_path(path),
        QPath::TypeRelative(ty, segment) => {
            let ty = match ty.kind {
                rustc_hir::TyKind::Path(QPath::Resolved(_, path)) => {
                    let mut path = compile_path(path);
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
