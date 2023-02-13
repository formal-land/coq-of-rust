extern crate rustc_hir;

use pretty::RcDoc;
use std::fmt;

#[derive(Debug)]
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
            segments: vec![name],
        }
    }
}

pub fn compile_path(path: &rustc_hir::Path) -> Path {
    Path {
        segments: path
            .segments
            .iter()
            .map(|segment| segment.ident.name.to_string())
            .collect(),
    }
}

pub fn compile_qpath(qpath: &rustc_hir::QPath) -> Path {
    match qpath {
        rustc_hir::QPath::Resolved(_, path) => compile_path(path),
        rustc_hir::QPath::TypeRelative(_, segment) => Path {
            segments: vec![segment.ident.name.to_string()],
        },
        rustc_hir::QPath::LangItem(lang_item, _, _) => Path {
            segments: vec![lang_item.name().to_string()],
        },
    }
}

impl Path {
    pub fn to_doc(&self) -> RcDoc<()> {
        RcDoc::intersperse(self.segments.iter().map(RcDoc::text), RcDoc::text("."))
    }
}
