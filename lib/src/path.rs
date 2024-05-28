use crate::env::*;
use crate::render::*;
use rustc_hir::{
    def::{DefKind, Res},
    definitions::DefPathData,
    hir_id::HirId,
    QPath,
};
use std::fmt;
use std::rc::Rc;
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
    pub(crate) fn new<S: ToString>(segments: &[S]) -> Rc<Self> {
        Rc::new(Path {
            segments: segments.iter().map(|s| s.to_string()).collect(),
        })
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

    pub(crate) fn concat(paths: &[Rc<Self>]) -> Rc<Self> {
        Rc::new(Path {
            segments: paths
                .iter()
                .flat_map(|path| path.segments.to_owned())
                .collect(),
        })
    }
}

fn compile_path_without_env(path: &rustc_hir::Path) -> Rc<Path> {
    Rc::new(Path {
        segments: path
            .segments
            .iter()
            .map(|segment| segment.ident.name.to_string())
            .collect(),
    })
}

pub(crate) fn compile_def_id(env: &Env, def_id: rustc_hir::def_id::DefId) -> Rc<Path> {
    let crate_name: String = env.tcx.crate_name(def_id.krate).to_string();
    let path_items = env.tcx.def_path(def_id);
    let mut segments = vec![crate_name];

    segments.extend(path_items.data.iter().filter_map(|item| {
        let name = match item.data.get_opt_name() {
            Some(name) => name.to_string(),
            None => match &item.data {
                DefPathData::AnonConst
                | DefPathData::Ctor
                | DefPathData::ForeignMod
                | DefPathData::Impl => return None,
                _ => item.data.to_string(),
            },
        };

        Some(if item.disambiguator == 0 {
            name
        } else {
            format!("{name}'{}", item.disambiguator)
        })
    }));

    if path_items.data.last().unwrap().data == DefPathData::AnonConst {
        let last_segment = segments.pop().unwrap();
        segments.push(format!("{}{}", last_segment, "_discriminant"));
    }

    Rc::new(Path { segments })
}

pub(crate) fn compile_path(env: &Env, path: &rustc_hir::Path) -> Rc<Path> {
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

pub(crate) fn compile_qpath(env: &Env, hir_id: HirId, qpath: &QPath) -> Rc<Path> {
    let type_check_results = rustc_middle::ty::TypeckResults::new(hir_id.owner);

    compile_def_id(
        env,
        type_check_results
            .qpath_res(qpath, hir_id)
            .opt_def_id()
            .unwrap(),
    )
}

#[derive(Eq, PartialEq)]
pub(crate) enum IsValue {
    Yes,
    No,
}

pub(crate) fn to_valid_coq_name(is_value: IsValue, str: &str) -> String {
    if str == "_" {
        return "underscore".to_string();
    }

    let str = str.replace("r#", "");

    let reserved_names = [
        "M", "Set", "Type", "Unset", "at", "by", "else", "end", "exists", "fix", "if", "pair",
        "then", "tt", "unit", "with",
    ];

    if reserved_names.contains(&str.as_str()) {
        return format!("{}_", str);
    }

    let str = str.replace("->", "arrow");
    let str = str.replace("::", "_");
    let str = str.replace('+', "_plus_");
    let characters_to_replace = [
        ' ', '$', '(', ')', '&', '?', ',', '<', '>', '=', '[', ']', '*',
    ];
    let str = characters_to_replace
        .iter()
        .fold(str.to_string(), |acc, &char| acc.replace(char, "_"));

    if is_value == IsValue::Yes && str.chars().next().unwrap().is_uppercase() {
        format!("value_{}", str)
    } else {
        str
    }
}
