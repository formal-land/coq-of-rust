use crate::path::*;
use crate::render::*;
use rustc_hir::{FnDecl, FnRetTy, Ty, TyKind};
use rustc_middle::ty::TyCtxt;

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum CoqType {
    Var(Path),
    Application {
        func: Box<CoqType>,
        args: Vec<CoqType>,
    },
    Function {
        arg: Box<CoqType>,
        ret: Box<CoqType>,
    },
    Tuple(Vec<CoqType>),
    Array(Box<CoqType>),
    Ref(Box<CoqType>, rustc_hir::Mutability),
}

impl CoqType {
    pub fn unit() -> CoqType {
        CoqType::Var(Path::local("unit".to_string()))
    }
}

pub fn compile_type(_tcx: &TyCtxt, ty: &Ty) -> CoqType {
    match &ty.kind {
        TyKind::Slice(_) => CoqType::Var(Path::local("Slice".to_string())),
        TyKind::Array(ty, _) => CoqType::Array(Box::new(compile_type(_tcx, ty))),
        TyKind::Ptr(mut_ty) => CoqType::Ref(Box::new(compile_type(_tcx, mut_ty.ty)), mut_ty.mutbl),
        TyKind::Ref(_, mut_ty) => {
            CoqType::Ref(Box::new(compile_type(_tcx, mut_ty.ty)), mut_ty.mutbl)
        }
        TyKind::BareFn(_) => CoqType::Var(Path::local("BareFn".to_string())),
        TyKind::Never => CoqType::Var(Path::local("Empty_set".to_string())),
        TyKind::Tup(tys) => CoqType::Tuple(tys.iter().map(|ty| compile_type(_tcx, ty)).collect()),
        TyKind::Path(qpath) => {
            let path = compile_qpath(qpath);
            CoqType::Var(path)
        }
        TyKind::OpaqueDef(_, _, _) => CoqType::Var(Path::local("OpaqueDef".to_string())),
        TyKind::TraitObject(_, _, _) => CoqType::Var(Path::local("TraitObject".to_string())),
        TyKind::Typeof(_) => CoqType::Var(Path::local("Typeof".to_string())),
        TyKind::Infer => CoqType::Var(Path::local("_".to_string())),
        TyKind::Err => CoqType::Var(Path::local("Error_type".to_string())),
    }
}

pub fn compile_fn_ret_ty(tcx: &TyCtxt, fn_ret_ty: &FnRetTy) -> Option<CoqType> {
    match fn_ret_ty {
        FnRetTy::DefaultReturn(_) => None,
        FnRetTy::Return(ty) => Some(compile_type(tcx, ty)),
    }
}

// The type of a function declaration
pub fn compile_fn_decl(tcx: &TyCtxt, fn_decl: &FnDecl) -> CoqType {
    let ret_ty = match compile_fn_ret_ty(tcx, &fn_decl.output) {
        Some(ret_ty) => ret_ty,
        None => CoqType::Var(Path::local("_".to_string())),
    };
    fn_decl
        .inputs
        .iter()
        .rfold(ret_ty, |acc, arg| CoqType::Function {
            arg: Box::new(compile_type(tcx, arg)),
            ret: Box::new(acc),
        })
}

// Returns the type parameters on a path
pub fn compile_path_ty_params(tcx: &TyCtxt, path: &rustc_hir::Path) -> Vec<CoqType> {
    match path.segments.last().unwrap().args {
        Some(args) => args
            .args
            .iter()
            .filter_map(|arg| match arg {
                rustc_hir::GenericArg::Type(ty) => Some(compile_type(tcx, ty)),
                _ => None,
            })
            .collect(),
        None => vec![],
    }
}

impl CoqType {
    pub fn to_doc(&self, with_paren: bool) -> Doc {
        match self {
            CoqType::Var(path) => path.to_doc(),
            CoqType::Application { func, args } => paren(
                with_paren,
                nest([
                    func.to_doc(true),
                    line(),
                    intersperse(args.iter().map(|arg| arg.to_doc(true)), [line()]),
                ]),
            ),
            CoqType::Function { arg, ret } => paren(
                with_paren,
                nest([
                    arg.to_doc(true),
                    line(),
                    text("->"),
                    line(),
                    ret.to_doc(true),
                ]),
            ),
            CoqType::Tuple(tys) => paren(
                with_paren,
                nest([intersperse(
                    tys.iter().map(|ty| ty.to_doc(true)),
                    [text(" *"), line()],
                )]),
            ),
            CoqType::Array(ty) => nest([text("list"), line(), ty.to_doc(true)]),
            CoqType::Ref(ty, mutbl) => paren(
                with_paren,
                match mutbl {
                    rustc_hir::Mutability::Mut => nest([text("mut_ref"), line(), ty.to_doc(true)]),
                    rustc_hir::Mutability::Not => nest([text("ref"), line(), ty.to_doc(true)]),
                },
            ),
        }
    }

    // We use this function when we need a quick and recognizable name for a type
    pub(crate) fn to_name(&self) -> String {
        match self {
            CoqType::Var(path) => path.to_name(),
            CoqType::Application { func, args } => {
                let mut name = func.to_name();
                for arg in args {
                    name.push('_');
                    name.push_str(&arg.to_name());
                }
                name
            }
            CoqType::Function { arg, ret } => {
                let mut name = arg.to_name();
                name.push_str("To");
                name.push_str(&ret.to_name());
                name
            }
            CoqType::Tuple(tys) => {
                let mut name = "Tuple_".to_string();
                for ty in tys {
                    name.push_str(&ty.to_name());
                    name.push('_')
                }
                name
            }
            CoqType::Array(ty) => {
                let mut name = "Array_".to_string();
                name.push_str(&ty.to_name());
                name
            }
            CoqType::Ref(ty, mutbl) => {
                let mut name = match mutbl {
                    rustc_hir::Mutability::Mut => "MutRef_".to_string(),
                    rustc_hir::Mutability::Not => "StaticRef_".to_string(),
                };
                name.push_str(&ty.to_name());
                name
            }
        }
    }

    // The path of a type: we remove all the type parameters to know on
    // which type an implementation is working
    pub(crate) fn to_path_doc(&self) -> Doc {
        match self {
            CoqType::Var(path) => path.to_doc(),
            CoqType::Application { func, args: _ } => func.to_path_doc(),
            CoqType::Function { .. } => text("Function"),
            CoqType::Tuple(_) => text("Tuple"),
            CoqType::Array(_) => text("Array"),
            CoqType::Ref(_, _) => text("Ref"),
        }
    }
}
