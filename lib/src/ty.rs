use crate::path::*;
use crate::render::*;
use rustc_hir::{BareFnTy, FnDecl, FnRetTy, Ty, TyKind};
use rustc_middle::ty::TyCtxt;

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum CoqType {
    Var(Box<Path>),
    Application {
        func: Box<Path>,
        args: Vec<Box<CoqType>>,
    },
    Function {
        /// We group together the arguments that are called together, as this
        /// will be useful for the monadic translation of types later.
        args: Vec<Box<CoqType>>,
        ret: Box<CoqType>,
    },
    Tuple(Vec<Box<CoqType>>),
    Array(Box<CoqType>),
    Ref(Box<CoqType>, rustc_hir::Mutability),
}

impl CoqType {
    pub(crate) fn var(name: String) -> Box<CoqType> {
        Box::new(CoqType::Var(Box::new(Path::local(name))))
    }

    pub(crate) fn unit() -> Box<CoqType> {
        CoqType::var("unit".to_string())
    }

    pub(crate) fn monad(ty: Box<CoqType>) -> Box<CoqType> {
        Box::new(CoqType::Application {
            func: Box::new(Path::local("M".to_string())),
            args: vec![ty],
        })
    }
}

pub(crate) fn mt_ty(ty: Box<CoqType>) -> Box<CoqType> {
    match *ty {
        CoqType::Application { func, args } => Box::new(CoqType::Application {
            func,
            args: args.into_iter().map(mt_ty).collect(),
        }),
        CoqType::Var(..) => ty,
        CoqType::Function { args, ret } => Box::new(CoqType::Function {
            args: args.into_iter().map(mt_ty).collect(),
            ret: CoqType::monad(mt_ty(ret)),
        }),
        CoqType::Tuple(tys) => Box::new(CoqType::Tuple(tys.into_iter().map(mt_ty).collect())),
        CoqType::Array(ty) => Box::new(CoqType::Array(mt_ty(ty))),
        CoqType::Ref(ty, mutability) => Box::new(CoqType::Ref(mt_ty(ty), mutability)),
    }
}

pub fn compile_type(_tcx: &TyCtxt, ty: &Ty) -> Box<CoqType> {
    match &ty.kind {
        TyKind::Slice(_) => CoqType::var("Slice".to_string()),
        TyKind::Array(ty, _) => Box::new(CoqType::Array(compile_type(_tcx, ty))),
        TyKind::Ptr(mut_ty) => Box::new(CoqType::Ref(compile_type(_tcx, mut_ty.ty), mut_ty.mutbl)),
        TyKind::Ref(_, mut_ty) => {
            Box::new(CoqType::Ref(compile_type(_tcx, mut_ty.ty), mut_ty.mutbl))
        }
        TyKind::BareFn(BareFnTy { decl, .. }) => compile_fn_decl(_tcx, decl),
        TyKind::Never => CoqType::var("Empty_set".to_string()),
        TyKind::Tup(tys) => Box::new(CoqType::Tuple(
            tys.iter().map(|ty| compile_type(_tcx, ty)).collect(),
        )),
        TyKind::Path(qpath) => {
            let params = match qpath {
                rustc_hir::QPath::Resolved(_, path) => compile_path_ty_params(_tcx, path),
                _ => vec![],
            };
            let qpath = Box::new(compile_qpath(qpath));
            if params.is_empty() {
                Box::new(CoqType::Var(qpath))
            } else {
                Box::new(CoqType::Application {
                    func: qpath,
                    args: params,
                })
            }
        }
        TyKind::OpaqueDef(_, _, _) => CoqType::var("OpaqueDef".to_string()),
        TyKind::TraitObject(_, _, _) => CoqType::var("TraitObject".to_string()),
        TyKind::Typeof(_) => CoqType::var("Typeof".to_string()),
        TyKind::Infer => CoqType::var("_".to_string()),
        TyKind::Err(_) => CoqType::var("Error_type".to_string()),
    }
}

pub fn compile_fn_ret_ty(tcx: &TyCtxt, fn_ret_ty: &FnRetTy) -> Box<CoqType> {
    match fn_ret_ty {
        FnRetTy::DefaultReturn(_) => CoqType::unit(),
        FnRetTy::Return(ty) => compile_type(tcx, ty),
    }
}

// The type of a function declaration
pub fn compile_fn_decl(tcx: &TyCtxt, fn_decl: &FnDecl) -> Box<CoqType> {
    let ret = compile_fn_ret_ty(tcx, &fn_decl.output);
    Box::new(CoqType::Function {
        args: fn_decl
            .inputs
            .iter()
            .map(|arg| compile_type(tcx, arg))
            .collect(),
        ret,
    })
}

// Returns the type parameters on a path
pub fn compile_path_ty_params(tcx: &TyCtxt, path: &rustc_hir::Path) -> Vec<Box<CoqType>> {
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
                    func.to_doc(),
                    line(),
                    intersperse(args.iter().map(|arg| arg.to_doc(true)), [line()]),
                ]),
            ),
            CoqType::Function { args, ret } => paren(
                with_paren,
                group([
                    intersperse(
                        args.iter().map(|arg| arg.to_doc(true)),
                        [text(" ->"), line()],
                    ),
                    text(" ->"),
                    line(),
                    ret.to_doc(true),
                ]),
            ),
            CoqType::Tuple(tys) => {
                if tys.is_empty() {
                    text("unit")
                } else {
                    paren(
                        with_paren,
                        nest([intersperse(
                            tys.iter().map(|ty| ty.to_doc(true)),
                            [text(" *"), line()],
                        )]),
                    )
                }
            }
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
            CoqType::Function { args, ret } => {
                let mut name = "".to_string();
                for arg in args {
                    name.push_str(&arg.to_name());
                }
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
}
