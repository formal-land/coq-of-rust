use crate::env::*;
use crate::path::*;
use crate::render::*;
use rustc_hir::{BareFnTy, FnDecl, FnRetTy, Ty, TyKind};

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub(crate) enum CoqType {
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
            // TODO: try to remove the explicit parameter
            func: Box::new(Path::local("M (H := H)".to_string())),
            args: vec![ty],
        })
    }
}

pub(crate) fn mt_ty_unboxed(ty: CoqType) -> CoqType {
    match ty {
        CoqType::Application { func, args } => CoqType::Application {
            func,
            args: args.into_iter().map(mt_ty).collect(),
        },
        CoqType::Var(..) => ty,
        CoqType::Function { args, ret } => CoqType::Function {
            args: args.into_iter().map(mt_ty).collect(),
            ret: CoqType::monad(mt_ty(ret)),
        },
        CoqType::Tuple(tys) => CoqType::Tuple(tys.into_iter().map(mt_ty).collect()),
        CoqType::Array(ty) => CoqType::Array(mt_ty(ty)),
        CoqType::Ref(ty, mutability) => CoqType::Ref(mt_ty(ty), mutability),
    }
}

pub(crate) fn mt_ty(ty: Box<CoqType>) -> Box<CoqType> {
    Box::new(mt_ty_unboxed(*ty))
}

pub(crate) fn compile_type(env: &Env, ty: &Ty) -> Box<CoqType> {
    match &ty.kind {
        TyKind::Slice(ty) => {
            let func = Box::new(Path::local("Slice".to_string()));
            let args = vec![compile_type(env, ty)];
            Box::new(CoqType::Application { func, args })
        }
        TyKind::Array(ty, _) => Box::new(CoqType::Array(compile_type(env, ty))),
        TyKind::Ptr(mut_ty) => Box::new(CoqType::Ref(compile_type(env, mut_ty.ty), mut_ty.mutbl)),
        TyKind::Ref(_, mut_ty) => {
            Box::new(CoqType::Ref(compile_type(env, mut_ty.ty), mut_ty.mutbl))
        }
        TyKind::BareFn(BareFnTy { decl, .. }) => compile_fn_decl(env, decl),
        TyKind::Never => CoqType::var("Empty_set".to_string()),
        TyKind::Tup(tys) => Box::new(CoqType::Tuple(
            tys.iter().map(|ty| compile_type(env, ty)).collect(),
        )),
        TyKind::Path(qpath) => {
            let params = match qpath {
                rustc_hir::QPath::Resolved(_, path) => compile_path_ty_params(env, path),
                _ => vec![],
            };
            let qpath = Box::new(compile_qpath(env, qpath));
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

pub(crate) fn compile_fn_ret_ty(env: &Env, fn_ret_ty: &FnRetTy) -> Box<CoqType> {
    match fn_ret_ty {
        FnRetTy::DefaultReturn(_) => CoqType::unit(),
        FnRetTy::Return(ty) => compile_type(env, ty),
    }
}

// The type of a function declaration
pub(crate) fn compile_fn_decl(env: &Env, fn_decl: &FnDecl) -> Box<CoqType> {
    let ret = compile_fn_ret_ty(env, &fn_decl.output);
    Box::new(CoqType::Function {
        args: fn_decl
            .inputs
            .iter()
            .map(|arg| compile_type(env, arg))
            .collect(),
        ret,
    })
}

/// Return the type parameters on a path
pub(crate) fn compile_path_ty_params(env: &Env, path: &rustc_hir::Path) -> Vec<Box<CoqType>> {
    match path.segments.last().unwrap().args {
        Some(args) => args
            .args
            .iter()
            .filter_map(|arg| match arg {
                rustc_hir::GenericArg::Type(ty) => Some(compile_type(env, ty)),
                _ => None,
            })
            .collect(),
        None => vec![],
    }
}

impl CoqType {
    pub(crate) fn to_doc<'a>(&self, with_paren: bool) -> Doc<'a> {
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
                    concat(
                        args.iter()
                            .map(|arg| concat([arg.to_doc(true), text(" ->"), line()])),
                    ),
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
            CoqType::Array(ty) => paren(with_paren, nest([text("list"), line(), ty.to_doc(true)])),
            CoqType::Ref(ty, mutbl) => paren(
                with_paren,
                match mutbl {
                    rustc_hir::Mutability::Mut => nest([text("mut_ref"), line(), ty.to_doc(true)]),
                    rustc_hir::Mutability::Not => nest([text("ref"), line(), ty.to_doc(true)]),
                },
            ),
        }
    }

    // we need this function to fix aligning
    pub(crate) fn to_doc_tuning(&self, with_paren: bool) -> Doc {
        match self {
            CoqType::Ref(ty, _) => paren(with_paren, ty.to_doc(true)),
            _ => self.to_doc(with_paren),
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

    // To get cleared name out of path
    // @TODO extend to cover more cases
    pub(crate) fn to_item_name(&self) -> String {
        match self {
            CoqType::Var(path) => {
                let ret = path.last().clone();
                ret
            }
            _ => String::from("default_name"),
        }
    }
}
