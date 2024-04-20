use crate::coq;
use crate::env::*;
use crate::path::*;
use rustc_hir::{FnDecl, FnRetTy, Ty};
use std::rc::Rc;

#[derive(Debug, Eq, PartialEq)]
pub(crate) enum CoqType {
    Var(String),
    Path {
        path: Rc<Path>,
    },
    Application {
        func: Rc<CoqType>,
        args: Vec<Rc<CoqType>>,
    },
    Function {
        /// We group together the arguments that are called together, as this
        /// will be useful for the monadic translation of types later.
        args: Vec<Rc<CoqType>>,
        ret: Rc<CoqType>,
    },
    Tuple(Vec<Rc<CoqType>>),
    // TODO: add the type parameters for the traits
    Dyn(Vec<Path>),
    Associated,
    Infer,
}

impl CoqType {
    pub(crate) fn var(name: &str) -> Rc<CoqType> {
        Rc::new(CoqType::Var(name.to_string()))
    }

    pub(crate) fn path(segments: &[&str]) -> Rc<CoqType> {
        Rc::new(CoqType::Path {
            path: Rc::new(Path::new(segments)),
        })
    }

    pub(crate) fn unit() -> Rc<CoqType> {
        CoqType::path(&["unit"])
    }

    pub(crate) fn make_ref(mutbl: &rustc_hir::Mutability, ty: Rc<CoqType>) -> Rc<CoqType> {
        let ptr_name = match mutbl {
            rustc_hir::Mutability::Mut => "&mut",
            rustc_hir::Mutability::Not => "&",
        };

        Rc::new(CoqType::Application {
            func: CoqType::path(&[ptr_name]),
            args: vec![ty],
        })
    }

    pub(crate) fn match_ref(self: Rc<CoqType>) -> Option<(String, Rc<CoqType>)> {
        if let CoqType::Application { func, args } = &*self {
            if let CoqType::Path { path, .. } = &**func {
                let Path { segments } = path.as_ref();
                if segments.len() == 1 && args.len() == 1 {
                    let name = segments.first().unwrap();
                    if name == "&" || name == "&mut" {
                        return Some((name.clone(), args.first().unwrap().clone()));
                    }
                }
            }
        }

        None
    }
}

pub(crate) fn compile_type(
    env: &Env,
    local_def_id: &rustc_hir::def_id::LocalDefId,
    ty: &Ty,
) -> Rc<CoqType> {
    let generics = env.tcx.generics_of(*local_def_id);
    let item_ctxt = rustc_hir_analysis::collect::ItemCtxt::new(env.tcx, *local_def_id);
    let ty = &item_ctxt.to_ty(ty);

    crate::thir_ty::compile_type(env, generics, ty)
}

pub(crate) fn compile_fn_ret_ty(
    env: &Env,
    local_def_id: &rustc_hir::def_id::LocalDefId,
    fn_ret_ty: &FnRetTy,
) -> Rc<CoqType> {
    match fn_ret_ty {
        FnRetTy::DefaultReturn(_) => CoqType::unit(),
        FnRetTy::Return(ty) => compile_type(env, local_def_id, ty),
    }
}

// The type of a function declaration
pub(crate) fn compile_fn_decl(
    env: &Env,
    local_def_id: &rustc_hir::def_id::LocalDefId,
    fn_decl: &FnDecl,
) -> Rc<CoqType> {
    let ret = compile_fn_ret_ty(env, local_def_id, &fn_decl.output);

    Rc::new(CoqType::Function {
        args: fn_decl
            .inputs
            .iter()
            .map(|arg| compile_type(env, local_def_id, arg))
            .collect(),
        ret,
    })
}

/// Return the type parameters on a path
pub(crate) fn compile_path_ty_params(
    env: &Env,
    local_def_id: &rustc_hir::def_id::LocalDefId,
    path: &rustc_hir::Path,
) -> Vec<Rc<CoqType>> {
    match path.segments.last().unwrap().args {
        Some(args) => args
            .args
            .iter()
            .filter_map(|arg| match arg {
                rustc_hir::GenericArg::Type(ty) => Some(compile_type(env, local_def_id, ty)),
                _ => None,
            })
            .collect(),
        None => vec![],
    }
}

impl CoqType {
    pub(crate) fn to_coq(&self) -> coq::Expression {
        match self {
            CoqType::Var(name) => coq::Expression::just_name(name),
            CoqType::Path { path } => coq::Expression::just_name("Ty.path")
                .apply(&coq::Expression::String(path.to_string())),
            CoqType::Application { func, args } => {
                if args.is_empty() {
                    func.to_coq()
                } else {
                    coq::Expression::just_name("Ty.apply").apply_many(&[
                        func.to_coq(),
                        coq::Expression::List {
                            exprs: args.iter().map(|arg| arg.to_coq()).collect(),
                        },
                    ])
                }
            }
            CoqType::Function { args, ret } => coq::Expression::just_name("Ty.function")
                .apply_many(&[
                    coq::Expression::List {
                        exprs: args.iter().map(|arg| arg.to_coq()).collect(),
                    },
                    ret.to_coq(),
                ]),
            CoqType::Tuple(tys) => {
                coq::Expression::just_name("Ty.tuple").apply(&coq::Expression::List {
                    exprs: tys.iter().map(|ty| ty.to_coq()).collect(),
                })
            }
            CoqType::Dyn(traits) => {
                coq::Expression::just_name("Ty.dyn").apply(&coq::Expression::List {
                    exprs: traits
                        .iter()
                        .map(|trait_name| {
                            coq::Expression::Tuple(vec![
                                coq::Expression::String(trait_name.to_string()),
                                coq::Expression::List { exprs: vec![] },
                            ])
                        })
                        .collect(),
                })
            }
            CoqType::Associated => coq::Expression::just_name("Ty.associated"),
            CoqType::Infer => coq::Expression::Wild,
        }
    }

    /// We use this function to get a name for a type for the `impl` sections. This function should
    /// be injective, so that there is no confusion on the `Self` type that might be merged when we
    /// merge multiple modules with the same name.
    pub(crate) fn to_name(&self) -> String {
        match self {
            CoqType::Var(name) => name.clone(),
            CoqType::Path { path, .. } => {
                path.to_name().replace('&', "ref_").replace('*', "pointer_")
            }
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
            CoqType::Dyn(paths) => {
                let mut name = "Dyn".to_string();
                for path in paths {
                    name.push('_');
                    name.push_str(&path.to_name());
                }
                name
            }
            CoqType::Associated => "associated_type".to_string(),
            CoqType::Infer => "inferred_type".to_string(),
        }
    }
}
