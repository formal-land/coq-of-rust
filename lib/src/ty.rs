use crate::coq;
use crate::env::*;
use crate::expression::*;
use crate::path::*;
use serde::Serialize;
use std::rc::Rc;

#[derive(Debug, Eq, PartialEq, Serialize)]
pub(crate) enum CoqType {
    Var {
        name: String,
    },
    Path {
        path: Rc<Path>,
    },
    Application {
        func: Rc<CoqType>,
        consts: Vec<Rc<Expr>>,
        tys: Vec<Rc<CoqType>>,
    },
    Function {
        /// We group together the arguments that are called together, as this
        /// will be useful for the monadic translation of types later.
        args: Vec<Rc<CoqType>>,
        ret: Rc<CoqType>,
    },
    Tuple {
        tys: Vec<Rc<CoqType>>,
    },
    // TODO: add the type parameters for the traits
    Dyn {
        traits: Vec<Rc<Path>>,
    },
    AssociatedInTrait {
        trait_name: Rc<Path>,
        const_args: Vec<Rc<Expr>>,
        ty_args: Vec<Rc<CoqType>>,
        self_ty: Rc<CoqType>,
        name: String,
    },
    AssociatedUnknown,
    Infer,
}

impl CoqType {
    pub(crate) fn var(name: &str) -> Rc<CoqType> {
        Rc::new(CoqType::Var {
            name: name.to_string(),
        })
    }

    pub(crate) fn path(segments: &[&str]) -> Rc<CoqType> {
        Rc::new(CoqType::Path {
            path: Path::new(segments),
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
            consts: vec![],
            tys: vec![ty],
        })
    }

    pub(crate) fn match_ref(self: Rc<CoqType>) -> Option<(String, Rc<CoqType>)> {
        if let CoqType::Application { func, consts, tys } = &*self {
            if let CoqType::Path { path, .. } = &**func {
                let Path { segments } = path.as_ref();
                if segments.len() == 1 && consts.is_empty() && tys.len() == 1 {
                    let name = segments.first().unwrap();
                    if name == "&" || name == "&mut" {
                        return Some((name.clone(), tys.first().unwrap().clone()));
                    }
                }
            }
        }

        None
    }
}

pub(crate) fn compile_type<'a>(
    env: &Env<'a>,
    local_def_id: &rustc_hir::def_id::LocalDefId,
    ty: &rustc_hir::Ty<'a>,
) -> Rc<CoqType> {
    let generics = env.tcx.generics_of(*local_def_id);
    let item_ctxt = rustc_hir_analysis::collect::ItemCtxt::new(env.tcx, *local_def_id);
    let span = &ty.span;
    let ty = &item_ctxt.lower_ty(ty);

    crate::thir_ty::compile_type(env, span, generics, ty)
}

pub(crate) fn compile_fn_ret_ty<'a>(
    env: &Env<'a>,
    local_def_id: &rustc_hir::def_id::LocalDefId,
    fn_ret_ty: &rustc_hir::FnRetTy<'a>,
) -> Rc<CoqType> {
    match fn_ret_ty {
        rustc_hir::FnRetTy::DefaultReturn(_) => CoqType::unit(),
        rustc_hir::FnRetTy::Return(ty) => compile_type(env, local_def_id, ty),
    }
}

// The type of a function declaration
pub(crate) fn compile_fn_decl<'a>(
    env: &Env<'a>,
    local_def_id: &rustc_hir::def_id::LocalDefId,
    fn_decl: &rustc_hir::FnDecl<'a>,
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
pub(crate) fn compile_path_ty_params<'a>(
    env: &Env<'a>,
    local_def_id: &rustc_hir::def_id::LocalDefId,
    path: &rustc_hir::Path<'a>,
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
    pub(crate) fn to_coq(&self) -> Rc<coq::Expression> {
        match self {
            CoqType::Var { name } => coq::Expression::just_name(name),
            CoqType::Path { path } => coq::Expression::just_name("Ty.path")
                .apply(Rc::new(coq::Expression::String(path.to_string()))),
            CoqType::Application { func, consts, tys } => {
                if consts.is_empty() && tys.is_empty() {
                    func.to_coq()
                } else {
                    coq::Expression::just_name("Ty.apply").apply_many(&[
                        func.to_coq(),
                        Rc::new(coq::Expression::List {
                            exprs: consts.iter().map(|const_| const_.to_coq()).collect(),
                        }),
                        Rc::new(coq::Expression::List {
                            exprs: tys.iter().map(|ty| ty.to_coq()).collect(),
                        }),
                    ])
                }
            }
            CoqType::Function { args, ret } => coq::Expression::just_name("Ty.function")
                .apply_many(&[
                    Rc::new(coq::Expression::List {
                        exprs: args.iter().map(|arg| arg.to_coq()).collect(),
                    }),
                    ret.to_coq(),
                ]),
            CoqType::Tuple { tys } => {
                coq::Expression::just_name("Ty.tuple").apply(Rc::new(coq::Expression::List {
                    exprs: tys.iter().map(|ty| ty.to_coq()).collect(),
                }))
            }
            CoqType::Dyn { traits } => {
                coq::Expression::just_name("Ty.dyn").apply(Rc::new(coq::Expression::List {
                    exprs: traits
                        .iter()
                        .map(|trait_name| {
                            Rc::new(coq::Expression::Tuple(vec![
                                Rc::new(coq::Expression::String(trait_name.to_string())),
                                Rc::new(coq::Expression::List { exprs: vec![] }),
                            ]))
                        })
                        .collect(),
                }))
            }
            CoqType::AssociatedInTrait {
                trait_name,
                const_args,
                ty_args,
                self_ty,
                name,
            } => coq::Expression::just_name("Ty.associated_in_trait").apply_many(&[
                Rc::new(coq::Expression::String(trait_name.to_string())),
                Rc::new(coq::Expression::List {
                    exprs: const_args.iter().map(|const_| const_.to_coq()).collect(),
                }),
                Rc::new(coq::Expression::List {
                    exprs: ty_args.iter().map(|ty| ty.to_coq()).collect(),
                }),
                self_ty.to_coq(),
                Rc::new(coq::Expression::String(name.clone())),
            ]),
            CoqType::AssociatedUnknown => coq::Expression::just_name("Ty.associated_unknown"),
            CoqType::Infer => Rc::new(coq::Expression::Wild),
        }
    }

    /// We use this function to get a name for a type for the `impl` sections. This function should
    /// be injective, so that there is no confusion on the `Self` type that might be merged when we
    /// merge multiple modules with the same name.
    pub(crate) fn to_name(&self) -> String {
        match self {
            CoqType::Var { name } => name.clone(),
            CoqType::Path { path, .. } => {
                path.to_name().replace('&', "ref_").replace('*', "pointer_")
            }
            CoqType::Application { func, consts, tys } => {
                let mut name = func.to_name();
                for const_ in consts {
                    name.push('_');
                    name.push_str(&const_.to_name());
                }
                for ty in tys {
                    name.push('_');
                    name.push_str(&ty.to_name());
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
            CoqType::Tuple { tys } => {
                let mut name = "Tuple_".to_string();
                for ty in tys {
                    name.push_str(&ty.to_name());
                    name.push('_')
                }
                name
            }
            CoqType::Dyn { traits } => {
                let mut name = "Dyn".to_string();
                for trait_ in traits {
                    name.push('_');
                    name.push_str(&trait_.to_name());
                }
                name
            }
            CoqType::AssociatedInTrait {
                trait_name,
                const_args,
                ty_args,
                self_ty,
                name,
            } => {
                format!(
                    "associated_in_trait_{}_{}_{}_{}_{}",
                    trait_name.to_name(),
                    const_args
                        .iter()
                        .map(|const_| const_.to_name())
                        .collect::<Vec<_>>()
                        .join("_"),
                    ty_args
                        .iter()
                        .map(|ty| ty.to_name())
                        .collect::<Vec<_>>()
                        .join("_"),
                    self_ty.to_name(),
                    name
                )
            }
            CoqType::AssociatedUnknown => "associated_unknown_type".to_string(),
            CoqType::Infer => "inferred_type".to_string(),
        }
    }
}
