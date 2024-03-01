use crate::coq;
use crate::env::*;
use crate::path::*;
use crate::render::*;
use crate::top_level::*;
use itertools::Itertools;
use rustc_hir::def::{DefKind, Res};
use rustc_hir::{BareFnTy, FnDecl, FnRetTy, GenericBound, ItemKind, OpaqueTyOrigin, Ty, TyKind};
use std::rc::Rc;

#[derive(Debug, PartialEq, Eq, Hash)]
pub(crate) enum CoqType {
    Var(String),
    Path {
        path: Rc<Path>,
    },
    PathInTrait {
        path: Rc<Path>,
        self_ty: Rc<CoqType>,
    },
    Application {
        func: Rc<CoqType>,
        args: Vec<Rc<CoqType>>,
        is_alias: bool,
    },
    Function {
        /// We group together the arguments that are called together, as this
        /// will be useful for the monadic translation of types later.
        args: Vec<Rc<CoqType>>,
        ret: Rc<CoqType>,
    },
    Tuple(Vec<Rc<CoqType>>),
    OpaqueType(Vec<Path>),
    Dyn(Vec<Path>),
    Infer,
    Monad(Rc<CoqType>),
    Val(Rc<CoqType>),
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
            rustc_hir::Mutability::Mut => "mut_ref",
            rustc_hir::Mutability::Not => "ref",
        };
        Rc::new(CoqType::Application {
            func: CoqType::path(&[ptr_name]),
            args: vec![ty],
            is_alias: false,
        })
    }

    pub(crate) fn match_ref(self: Rc<CoqType>) -> Option<(String, Rc<CoqType>, bool)> {
        if let CoqType::Application {
            func,
            args,
            is_alias,
        } = &*self
        {
            if let CoqType::Path { path, .. } = &**func {
                let Path { segments } = path.as_ref();
                if segments.len() == 1 && args.len() == 1 {
                    let name = segments.first().unwrap();
                    if name == "ref" || name == "mut_ref" {
                        return Some((name.clone(), args.first().unwrap().clone(), *is_alias));
                    }
                }
            }
        }

        None
    }

    pub(crate) fn val(self: Rc<CoqType>) -> Rc<CoqType> {
        Rc::new(CoqType::Val(self))
    }

    pub(crate) fn unval(self: Rc<CoqType>) -> Option<Rc<CoqType>> {
        match &*self {
            CoqType::Val(ty) => Some(ty.clone()),
            _ => None,
        }
    }
}

pub(crate) fn mt_ty(ty: Rc<CoqType>) -> Rc<CoqType> {
    match &*ty {
        CoqType::Application {
            func,
            args,
            is_alias,
        } => Rc::new(CoqType::Application {
            func: func.clone(),
            args: args.iter().map(|ty| mt_ty(ty.clone())).collect(),
            is_alias: *is_alias,
        }),
        CoqType::Var(..) | CoqType::Path { .. } => ty,
        CoqType::PathInTrait { path, self_ty } => Rc::new(CoqType::PathInTrait {
            path: path.clone(),
            self_ty: mt_ty(self_ty.clone()),
        }),
        CoqType::Function { args, ret } => Rc::new(CoqType::Function {
            args: args.iter().map(|ty| mt_ty(ty.clone())).collect(),
            ret: Rc::new(CoqType::Monad(mt_ty(ret.clone()))),
        }),
        CoqType::Tuple(tys) => Rc::new(CoqType::Tuple(
            tys.iter().map(|ty| mt_ty(ty.clone())).collect(),
        )),
        CoqType::OpaqueType(..) => ty,
        CoqType::Dyn(..) => ty,
        CoqType::Infer => ty,
        CoqType::Monad(_) => panic!("the monadic type should not appear here"),
        CoqType::Val(ty) => Rc::new(CoqType::Val(mt_ty(ty.clone()))),
    }
}

pub(crate) fn compile_type(env: &Env, ty: &Ty) -> Rc<CoqType> {
    match &ty.kind {
        TyKind::Slice(ty) => Rc::new(CoqType::Application {
            func: CoqType::path(&["slice"]),
            args: vec![compile_type(env, ty)],
            is_alias: false,
        }),
        TyKind::Array(ty, _) => Rc::new(CoqType::Application {
            func: CoqType::path(&["array"]),
            args: vec![compile_type(env, ty)],
            is_alias: false,
        }),
        TyKind::Ptr(mut_ty) | TyKind::Ref(_, mut_ty) => {
            let rustc_hir::MutTy { ty, mutbl } = mut_ty;
            CoqType::make_ref(mutbl, compile_type(env, ty))
        }
        TyKind::BareFn(BareFnTy { decl, .. }) => compile_fn_decl(env, decl),
        TyKind::Never => CoqType::path(&["never"]),
        TyKind::Tup(tys) => Rc::new(CoqType::Tuple(
            tys.iter().map(|ty| compile_type(env, ty)).collect(),
        )),
        TyKind::Path(qpath) => {
            // When the [qpath] is a `Self::A`
            if let rustc_hir::QPath::TypeRelative(ty, segment) = qpath {
                if let TyKind::Path(rustc_hir::QPath::Resolved(_, ty_path)) = &ty.kind {
                    if let Res::SelfTyAlias { .. } = ty_path.res {
                        return Rc::new(CoqType::Var(segment.ident.to_string()));
                    }
                }
            }

            let is_alias = match qpath {
                rustc_hir::QPath::Resolved(_, path) => {
                    matches!(path.res, Res::Def(DefKind::TyAlias, _))
                }
                _ => false,
            };
            let is_variable: Option<String> = match qpath {
                rustc_hir::QPath::Resolved(_, path) => {
                    if matches!(
                        path.res,
                        Res::SelfTyAlias { .. }
                            | Res::SelfTyParam { .. }
                            | Res::Def(DefKind::AssocTy | DefKind::TyParam, _)
                    ) {
                        // We assume that a variable is a path with a single element
                        Some(path.segments.last().unwrap().ident.to_string())
                    } else {
                        None
                    }
                }
                _ => None,
            };
            let self_ty = match qpath {
                rustc_hir::QPath::Resolved(Some(self_ty), _) => Some(compile_type(env, self_ty)),
                _ => None,
            };
            let coq_path = compile_qpath(env, qpath);
            let func = Rc::new(match self_ty {
                Some(self_ty) => CoqType::PathInTrait {
                    path: Rc::new(coq_path.clone()),
                    self_ty,
                },
                None => match is_variable {
                    Some(name) => CoqType::Var(name),
                    None => CoqType::Path {
                        path: Rc::new(coq_path.clone()),
                    },
                },
            });
            let params = match qpath {
                rustc_hir::QPath::Resolved(_, path) => {
                    if let Some(generics) = get_path_generics(env, path) {
                        let type_params_name_and_default_status =
                            get_type_params_name_and_default_status(generics);
                        let ty_params = compile_path_ty_params(env, path);
                        ty_params
                            .iter()
                            .map(Some)
                            .chain(std::iter::repeat(None))
                            .zip(type_params_name_and_default_status)
                            .map(|(ty, (name, has_default))| match ty {
                                Some(ty) => ty.clone(),
                                None => {
                                    if has_default {
                                        let mut segments = coq_path.segments.clone();
                                        segments.push("Default".to_string());
                                        segments.push(name);
                                        Rc::new(CoqType::Path {
                                            path: Rc::new(Path { segments }),
                                        })
                                    } else {
                                        Rc::new(CoqType::Infer)
                                    }
                                }
                            })
                            .collect()
                    } else {
                        vec![]
                    }
                }
                _ => vec![],
            };
            Rc::new(CoqType::Application {
                func,
                args: params,
                is_alias,
            })
        }
        TyKind::OpaqueDef(item_id, _, _) => {
            let item = env.tcx.hir().item(*item_id);
            if let ItemKind::OpaqueTy(opaque_ty) = item.kind {
                if opaque_ty.generics.params.is_empty() {
                    if opaque_ty.generics.predicates.is_empty() {
                        if let OpaqueTyOrigin::FnReturn(_) = opaque_ty.origin {
                            Rc::new(CoqType::OpaqueType(
                                opaque_ty
                                    .bounds
                                    .iter()
                                    .filter_map(|bound| match bound {
                                        GenericBound::Trait(p_trait_ref, _) => {
                                            Some(compile_path(env, p_trait_ref.trait_ref.path))
                                        }
                                        GenericBound::LangItemTrait{..} => {
                                            env.tcx
                                                .sess
                                                .struct_span_warn(
                                                    ty.span,
                                                    "LangItem traits are not supported in the bounds of opaque types.",
                                                )
                                                .note("It should change in the future.")
                                                .emit();
                                            None
                                        }
                                        // we ignore lifetimes
                                        GenericBound::Outlives(..) => None,
                                    })
                                    .collect(),
                            ))
                        } else {
                            env.tcx
                                .sess
                                .struct_span_warn(
                                    ty.span,
                                    "Opaque types are currently supported only in return types.",
                                )
                                .note("It should change in the future.")
                                .emit();
                            CoqType::var("OpaqueDef")
                        }
                    } else {
                        env.tcx
                            .sess
                            .struct_span_warn(
                                ty.span,
                                "Bounds on generic parameters are not supported for opaque types yet.",
                            )
                            .note("It should be supported in the future.")
                            .emit();
                        CoqType::var("OpaqueDef")
                    }
                } else {
                    env.tcx
                        .sess
                        .struct_span_warn(
                            ty.span,
                            "Generic parameters are not supported for opaque types yet.",
                        )
                        .note("It should be supported in the future.")
                        .emit();
                    CoqType::var("OpaqueDef")
                }
            } else {
                // @TODO: check whether it should be possible
                env.tcx
                    .sess
                    .struct_span_warn(
                        ty.span,
                        "OpaqueDef refers to an item of kind other than OpaqueTy.",
                    )
                    .emit();
                CoqType::var("OpaqueDef")
            }
        }
        TyKind::TraitObject(ptrait_refs, _, _) => Rc::new(CoqType::Dyn(
            ptrait_refs
                .iter()
                .map(|ptrait_ref| {
                    Path::concat(&[
                        compile_path(env, ptrait_ref.trait_ref.path),
                        Path::local("Trait"),
                    ])
                })
                .collect(),
        )),
        TyKind::Typeof(_) => CoqType::var("Typeof"),
        TyKind::Infer => Rc::new(CoqType::Infer),
        TyKind::Err(_) => CoqType::var("Error_type"),
    }
}

pub(crate) fn compile_fn_ret_ty(env: &Env, fn_ret_ty: &FnRetTy) -> Rc<CoqType> {
    match fn_ret_ty {
        FnRetTy::DefaultReturn(_) => CoqType::unit(),
        FnRetTy::Return(ty) => compile_type(env, ty),
    }
}

// The type of a function declaration
pub(crate) fn compile_fn_decl(env: &Env, fn_decl: &FnDecl) -> Rc<CoqType> {
    let ret = compile_fn_ret_ty(env, &fn_decl.output);
    Rc::new(CoqType::Function {
        args: fn_decl
            .inputs
            .iter()
            .map(|arg| compile_type(env, arg))
            .collect(),
        ret,
    })
}

/// Return the type parameters on a path
pub(crate) fn compile_path_ty_params(env: &Env, path: &rustc_hir::Path) -> Vec<Rc<CoqType>> {
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
    pub(crate) fn to_coq<'a>(&self) -> coq::Expression<'a> {
        match self {
            CoqType::Var(name) => coq::Expression::just_name(name),
            CoqType::Path { path } => coq::Expression::just_name("Ty.path")
                .apply(&coq::Expression::String(path.to_string())),
            CoqType::PathInTrait { path, self_ty } => coq::Expression::Variable {
                ident: path.as_ref().clone(),
                no_implicit: false,
            }
            .apply_many_args(&[
                (Some("Self".to_string()), self_ty.to_coq()),
                (
                    Some("Trait".to_string()),
                    coq::Expression::Code(text("ltac:(refine _)")),
                ),
            ]),
            CoqType::Application {
                func,
                args,
                is_alias: _,
            } => coq::Expression::just_name("Ty.apply").apply_many(&[
                func.to_coq(),
                coq::Expression::List {
                    exprs: args.iter().map(|arg| arg.to_coq()).collect(),
                },
            ]),
            CoqType::Function { args, ret } => coq::Expression::just_name("Ty.function")
                .apply_many(&[
                    coq::Expression::List {
                        exprs: args.iter().map(|arg| arg.to_coq()).collect(),
                    },
                    ret.to_coq(),
                ]),
            CoqType::Tuple(tys) => coq::Expression::just_name("Ty.tuple")
                .apply_many(&tys.iter().map(|ty| ty.to_coq()).collect::<Vec<_>>()),
            CoqType::OpaqueType(_) => coq::Expression::Variable {
                ident: Path::new(&["_ (* OpaqueTy *)"]),
                no_implicit: false,
            },
            CoqType::Dyn(traits) => {
                coq::Expression::just_name("dyn").apply(&coq::Expression::List {
                    exprs: traits
                        .iter()
                        .map(|trait_name| coq::Expression::Variable {
                            ident: trait_name.clone(),
                            no_implicit: false,
                        })
                        .collect(),
                })
            }
            CoqType::Infer => coq::Expression::Wild,
            CoqType::Monad(ty) => ty.to_coq(),
            CoqType::Val(ty) => ty.to_coq(),
        }
    }

    // We use this function when we need a quick and recognizable name for a type
    pub(crate) fn to_name(&self) -> String {
        match self {
            CoqType::Var(name) => name.clone(),
            CoqType::Path { path, .. } => path.to_name(),
            CoqType::PathInTrait { path, self_ty } => {
                format!("{}_{}", self_ty.to_name(), path.to_name())
            }
            CoqType::Application {
                func,
                args,
                is_alias: _,
            } => {
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
            CoqType::OpaqueType(paths) => {
                let mut name = "OpaqueType".to_string();
                for path in paths {
                    name.push('_');
                    name.push_str(&path.to_name());
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
            CoqType::Infer => "inferred_type".to_string(),
            CoqType::Monad(ty) => format!("Monad_{}", ty.to_name()),
            CoqType::Val(ty) => format!("Val_{}", ty.to_name()),
        }
    }

    /// returns true if the subtree rooted in [self] contains an opaque type
    pub(crate) fn has_opaque_types(&self) -> bool {
        match self {
            CoqType::Var(_) => false,
            CoqType::Path { .. } => false,
            CoqType::PathInTrait { path: _, self_ty } => self_ty.has_opaque_types(),
            CoqType::Application { args, .. } => args.iter().any(|ty| ty.has_opaque_types()),
            CoqType::Function { args, ret } => {
                args.iter().any(|ty| ty.has_opaque_types()) && ret.has_opaque_types()
            }
            CoqType::Tuple(types) => types.iter().any(|ty| ty.has_opaque_types()),
            CoqType::OpaqueType(_) => true,
            CoqType::Dyn(_) => false,
            CoqType::Infer => false,
            CoqType::Monad(ty) => ty.has_opaque_types(),
            CoqType::Val(ty) => ty.has_opaque_types(),
        }
    }

    /// returns the list of the parameters of opaque types in the subtree rooted in [self]
    pub(crate) fn opaque_types_bounds(&self) -> Vec<Vec<Path>> {
        match self {
            CoqType::Var(_) => vec![],
            CoqType::Path { .. } => vec![],
            CoqType::PathInTrait { path: _, self_ty } => self_ty.opaque_types_bounds(),
            CoqType::Application { args, .. } => args
                .iter()
                .flat_map(|ty| ty.opaque_types_bounds())
                .collect(),
            CoqType::Function { args, ret } => args
                .iter()
                .flat_map(|ty| ty.opaque_types_bounds())
                .chain(ret.opaque_types_bounds())
                .collect(),
            CoqType::Tuple(types) => types
                .iter()
                .flat_map(|ty| ty.opaque_types_bounds())
                .collect(),
            CoqType::OpaqueType(bounds) => vec![bounds.to_owned()],
            CoqType::Dyn(..) => vec![],
            CoqType::Infer => vec![],
            CoqType::Monad(ty) => ty.opaque_types_bounds(),
            CoqType::Val(ty) => ty.opaque_types_bounds(),
        }
    }

    /// substitutes all occurrences of OpaqueType with ty
    #[allow(dead_code)]
    pub(crate) fn subst_opaque_types(&mut self, _ty: &CoqType) {
        // match self {
        //     CoqType::Var(_) => {}
        //     CoqType::PathInTrait(_, self_ty) => self_ty.subst_opaque_types(ty),
        //     CoqType::Application { args, .. } => args
        //         .iter_mut()
        //         .map(|arg_ty| arg_ty.subst_opaque_types(ty))
        //         .collect(),
        //     CoqType::Function { args, ret } => {
        //         ret.subst_opaque_types(ty);
        //         args.iter_mut()
        //             .map(|arg_ty| arg_ty.subst_opaque_types(ty))
        //             .collect()
        //     }
        //     CoqType::Tuple(types) => types
        //         .iter_mut()
        //         .map(|one_ty| one_ty.subst_opaque_types(ty))
        //         .collect(),
        //     CoqType::Array(item_ty) => item_ty.subst_opaque_types(ty),
        //     CoqType::Ref(ref_ty, _) => ref_ty.subst_opaque_types(ty),
        //     CoqType::OpaqueType(_) => *self = ty.clone(),
        //     CoqType::Dyn(_) => (),
        //     CoqType::Infer => (),
        // }
    }

    /// returns the list of the trait names for the opaque types
    /// generated for the trait objects from the subtree rooted in [self]
    #[allow(dead_code)]
    pub(crate) fn collect_and_subst_trait_objects(&mut self) -> Vec<Vec<Path>> {
        vec![]
        // match self {
        //     CoqType::Var(_) => vec![],
        //     CoqType::PathInTrait(_, self_ty) => self_ty.collect_and_subst_trait_objects(),
        //     CoqType::Application { args, .. } => args
        //         .iter_mut()
        //         .flat_map(|ty| ty.collect_and_subst_trait_objects())
        //         .collect(),
        //     CoqType::Function { args, ret } => args
        //         .iter_mut()
        //         .flat_map(|ty| ty.collect_and_subst_trait_objects())
        //         .chain(ret.collect_and_subst_trait_objects())
        //         .collect(),
        //     CoqType::Tuple(types) => types
        //         .iter_mut()
        //         .flat_map(|ty| ty.collect_and_subst_trait_objects())
        //         .collect(),
        //     CoqType::Array(ty) => ty.collect_and_subst_trait_objects(),
        //     CoqType::Ref(ty, _) => ty.collect_and_subst_trait_objects(),
        //     CoqType::OpaqueType(..) => vec![],
        //     CoqType::Dyn(trait_names) => {
        //         let tn = trait_names.to_owned();
        //         *self = *CoqType::var(CoqType::trait_object_to_name(trait_names));
        //         vec![tn]
        //     }
        //     CoqType::Infer => vec![],
        // }
    }

    /// produces a name for the opaque type generated for the trait object
    #[allow(dead_code)]
    pub(crate) fn trait_object_to_name(trait_names: &[Path]) -> String {
        [
            "Dyn_",
            &trait_names
                .iter()
                .map(|name| name.to_name())
                .collect_vec()
                .join("_"),
        ]
        .concat()
    }
}
