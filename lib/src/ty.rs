use crate::coq::{self, LOCAL_STATE_TRAIT_INSTANCE};
use crate::env::*;
use crate::path::*;
use crate::render::*;
use crate::top_level::*;
use itertools::Itertools;
use rustc_hir::{BareFnTy, FnDecl, FnRetTy, GenericBound, ItemKind, OpaqueTyOrigin, Ty, TyKind};

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub(crate) enum CoqType {
    Var(Box<Path>),
    VarWithSelfTy(Box<Path>, Box<CoqType>),
    Application {
        func: Box<CoqType>,
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
    OpaqueType(Vec<Path>),
    Dyn(Vec<Path>),
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
            func: Box::new(CoqType::Var(Box::new(Path::local(format!(
                "M (H := {LOCAL_STATE_TRAIT_INSTANCE})"
            ))))),
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
        CoqType::VarWithSelfTy(path, self_ty) => CoqType::VarWithSelfTy(path, mt_ty(self_ty)),
        CoqType::Function { args, ret } => CoqType::Function {
            args: args.into_iter().map(mt_ty).collect(),
            ret: CoqType::monad(mt_ty(ret)),
        },
        CoqType::Tuple(tys) => CoqType::Tuple(tys.into_iter().map(mt_ty).collect()),
        CoqType::Array(ty) => CoqType::Array(mt_ty(ty)),
        CoqType::Ref(ty, mutability) => CoqType::Ref(mt_ty(ty), mutability),
        CoqType::OpaqueType(..) => ty,
        CoqType::Dyn(..) => ty,
    }
}

#[allow(clippy::boxed_local)]
pub(crate) fn mt_ty(ty: Box<CoqType>) -> Box<CoqType> {
    Box::new(mt_ty_unboxed(*ty))
}

pub(crate) fn compile_type(env: &Env, ty: &Ty) -> Box<CoqType> {
    match &ty.kind {
        TyKind::Slice(ty) => {
            let func = Box::new(CoqType::Var(Box::new(Path::local("Slice".to_string()))));
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
            let self_ty = match qpath {
                rustc_hir::QPath::Resolved(Some(self_ty), _) => Some(compile_type(env, self_ty)),
                _ => None,
            };
            let coq_path = Box::new(compile_qpath(env, qpath));
            let func = Box::new(match self_ty {
                Some(self_ty) => CoqType::VarWithSelfTy(coq_path.clone(), self_ty),
                None => CoqType::Var(coq_path.clone()),
            });
            let params = match qpath {
                rustc_hir::QPath::Resolved(_, path) => {
                    if let Some(generics) = get_path_generics(env, path) {
                        let type_params_name_and_default_status =
                            type_params_name_and_default_status(generics);
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
                                        Box::new(CoqType::Var(Box::new(Path { segments })))
                                    } else {
                                        CoqType::var("_".to_string())
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
            if params.is_empty() {
                func
            } else {
                Box::new(CoqType::Application { func, args: params })
            }
        }
        TyKind::OpaqueDef(item_id, _, _) => {
            let item = env.tcx.hir().item(*item_id);
            if let ItemKind::OpaqueTy(opaque_ty) = item.kind {
                if opaque_ty.generics.params.is_empty() {
                    if opaque_ty.generics.predicates.is_empty() {
                        if let OpaqueTyOrigin::FnReturn(_) = opaque_ty.origin {
                            Box::new(CoqType::OpaqueType(
                                opaque_ty
                                    .bounds
                                    .iter()
                                    .filter_map(|bound| match bound {
                                        GenericBound::Trait(p_trait_ref, _) => {
                                            Some(compile_path(env, p_trait_ref.trait_ref.path))
                                        }
                                        GenericBound::LangItemTrait(..) => {
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
                                        GenericBound::Outlives(..) => None
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
                            CoqType::var("OpaqueDef".to_string())
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
                        CoqType::var("OpaqueDef".to_string())
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
                    CoqType::var("OpaqueDef".to_string())
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
                CoqType::var("OpaqueDef".to_string())
            }
        }
        TyKind::TraitObject(ptrait_refs, _, _) => Box::new(CoqType::Dyn(
            ptrait_refs
                .iter()
                .map(|ptrait_ref| compile_path(env, ptrait_ref.trait_ref.path))
                .collect(),
        )),
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
    pub(crate) fn to_coq<'a>(&self) -> coq::Expression<'a> {
        match self {
            CoqType::Var(path) => coq::Expression::Variable {
                ident: *path.clone(),
                no_implicit: false,
            },
            CoqType::VarWithSelfTy(path, self_ty) => coq::Expression::Variable {
                ident: *path.clone(),
                no_implicit: false,
            }
            .apply_arg(&Some("Self".to_string()), &self_ty.to_coq()),
            CoqType::Application { func, args } => func
                .to_coq()
                .apply_many(&args.iter().map(|arg| arg.to_coq()).collect::<Vec<_>>()),
            CoqType::Function { args, ret } => ret
                .to_coq()
                .arrows_from(&args.iter().map(|arg| arg.to_coq()).collect::<Vec<_>>()),
            CoqType::Tuple(tys) => coq::Expression::multiply_many(
                &tys.iter().map(|ty| ty.to_coq()).collect::<Vec<_>>(),
            ),
            CoqType::Array(ty) => coq::Expression::Variable {
                ident: Path::new(&["list"]),
                no_implicit: false,
            }
            .apply(&ty.to_coq()),
            CoqType::Ref(ty, mutbl) => coq::Expression::Variable {
                ident: Path::new(&[match mutbl {
                    rustc_hir::Mutability::Mut => "mut_ref",
                    rustc_hir::Mutability::Not => "ref",
                }]),
                no_implicit: false,
            }
            .apply(&ty.to_coq()),
            CoqType::OpaqueType(_) => coq::Expression::Variable {
                ident: Path::new(&["_ (* OpaqueTy *)"]),
                no_implicit: false,
            },
            CoqType::Dyn(_) => coq::Expression::Variable {
                ident: Path::new(&["_ (* dyn *)"]),
                no_implicit: false,
            },
        }
    }

    // we need this function to fix aligning
    pub(crate) fn to_coq_tuning(&self) -> coq::Expression {
        match self {
            CoqType::Ref(ty, _) => ty.to_coq(),
            _ => self.to_coq(),
        }
    }

    pub(crate) fn to_doc<'a>(&self, with_paren: bool) -> Doc<'a> {
        match self {
            CoqType::Var(path) => path.to_doc(),
            CoqType::VarWithSelfTy(path, self_ty) => paren(
                with_paren,
                nest([
                    path.to_doc(),
                    line(),
                    nest([text("(Self :="), line(), self_ty.to_doc(false), text(")")]),
                ]),
            ),
            CoqType::Application { func, args } => paren(
                with_paren,
                nest([
                    func.to_doc(true),
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
            CoqType::OpaqueType(_) => text("_ (* OpaqueTy *)"),
            CoqType::Dyn(_) => text("_ (* OpaqueTy *)"),
        }
    }

    // We use this function when we need a quick and recognizable name for a type
    pub(crate) fn to_name(&self) -> String {
        match self {
            CoqType::Var(path) => path.to_name(),
            CoqType::VarWithSelfTy(path, self_ty) => {
                format!("{}_{}", self_ty.to_name(), path.to_name())
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
            CoqType::OpaqueType(_) => todo!(),
            CoqType::Dyn(_) => todo!(),
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

    /// returns true if the subtree rooted in [self] contains an opaque type
    pub(crate) fn has_opaque_types(&self) -> bool {
        match self {
            CoqType::Var(_) => false,
            CoqType::VarWithSelfTy(_, self_ty) => self_ty.has_opaque_types(),
            CoqType::Application { args, .. } => args.iter().any(|ty| ty.has_opaque_types()),
            CoqType::Function { args, ret } => {
                args.iter().any(|ty| ty.has_opaque_types()) && ret.has_opaque_types()
            }
            CoqType::Tuple(types) => types.iter().any(|ty| ty.has_opaque_types()),
            CoqType::Array(ty) => ty.has_opaque_types(),
            CoqType::Ref(ty, _) => ty.has_opaque_types(),
            CoqType::OpaqueType(_) => true,
            CoqType::Dyn(_) => false,
        }
    }

    /// returns the list of the parameters of opaque types in the subtree rooted in [self]
    pub(crate) fn opaque_types_bounds(&self) -> Vec<Vec<Path>> {
        match self {
            CoqType::Var(_) => vec![],
            CoqType::VarWithSelfTy(_, self_ty) => self_ty.opaque_types_bounds(),
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
            CoqType::Array(ty) => ty.opaque_types_bounds(),
            CoqType::Ref(ty, _) => ty.opaque_types_bounds(),
            CoqType::OpaqueType(bounds) => vec![bounds.to_owned()],
            CoqType::Dyn(..) => vec![],
        }
    }

    /// substitutes all occurrences of OpaqueType with ty
    pub(crate) fn subst_opaque_types(&mut self, ty: &CoqType) {
        match self {
            CoqType::Var(_) => {}
            CoqType::VarWithSelfTy(_, self_ty) => self_ty.subst_opaque_types(ty),
            CoqType::Application { args, .. } => args
                .iter_mut()
                .map(|arg_ty| arg_ty.subst_opaque_types(ty))
                .collect(),
            CoqType::Function { args, ret } => {
                ret.subst_opaque_types(ty);
                args.iter_mut()
                    .map(|arg_ty| arg_ty.subst_opaque_types(ty))
                    .collect()
            }
            CoqType::Tuple(types) => types
                .iter_mut()
                .map(|one_ty| one_ty.subst_opaque_types(ty))
                .collect(),
            CoqType::Array(item_ty) => item_ty.subst_opaque_types(ty),
            CoqType::Ref(ref_ty, _) => ref_ty.subst_opaque_types(ty),
            CoqType::OpaqueType(_) => *self = ty.clone(),
            CoqType::Dyn(_) => (),
        }
    }

    /// returns the list of the trait names for the opaque types
    /// generated for the trait objects from the subtree rooted in [self]
    pub(crate) fn collect_and_subst_trait_objects(&mut self) -> Vec<Vec<Path>> {
        match self {
            CoqType::Var(_) => vec![],
            CoqType::VarWithSelfTy(_, self_ty) => self_ty.collect_and_subst_trait_objects(),
            CoqType::Application { args, .. } => args
                .iter_mut()
                .flat_map(|ty| ty.collect_and_subst_trait_objects())
                .collect(),
            CoqType::Function { args, ret } => args
                .iter_mut()
                .flat_map(|ty| ty.collect_and_subst_trait_objects())
                .chain(ret.collect_and_subst_trait_objects())
                .collect(),
            CoqType::Tuple(types) => types
                .iter_mut()
                .flat_map(|ty| ty.collect_and_subst_trait_objects())
                .collect(),
            CoqType::Array(ty) => ty.collect_and_subst_trait_objects(),
            CoqType::Ref(ty, _) => ty.collect_and_subst_trait_objects(),
            CoqType::OpaqueType(..) => vec![],
            CoqType::Dyn(trait_names) => {
                let tn = trait_names.to_owned();
                *self = *CoqType::var(CoqType::trait_object_to_name(trait_names));
                vec![tn]
            }
        }
    }

    /// produces a name for the opaque type generated for the trait object
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
