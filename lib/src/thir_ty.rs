use crate::env::*;
use crate::path::*;
use crate::ty::*;
use rustc_middle::ty::GenericArgKind;
use rustc_span::def_id::DefId;
use rustc_type_ir::TyKind;
use std::rc::Rc;

pub(crate) fn compile_generic_param(env: &Env, def_id: DefId) -> String {
    to_valid_coq_name(
        IsValue::No,
        compile_def_id(env, def_id).segments.last().unwrap(),
    )
}

fn compile_poly_fn_sig<'a>(
    env: &Env<'a>,
    generics: &'a rustc_middle::ty::Generics,
    sig: &rustc_middle::ty::PolyFnSig<'a>,
) -> Rc<CoqType> {
    let sig = sig.skip_binder();
    let args = sig
        .inputs()
        .iter()
        .map(|ty| compile_type(env, generics, ty))
        .collect::<Vec<_>>();
    let ret = compile_type(env, generics, &sig.output());

    Rc::new(CoqType::Function { args, ret })
}

/// The [generics] parameter is the list of generic types available in the
/// current environment. It is required to disambiguate the names of the
/// occurrences of these generic types. It is possible to have twice the same
/// name for a generic type, especially with `impl Trait` types that are
/// represented as generics of the name "impl Trait".
pub(crate) fn compile_type<'a>(
    env: &Env<'a>,
    generics: &'a rustc_middle::ty::Generics,
    ty: &rustc_middle::ty::Ty<'a>,
) -> Rc<CoqType> {
    match ty.kind() {
        TyKind::Bool | TyKind::Char | TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_) => {
            CoqType::path(&[&ty.to_string()])
        }
        TyKind::Adt(adt_def, substs) => {
            let path = compile_def_id(env, adt_def.did());
            let args = substs
                .iter()
                .filter_map(|subst| match &subst.unpack() {
                    GenericArgKind::Type(ty) => Some(compile_type(env, generics, ty)),
                    _ => None,
                })
                .collect();
            Rc::new(CoqType::Application {
                func: Rc::new(CoqType::Path { path }),
                args,
            })
        }
        TyKind::Foreign(def_id) => Rc::new(CoqType::Path {
            path: compile_def_id(env, *def_id),
        }),
        TyKind::Str => CoqType::path(&["str"]),
        TyKind::Array(ty, _) => Rc::new(CoqType::Application {
            func: CoqType::path(&["array"]),
            args: vec![compile_type(env, generics, ty)],
        }),
        TyKind::Slice(ty) => Rc::new(CoqType::Application {
            func: CoqType::path(&["slice"]),
            args: vec![compile_type(env, generics, ty)],
        }),
        TyKind::RawPtr(rustc_middle::ty::TypeAndMut { ty, mutbl }) => {
            let ptr_name = match mutbl {
                rustc_hir::Mutability::Mut => "*mut",
                rustc_hir::Mutability::Not => "*const",
            };

            Rc::new(CoqType::Application {
                func: CoqType::path(&[ptr_name]),
                args: vec![compile_type(env, generics, ty)],
            })
        }
        TyKind::Ref(_, ty, mutbl) => CoqType::make_ref(mutbl, compile_type(env, generics, ty)),
        TyKind::FnPtr(fn_sig) => compile_poly_fn_sig(env, generics, fn_sig),
        TyKind::Dynamic(existential_predicates, _, _) => {
            let traits = existential_predicates
                .iter()
                .filter_map(
                    |existential_predicate| match existential_predicate.no_bound_vars() {
                        None => Some(Path::new(&["existential predicate with variables"])),
                        Some(existential_predicate) => match existential_predicate {
                            rustc_middle::ty::ExistentialPredicate::Trait(
                                existential_trait_ref,
                            ) => Some(Path::concat(&[
                                compile_def_id(env, existential_trait_ref.def_id),
                                Path::new(&["Trait"]),
                            ])),
                            _ => None,
                        },
                    },
                )
                .collect();

            Rc::new(CoqType::Dyn(traits))
        }
        TyKind::FnDef(_, _) => {
            let fn_sig = ty.fn_sig(env.tcx);

            compile_poly_fn_sig(env, generics, &fn_sig)
        }
        TyKind::Closure(_, generic_args) => {
            let fn_sig = generic_args.as_closure().sig();

            compile_poly_fn_sig(env, generics, &fn_sig)
        }
        // Generator(DefId, &'tcx List<GenericArg<'tcx>>, Movability),
        // GeneratorWitness(DefId, &'tcx List<GenericArg<'tcx>>),
        TyKind::Never => CoqType::path(&["never"]),
        TyKind::Tuple(tys) => Rc::new(CoqType::Tuple(
            tys.iter()
                .map(|ty| compile_type(env, generics, &ty))
                .collect(),
        )),
        TyKind::Alias(_, _) => Rc::new(CoqType::Associated),
        TyKind::Param(param) => {
            if generics.has_self && param.index == 0 {
                return Rc::new(CoqType::Var("Self".to_string()));
            }

            let type_param = generics.type_param(param, env.tcx);

            Rc::new(CoqType::Var(compile_generic_param(env, type_param.def_id)))
        }
        // Bound(DebruijnIndex, BoundTy),
        // Placeholder(Placeholder<BoundTy>),
        TyKind::Infer(_) => Rc::new(CoqType::Infer),
        TyKind::Error(error) => CoqType::var(&format!("error: {error:#?}")),
        _ => CoqType::var(&format!("type {:#?} not yet handled", ty.kind())),
    }
}
