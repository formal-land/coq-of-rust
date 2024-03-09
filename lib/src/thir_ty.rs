use crate::env::*;
use crate::path::*;
use crate::ty::*;
use rustc_middle::ty::GenericArgKind;
use rustc_type_ir::TyKind;
use std::rc::Rc;

fn compile_poly_fn_sig<'a>(env: &Env<'a>, sig: &rustc_middle::ty::PolyFnSig<'a>) -> Rc<CoqType> {
    let sig = sig.skip_binder();
    let args = sig
        .inputs()
        .iter()
        .map(|ty| compile_type(env, ty))
        .collect::<Vec<_>>();
    let ret = compile_type(env, &sig.output());

    Rc::new(CoqType::Function { args, ret })
}

pub(crate) fn compile_type<'a>(env: &Env<'a>, ty: &rustc_middle::ty::Ty<'a>) -> Rc<CoqType> {
    match ty.kind() {
        TyKind::Bool | TyKind::Char | TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_) => {
            CoqType::path(&[&ty.to_string()])
        }
        TyKind::Adt(adt_def, substs) => {
            let path = compile_def_id(env, adt_def.did());
            let args = substs
                .iter()
                .filter_map(|subst| match &subst.unpack() {
                    GenericArgKind::Type(ty) => Some(compile_type(env, ty)),
                    _ => None,
                })
                .collect();
            Rc::new(CoqType::Application {
                func: Rc::new(CoqType::Path {
                    path: Rc::new(path),
                }),
                args,
            })
        }
        // Foreign(DefId),
        TyKind::Str => CoqType::path(&["str"]),
        TyKind::Array(ty, _) => Rc::new(CoqType::Application {
            func: CoqType::path(&["array"]),
            args: vec![compile_type(env, ty)],
        }),
        TyKind::Slice(ty) => Rc::new(CoqType::Application {
            func: CoqType::path(&["slice"]),
            args: vec![compile_type(env, ty)],
        }),
        TyKind::RawPtr(rustc_middle::ty::TypeAndMut { ty, mutbl }) => {
            let ptr_name = match mutbl {
                rustc_hir::Mutability::Mut => "*mut",
                rustc_hir::Mutability::Not => "*const",
            };

            Rc::new(CoqType::Application {
                func: CoqType::path(&[ptr_name]),
                args: vec![compile_type(env, ty)],
            })
        }
        TyKind::Ref(_, ty, mutbl) => CoqType::make_ref(mutbl, compile_type(env, ty)),
        TyKind::FnPtr(fn_sig) => compile_poly_fn_sig(env, fn_sig),
        TyKind::Dynamic(existential_predicates, _, _) => {
            let traits = existential_predicates
                .iter()
                .filter_map(
                    |existential_predicate| match existential_predicate.no_bound_vars() {
                        None => Some(Path::local("existential predicate with variables")),
                        Some(existential_predicate) => match existential_predicate {
                            rustc_middle::ty::ExistentialPredicate::Trait(
                                existential_trait_ref,
                            ) => Some(Path::concat(&[
                                compile_def_id(env, existential_trait_ref.def_id),
                                Path::local("Trait"),
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

            compile_poly_fn_sig(env, &fn_sig)
        }
        TyKind::Closure(_, generic_args) => {
            let fn_sig = generic_args.as_closure().sig();

            compile_poly_fn_sig(env, &fn_sig)
        }
        // Generator(DefId, &'tcx List<GenericArg<'tcx>>, Movability),
        // GeneratorWitness(DefId, &'tcx List<GenericArg<'tcx>>),
        TyKind::Never => CoqType::path(&["never"]),
        TyKind::Tuple(tys) => Rc::new(CoqType::Tuple(
            tys.iter().map(|ty| compile_type(env, &ty)).collect(),
        )),
        TyKind::Alias(_, _) => {
            // These types are generally too complex to represent in Coq.
            Rc::new(CoqType::Infer)
        }
        TyKind::Param(param) => Rc::new(CoqType::Var(param.name.to_string())),
        // Bound(DebruijnIndex, BoundTy),
        // Placeholder(Placeholder<BoundTy>),
        TyKind::Infer(_) => Rc::new(CoqType::Infer),
        TyKind::Error(error) => CoqType::var(&format!("error: {error:#?}")),
        _ => {
            eprintln!("type {:#?} not yet handled", ty.kind());
            CoqType::var("type not implemented")
        }
    }
}
