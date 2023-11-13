use crate::env::*;
use crate::path::*;
use crate::ty::*;
use rustc_middle::ty::GenericArgKind;
use rustc_type_ir::sty::TyKind;
use std::rc::Rc;

pub(crate) fn compile_type(env: &Env, ty: &rustc_middle::ty::Ty) -> Rc<CoqType> {
    match ty.kind() {
        TyKind::Bool | TyKind::Char | TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_) => {
            CoqType::path(&[&ty.to_string(), "t"])
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
                    path: Box::new(path.suffix_last_with_dot_t()),
                }),
                args,
                is_alias: false,
            })
        }
        // Foreign(DefId),
        TyKind::Str => CoqType::path(&["str", "t"]),
        TyKind::Array(ty, _) => Rc::new(CoqType::Application {
            func: CoqType::path(&["array"]),
            args: vec![compile_type(env, ty)],
            is_alias: false,
        }),
        TyKind::Slice(ty) => Rc::new(CoqType::Application {
            func: CoqType::path(&["slice"]),
            args: vec![compile_type(env, ty)],
            is_alias: false,
        }),
        TyKind::RawPtr(rustc_middle::ty::TypeAndMut { ty, mutbl }) | TyKind::Ref(_, ty, mutbl) => {
            CoqType::make_ref(mutbl, compile_type(env, ty))
        }
        // Ref(Region<'tcx>, Ty<'tcx>, Mutability),
        TyKind::FnDef(_, _) => Rc::new(CoqType::Infer),
        // FnPtr(Binder<'tcx, FnSig<'tcx>>),
        // Dynamic(&'tcx List<Binder<'tcx, ExistentialPredicate<'tcx>>>, Region<'tcx>, DynKind),
        // Closure(DefId, &'tcx List<GenericArg<'tcx>>),
        // Generator(DefId, &'tcx List<GenericArg<'tcx>>, Movability),
        // GeneratorWitness(DefId, &'tcx List<GenericArg<'tcx>>),
        TyKind::Never => CoqType::path(&["never", "t"]),
        TyKind::Tuple(tys) => Rc::new(CoqType::Tuple(
            tys.iter().map(|ty| compile_type(env, &ty)).collect(),
        )),
        // Alias(AliasKind, AliasTy<'tcx>),
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
