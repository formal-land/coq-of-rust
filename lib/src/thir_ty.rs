use crate::env::*;
use crate::path::*;
use crate::ty::*;
use rustc_middle::ty::GenericArgKind;
use rustc_type_ir::sty::TyKind;
use std::rc::Rc;

pub(crate) fn compile_type(env: &Env, ty: &rustc_middle::ty::Ty) -> Rc<CoqType> {
    match ty.kind() {
        TyKind::Bool | TyKind::Char | TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_) => {
            CoqType::var(ty.to_string())
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
                func: Rc::new(CoqType::Var(Box::new(path))),
                args,
                is_alias: false,
            })
        }
        // Foreign(DefId),
        TyKind::Str => CoqType::var("str".to_string()),
        TyKind::Array(ty, _) => Rc::new(CoqType::Array(compile_type(env, ty))),
        TyKind::Slice(ty) => {
            let func = Rc::new(CoqType::Var(Box::new(Path::local("slice".to_string()))));
            let args = vec![compile_type(env, ty)];
            Rc::new(CoqType::Application {
                func,
                args,
                is_alias: false,
            })
        }
        TyKind::RawPtr(rustc_middle::ty::TypeAndMut {
            ty,
            mutbl: mutability,
        })
        | TyKind::Ref(_, ty, mutability) => {
            let ty = compile_type(env, ty);
            Rc::new(CoqType::Ref(ty, *mutability))
        }
        // Ref(Region<'tcx>, Ty<'tcx>, Mutability),
        TyKind::FnDef(_, _) => Rc::new(CoqType::Infer),
        // FnPtr(Binder<'tcx, FnSig<'tcx>>),
        // Dynamic(&'tcx List<Binder<'tcx, ExistentialPredicate<'tcx>>>, Region<'tcx>, DynKind),
        // Closure(DefId, &'tcx List<GenericArg<'tcx>>),
        // Generator(DefId, &'tcx List<GenericArg<'tcx>>, Movability),
        // GeneratorWitness(DefId, &'tcx List<GenericArg<'tcx>>),
        TyKind::Never => CoqType::var("never".to_string()),
        TyKind::Tuple(tys) => Rc::new(CoqType::Tuple(
            tys.iter().map(|ty| compile_type(env, &ty)).collect(),
        )),
        // Alias(AliasKind, AliasTy<'tcx>),
        TyKind::Param(param) => {
            Rc::new(CoqType::Var(Box::new(Path::local(param.name.to_string()))))
        }
        // Bound(DebruijnIndex, BoundTy),
        // Placeholder(Placeholder<BoundTy>),
        TyKind::Infer(_) => Rc::new(CoqType::Infer),
        TyKind::Error(error) => CoqType::var(format!("error: {error:#?}")),
        _ => {
            eprintln!("type {:#?} not yet handled", ty.kind());
            CoqType::var("type not implemented".to_string())
        }
    }
}
