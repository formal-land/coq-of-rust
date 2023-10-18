use crate::env::*;
use crate::path::*;
use crate::ty::*;
use rustc_middle::ty::GenericArgKind;
use rustc_type_ir::sty::TyKind;

pub(crate) fn compile_type(env: &Env, ty: &rustc_middle::ty::Ty) -> Box<CoqType> {
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
            Box::new(CoqType::Application {
                func: Box::new(CoqType::Var(Box::new(path))),
                args,
            })
        }
        // Foreign(DefId),
        TyKind::Str => CoqType::var("str".to_string()),
        TyKind::Array(ty, _) => Box::new(CoqType::Array(compile_type(env, ty))),
        TyKind::Slice(ty) => {
            let func = Box::new(CoqType::Var(Box::new(Path::local("Slice".to_string()))));
            let args = vec![compile_type(env, ty)];
            Box::new(CoqType::Application { func, args })
        }
        // RawPtr(TypeAndMut<'tcx>),
        TyKind::Ref(_, ty, mutability) => {
            let ty = compile_type(env, ty);
            Box::new(CoqType::Ref(ty, *mutability))
        }
        // Ref(Region<'tcx>, Ty<'tcx>, Mutability),
        // FnDef(DefId, &'tcx List<GenericArg<'tcx>>),
        // FnPtr(Binder<'tcx, FnSig<'tcx>>),
        // Dynamic(&'tcx List<Binder<'tcx, ExistentialPredicate<'tcx>>>, Region<'tcx>, DynKind),
        // Closure(DefId, &'tcx List<GenericArg<'tcx>>),
        // Generator(DefId, &'tcx List<GenericArg<'tcx>>, Movability),
        // GeneratorWitness(DefId, &'tcx List<GenericArg<'tcx>>),
        TyKind::Never => CoqType::var("never".to_string()),
        TyKind::Tuple(tys) => Box::new(CoqType::Tuple(
            tys.iter().map(|ty| compile_type(env, &ty)).collect(),
        )),
        // Alias(AliasKind, AliasTy<'tcx>),
        TyKind::Param(_) => {
            // Box::new(CoqType::Var(Box::new(Path::local(param.name.to_string()))))
            Box::new(CoqType::Infer)
        }
        // Bound(DebruijnIndex, BoundTy),
        // Placeholder(Placeholder<BoundTy>),
        // Infer(InferTy),
        // Error(ErrorGuaranteed),
        _ => panic!("type {:#?} not yet handled", ty.kind()),
    }
}
