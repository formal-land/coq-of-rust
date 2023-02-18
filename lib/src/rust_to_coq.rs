use crate::path::*;
use crate::render::*;
use pretty::RcDoc;
use rustc_hir::{FnDecl, FnRetTy, Ty, TyKind};
use rustc_middle::ty::TyCtxt;

#[derive(Debug)]
pub enum CoqType {
    Var(Path),
    Application {
        func: Box<CoqType>,
        args: Vec<CoqType>,
    },
    Function {
        func: Box<CoqType>,
        arg: Box<CoqType>,
    },
    Tuple(Vec<CoqType>),
    Array(Box<CoqType>),
    Ref(Box<CoqType>, rustc_hir::Mutability),
}

impl CoqType {
    pub fn unit() -> CoqType {
        CoqType::Tuple(vec![])
    }
}

pub fn compile_type(tcx: &TyCtxt, ty: &Ty) -> CoqType {
    match &ty.kind {
        TyKind::Slice(_) => CoqType::Var(Path::local("Slice".to_string())),
        TyKind::Array(ty, _) => CoqType::Array(Box::new(compile_type(tcx, ty))),
        TyKind::Ptr(mut_ty) => CoqType::Ref(Box::new(compile_type(tcx, mut_ty.ty)), mut_ty.mutbl),
        TyKind::Ref(_, mut_ty) => {
            CoqType::Ref(Box::new(compile_type(tcx, mut_ty.ty)), mut_ty.mutbl)
        }
        TyKind::BareFn(_) => CoqType::Var(Path::local("BareFn".to_string())),
        TyKind::Never => CoqType::Var(Path::local("Empty_set".to_string())),
        TyKind::Tup(tys) => CoqType::Tuple(tys.iter().map(|ty| compile_type(tcx, ty)).collect()),
        TyKind::Path(qpath) => match qpath {
            rustc_hir::QPath::Resolved(_, path) => match path.res {
                rustc_hir::def::Res::SelfTyAlias {
                    alias_to,
                    forbid_generic: _,
                    is_trait_impl: _,
                } => {
                    let self_ty_alias_name = tcx.type_of(alias_to).to_string();
                    CoqType::Var(Path::local(self_ty_alias_name))
                }
                _ => {
                    let path = compile_qpath(qpath);
                    CoqType::Var(path)
                }
            },
            _ => {
                let path = compile_qpath(qpath);
                CoqType::Var(path)
            }
        },
        TyKind::OpaqueDef(_, _, _) => CoqType::Var(Path::local("OpaqueDef".to_string())),
        TyKind::TraitObject(_, _, _) => CoqType::Var(Path::local("TraitObject".to_string())),
        TyKind::Typeof(_) => CoqType::Var(Path::local("Typeof".to_string())),
        TyKind::Infer => CoqType::Var(Path::local("_".to_string())),
        TyKind::Err => CoqType::Var(Path::local("Error_type".to_string())),
    }
}

pub fn compile_fn_ret_ty(tcx: &TyCtxt, fn_ret_ty: &FnRetTy) -> Option<CoqType> {
    match fn_ret_ty {
        FnRetTy::DefaultReturn(_) => None,
        FnRetTy::Return(ty) => Some(compile_type(tcx, ty)),
    }
}

pub fn compile_fn_decl(tcx: &TyCtxt, fn_decl: &FnDecl) -> CoqType {
    let ret_ty = match compile_fn_ret_ty(tcx, &fn_decl.output) {
        Some(ret_ty) => ret_ty,
        None => CoqType::Var(Path::local("_".to_string())),
    };
    fn_decl
        .inputs
        .iter()
        .rfold(ret_ty, |acc, arg| CoqType::Function {
            func: Box::new(compile_type(tcx, arg)),
            arg: Box::new(acc),
        })
}

impl CoqType {
    pub fn to_doc(&self) -> RcDoc {
        match self {
            CoqType::Var(path) => path.to_doc(),
            CoqType::Application { func, args } => RcDoc::concat([
                func.to_doc(),
                RcDoc::space(),
                RcDoc::intersperse(args.iter().map(|arg| arg.to_doc()), RcDoc::space()),
            ]),
            CoqType::Function { func, arg } => indent(RcDoc::concat([
                func.to_doc(),
                RcDoc::line(),
                RcDoc::text("->"),
                RcDoc::line(),
                arg.to_doc(),
            ]))
            .group(),
            CoqType::Tuple(tys) => RcDoc::concat([RcDoc::intersperse(
                tys.iter().map(|ty| ty.to_doc()),
                RcDoc::concat([RcDoc::space(), RcDoc::text("*"), RcDoc::space()]),
            )])
            .group(),
            CoqType::Array(ty) => RcDoc::concat([RcDoc::text("list"), RcDoc::space(), ty.to_doc()]),
            CoqType::Ref(ty, mutbl) => match mutbl {
                rustc_hir::Mutability::Mut => {
                    RcDoc::concat([RcDoc::text("mut_ref"), RcDoc::space(), ty.to_doc()])
                }
                rustc_hir::Mutability::Not => {
                    RcDoc::concat([RcDoc::text("static_ref"), RcDoc::space(), ty.to_doc()])
                }
            },
        }
    }
}
