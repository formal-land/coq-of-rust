extern crate rustc_hir;
extern crate rustc_middle;

use crate::path::*;
use crate::render::*;
use pretty::RcDoc;

#[derive(Debug)]
pub enum Type {
    Var(Path),
    Application { func: Box<Type>, args: Vec<Type> },
    Function { func: Box<Type>, arg: Box<Type> },
    Tuple(Vec<Type>),
    Array(Box<Type>),
    Ref(Box<Type>),
}

impl Type {
    pub fn unit() -> Type {
        Type::Tuple(vec![])
    }
}

pub fn compile_type(ty: &rustc_hir::Ty) -> Type {
    match &ty.kind {
        rustc_hir::TyKind::Slice(_) => Type::Var(Path::local("Slice".to_string())),
        rustc_hir::TyKind::Array(ty, _) => Type::Array(Box::new(compile_type(ty))),
        rustc_hir::TyKind::Ptr(ty) => Type::Ref(Box::new(compile_type(ty.ty))),
        rustc_hir::TyKind::Ref(_, ty) => Type::Ref(Box::new(compile_type(ty.ty))),
        rustc_hir::TyKind::BareFn(_) => Type::Var(Path::local("BareFn".to_string())),
        rustc_hir::TyKind::Never => Type::Var(Path::local("Empty_set".to_string())),
        rustc_hir::TyKind::Tup(tys) => Type::Tuple(tys.iter().map(compile_type).collect()),
        rustc_hir::TyKind::Path(qpath) => {
            let path = compile_qpath(qpath);
            Type::Var(path)
        }
        rustc_hir::TyKind::OpaqueDef(_, _, _) => Type::Var(Path::local("OpaqueDef".to_string())),
        rustc_hir::TyKind::TraitObject(_, _, _) => {
            Type::Var(Path::local("TraitObject".to_string()))
        }
        rustc_hir::TyKind::Typeof(_) => Type::Var(Path::local("Typeof".to_string())),
        rustc_hir::TyKind::Infer => Type::Var(Path::local("_".to_string())),
        rustc_hir::TyKind::Err => Type::Var(Path::local("Error_type".to_string())),
    }
}

pub fn compile_fn_ret_ty(fn_ret_ty: &rustc_hir::FnRetTy) -> Option<Type> {
    match fn_ret_ty {
        rustc_hir::FnRetTy::DefaultReturn(_) => None,
        rustc_hir::FnRetTy::Return(ty) => Some(compile_type(ty)),
    }
}

pub fn compile_fn_decl(fn_decl: &rustc_hir::FnDecl) -> Type {
    let ret_ty = match compile_fn_ret_ty(&fn_decl.output) {
        Some(ret_ty) => ret_ty,
        None => Type::Var(Path::local("_".to_string())),
    };
    fn_decl
        .inputs
        .iter()
        .rfold(ret_ty, |acc, arg| Type::Function {
            func: Box::new(compile_type(arg)),
            arg: Box::new(acc),
        })
}

impl Type {
    pub fn to_doc(&self) -> RcDoc {
        match self {
            Type::Var(path) => path.to_doc(),
            Type::Application { func, args } => RcDoc::concat([
                func.to_doc(),
                RcDoc::space(),
                RcDoc::intersperse(args.iter().map(|arg| arg.to_doc()), RcDoc::space()),
            ]),
            Type::Function { func, arg } => indent(RcDoc::concat([
                func.to_doc(),
                RcDoc::line(),
                RcDoc::text("->"),
                RcDoc::line(),
                arg.to_doc(),
            ]))
            .group(),
            Type::Tuple(tys) => RcDoc::concat([RcDoc::intersperse(
                tys.iter().map(|ty| ty.to_doc()),
                RcDoc::concat([RcDoc::space(), RcDoc::text("*"), RcDoc::space()]),
            )])
            .group(),
            Type::Array(ty) => RcDoc::concat([RcDoc::text("list"), RcDoc::space(), ty.to_doc()]),
            Type::Ref(ty) => RcDoc::concat([RcDoc::text("ref"), RcDoc::space(), ty.to_doc()]),
        }
    }
}
