extern crate rustc_hir;
extern crate rustc_middle;

use crate::expression::*;
use crate::render::*;
use crate::ty::*;
use pretty::RcDoc;

/// Representation of top-level hir [Item]s in coq-of-rust
/// See https://doc.rust-lang.org/reference/items.html
#[derive(Debug)]
enum TopLevelItem {
    Definition {
        name: String,
        args: Vec<(String, Type)>,
        ret_ty: Option<Type>,
        body: Expr,
    },
    TypeAlias {
        name: String,
        ty: Box<Type>,
    },
    Module {
        name: String,
        body: TopLevel,
    },
    Error(String),
}

#[derive(Debug)]
pub struct TopLevel(Vec<TopLevelItem>);

/// [compile_top_level_item] compiles hir [Item]s into coq-of-rust (optional)
/// items.
/// - See https://doc.rust-lang.org/stable/nightly-rustc/rustc_hir/struct.Item.html
///   and the doc for [TopLevelItem]
/// - [rustc_middle::hir::map::Map] is intuitively the type for hir environments
/// - Method [body] allows retrievient the body of an identifier [body_id] in an
///   hir environment [hir]
fn compile_top_level_item(
    hir: rustc_middle::hir::map::Map,
    item: &rustc_hir::Item,
) -> Vec<TopLevelItem> {
    match &item.kind {
        rustc_hir::ItemKind::ExternCrate(_) => vec![],
        rustc_hir::ItemKind::Use(_, _) => vec![],
        rustc_hir::ItemKind::Static(_, _, body_id) => {
            let expr = hir.body(*body_id).value;
            vec![TopLevelItem::Definition {
                name: item.ident.name.to_string(),
                args: vec![],
                ret_ty: None,
                body: compile_expr(hir, expr),
            }]
        }
        rustc_hir::ItemKind::Const(_, body_id) => {
            let expr = hir.body(*body_id).value;
            vec![TopLevelItem::Definition {
                name: item.ident.name.to_string(),
                args: vec![],
                ret_ty: None,
                body: compile_expr(hir, expr),
            }]
        }
        rustc_hir::ItemKind::Fn(_fn_sig, _, body_id) => {
            let expr = hir.body(*body_id).value;
            vec![TopLevelItem::Definition {
                name: item.ident.name.to_string(),
                args: vec![],
                ret_ty: None,
                body: compile_expr(hir, expr),
            }]
        }
        rustc_hir::ItemKind::Macro(_, _) => vec![],
        rustc_hir::ItemKind::Mod(module) => {
            let items = module
                .item_ids
                .iter()
                .flat_map(|item_id| {
                    let item = hir.item(*item_id);
                    compile_top_level_item(hir, item)
                })
                .collect();
            vec![TopLevelItem::Module {
                name: item.ident.name.to_string(),
                body: TopLevel(items),
            }]
        }
        rustc_hir::ItemKind::ForeignMod { .. } => {
            vec![TopLevelItem::Error("ForeignMod".to_string())]
        }
        rustc_hir::ItemKind::GlobalAsm(_) => vec![TopLevelItem::Error("GlobalAsm".to_string())],
        rustc_hir::ItemKind::TyAlias(_, _) => vec![TopLevelItem::Error("TyAlias".to_string())],
        rustc_hir::ItemKind::OpaqueTy(_) => vec![TopLevelItem::Error("OpaqueTy".to_string())],
        rustc_hir::ItemKind::Enum(_, _) => vec![TopLevelItem::Error("Enum".to_string())],
        rustc_hir::ItemKind::Struct(body, _) => match body {
            rustc_hir::VariantData::Tuple(fields, _, _) => {
                let ty = Box::new(Type::Tuple(
                    fields
                        .iter()
                        .map(|field| compile_type(hir, &field.ty))
                        .collect(),
                ));
                vec![TopLevelItem::TypeAlias {
                    name: item.ident.name.to_string(),
                    ty,
                }]
            }
            _ => vec![TopLevelItem::Error("Struct".to_string())],
        },
        rustc_hir::ItemKind::Union(_, _) => vec![TopLevelItem::Error("Union".to_string())],
        rustc_hir::ItemKind::Trait(_, _, _, _, _) => vec![TopLevelItem::Error("Trait".to_string())],
        rustc_hir::ItemKind::TraitAlias(_, _) => {
            vec![TopLevelItem::Error("TraitAlias".to_string())]
        }
        rustc_hir::ItemKind::Impl(rustc_hir::Impl { items, .. }) => items
            .iter()
            .flat_map(|item| {
                let item = hir.impl_item(item.id);
                match &item.kind {
                    rustc_hir::ImplItemKind::Const(_, body_id) => {
                        let expr = hir.body(*body_id).value;
                        vec![TopLevelItem::Definition {
                            name: item.ident.name.to_string(),
                            args: vec![],
                            ret_ty: None,
                            body: compile_expr(hir, expr),
                        }]
                    }
                    rustc_hir::ImplItemKind::Fn(fn_sig, body_id) => {
                        let arg_names =
                            hir.body(*body_id)
                                .params
                                .iter()
                                .map(|param| match param.pat.kind {
                                    rustc_hir::PatKind::Binding(_, _, ident, _) => {
                                        ident.name.to_string()
                                    }
                                    _ => "Pattern".to_string(),
                                });
                        let arg_tys = fn_sig.decl.inputs.iter().map(|ty| compile_type(hir, ty));
                        let ret_ty = match &fn_sig.decl.output {
                            rustc_hir::FnRetTy::DefaultReturn(_) => None,
                            rustc_hir::FnRetTy::Return(ty) => Some(compile_type(hir, ty)),
                        };
                        let expr = hir.body(*body_id).value;
                        vec![TopLevelItem::Definition {
                            name: item.ident.name.to_string(),
                            args: arg_names.zip(arg_tys).collect(),
                            ret_ty,
                            body: compile_expr(hir, expr),
                        }]
                    }
                    rustc_hir::ImplItemKind::Type(_) => {
                        vec![TopLevelItem::Error("ImplItemKind::Type".to_string())]
                    }
                }
            })
            .collect(),
    }
}

pub fn compile_top_level(tcx: rustc_middle::ty::TyCtxt) -> TopLevel {
    let hir = tcx.hir();
    TopLevel(
        hir.items()
            .flat_map(|item_id| {
                let item = hir.item(item_id);
                compile_top_level_item(hir, item)
            })
            .collect(),
    )
}

impl TopLevelItem {
    fn to_doc(&self) -> RcDoc {
        match self {
            TopLevelItem::Definition {
                name,
                args,
                ret_ty,
                body,
            } => indent(RcDoc::concat([
                RcDoc::concat([
                    RcDoc::text("Definition"),
                    RcDoc::space(),
                    RcDoc::text(name),
                    RcDoc::intersperse(
                        args.iter().map(|(name, ty)| {
                            RcDoc::concat([
                                RcDoc::line(),
                                indent(
                                    RcDoc::concat([
                                        RcDoc::text("("),
                                        RcDoc::text(name),
                                        RcDoc::space(),
                                        RcDoc::text(":"),
                                        RcDoc::space(),
                                        ty.to_doc(),
                                        RcDoc::text(")"),
                                    ])
                                    .group(),
                                ),
                            ])
                        }),
                        RcDoc::nil(),
                    ),
                    match ret_ty {
                        Some(ty) => RcDoc::concat([
                            RcDoc::line(),
                            RcDoc::text(":"),
                            RcDoc::space(),
                            ty.to_doc(),
                        ]),
                        None => RcDoc::nil(),
                    },
                    RcDoc::space(),
                    RcDoc::text(":="),
                ])
                .group(),
                RcDoc::concat([
                    RcDoc::hardline().append(body.to_doc(false)),
                    RcDoc::text("."),
                ]),
            ])),
            TopLevelItem::Module { name, body } => indent(RcDoc::concat([
                RcDoc::text("Module"),
                RcDoc::space(),
                RcDoc::text(name),
                RcDoc::space(),
                RcDoc::text(":="),
                RcDoc::hardline().append(body.to_doc()).group(),
                RcDoc::text("."),
            ]))
            .group(),
            TopLevelItem::TypeAlias { name, ty } => indent(RcDoc::concat([
                RcDoc::concat([
                    RcDoc::text("Definition"),
                    RcDoc::space(),
                    RcDoc::text(name),
                    RcDoc::space(),
                    RcDoc::text(":"),
                    RcDoc::space(),
                    RcDoc::text("Set"),
                    RcDoc::space(),
                    RcDoc::text(":="),
                ])
                .group(),
                RcDoc::hardline(),
                ty.to_doc(),
                RcDoc::text("."),
            ])),
            TopLevelItem::Error(message) => RcDoc::concat([
                RcDoc::text("Error"),
                RcDoc::space(),
                RcDoc::text(message),
                RcDoc::text("."),
            ])
            .group(),
        }
    }
}

impl TopLevel {
    fn to_doc(&self) -> RcDoc {
        RcDoc::intersperse(
            self.0.iter().map(|item| item.to_doc()),
            RcDoc::hardline().append(RcDoc::hardline()),
        )
    }

    pub fn to_pretty(&self, width: usize) -> String {
        let mut w = Vec::new();
        self.to_doc().render(width, &mut w).unwrap();
        String::from_utf8(w).unwrap()
    }
}
