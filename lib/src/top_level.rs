use crate::expression::*;
use crate::header::*;
use crate::path::*;
use crate::render::*;
use crate::ty::*;
use pretty::RcDoc;

use rustc_hir::{Impl, ImplItemKind, Item, ItemKind, PatKind, TraitItemKind, VariantData};
use rustc_middle::ty::TyCtxt;

#[derive(Debug)]
enum TraitItem {
    Definition { ty: CoqType },
    Type,
}

/// Representation of top-level hir [Item]s in coq-of-rust
/// See https://doc.rust-lang.org/reference/items.html
#[derive(Debug)]
enum TopLevelItem {
    Definition {
        name: String,
        args: Vec<(String, CoqType)>,
        ret_ty: Option<CoqType>,
        body: Expr,
    },
    TypeAlias {
        name: String,
        ty: Box<CoqType>,
    },
    TypeRecord {
        name: String,
        fields: Vec<(String, CoqType)>,
    },
    Module {
        name: String,
        body: TopLevel,
    },
    Impl {
        self_ty: CoqType,
        body: TopLevel,
    },
    Trait {
        name: String,
        body: Vec<(String, TraitItem)>,
    },
    TraitImpl {
        self_ty: CoqType,
        of_trait: Path,
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
fn compile_top_level_item(tcx: TyCtxt, item: &Item) -> Vec<TopLevelItem> {
    match &item.kind {
        ItemKind::ExternCrate(_) => vec![],
        ItemKind::Use(_, _) => vec![],
        ItemKind::Static(_, _, body_id) => {
            let expr = tcx.hir().body(*body_id).value;
            vec![TopLevelItem::Definition {
                name: item.ident.name.to_string(),
                args: vec![],
                ret_ty: None,
                body: compile_expr(tcx, expr),
            }]
        }
        ItemKind::Const(_, body_id) => {
            let expr = tcx.hir().body(*body_id).value;
            vec![TopLevelItem::Definition {
                name: item.ident.name.to_string(),
                args: vec![],
                ret_ty: None,
                body: compile_expr(tcx, expr),
            }]
        }
        ItemKind::Fn(_fn_sig, _, body_id) => {
            let expr = tcx.hir().body(*body_id).value;
            vec![TopLevelItem::Definition {
                name: item.ident.name.to_string(),
                args: vec![],
                ret_ty: None,
                body: compile_expr(tcx, expr),
            }]
        }
        ItemKind::Macro(_, _) => vec![],
        ItemKind::Mod(module) => {
            let items = module
                .item_ids
                .iter()
                .flat_map(|item_id| {
                    let item = tcx.hir().item(*item_id);
                    compile_top_level_item(tcx, item)
                })
                .collect();
            vec![TopLevelItem::Module {
                name: item.ident.name.to_string(),
                body: TopLevel(items),
            }]
        }
        ItemKind::ForeignMod { .. } => {
            vec![TopLevelItem::Error("ForeignMod".to_string())]
        }
        ItemKind::GlobalAsm(_) => vec![TopLevelItem::Error("GlobalAsm".to_string())],
        ItemKind::TyAlias(_, _) => vec![TopLevelItem::Error("TyAlias".to_string())],
        ItemKind::OpaqueTy(_) => vec![TopLevelItem::Error("OpaqueTy".to_string())],
        ItemKind::Enum(_, _) => vec![TopLevelItem::Error("Enum".to_string())],
        ItemKind::Struct(body, _) => match body {
            VariantData::Struct(fields, _) => {
                let fields = fields
                    .iter()
                    .map(|field| (field.ident.name.to_string(), compile_type(&tcx, field.ty)))
                    .collect();
                vec![TopLevelItem::TypeRecord {
                    name: item.ident.name.to_string(),
                    fields,
                }]
            }
            VariantData::Tuple(fields, _, _) => {
                let ty = Box::new(CoqType::Tuple(
                    fields
                        .iter()
                        .map(|field| compile_type(&tcx, field.ty))
                        .collect(),
                ));
                vec![TopLevelItem::TypeAlias {
                    name: item.ident.name.to_string(),
                    ty,
                }]
            }
            VariantData::Unit(_, _) => vec![TopLevelItem::Error("Struct".to_string())],
        },
        ItemKind::Union(_, _) => vec![TopLevelItem::Error("Union".to_string())],
        ItemKind::Trait(_, _, _, _, items) => {
            vec![TopLevelItem::Trait {
                name: item.ident.name.to_string(),
                body: items
                    .iter()
                    .map(|item| {
                        let item = tcx.hir().trait_item(item.id);
                        let body = match &item.kind {
                            TraitItemKind::Const(ty, _) => TraitItem::Definition {
                                ty: compile_type(&tcx, ty),
                            },
                            TraitItemKind::Fn(fn_sig, _) => TraitItem::Definition {
                                ty: compile_fn_decl(&tcx, fn_sig.decl),
                            },
                            TraitItemKind::Type(_, _) => TraitItem::Type,
                        };
                        (item.ident.name.to_string(), body)
                    })
                    .collect(),
            }]
        }
        ItemKind::TraitAlias(_, _) => {
            vec![TopLevelItem::Error("TraitAlias".to_string())]
        }
        ItemKind::Impl(Impl {
            items,
            self_ty,
            of_trait,
            ..
        }) => {
            let items = items
                .iter()
                .flat_map(|item| {
                    let item = tcx.hir().impl_item(item.id);
                    match &item.kind {
                        ImplItemKind::Const(_, body_id) => {
                            let expr = tcx.hir().body(*body_id).value;
                            vec![TopLevelItem::Definition {
                                name: item.ident.name.to_string(),
                                args: vec![],
                                ret_ty: None,
                                body: compile_expr(tcx, expr),
                            }]
                        }
                        ImplItemKind::Fn(
                            rustc_hir::FnSig {
                                decl: rustc_hir::FnDecl { inputs, output, .. },
                                ..
                            },
                            body_id,
                        ) => {
                            let arg_names = tcx.hir().body(*body_id).params.iter().map(|param| {
                                match param.pat.kind {
                                    PatKind::Binding(_, _, ident, _) => ident.name.to_string(),
                                    _ => "Pattern".to_string(),
                                }
                            });
                            let arg_tys = inputs.iter().map(|ty| compile_type(&tcx, ty));
                            let ret_ty = compile_fn_ret_ty(&tcx, output);
                            let expr = tcx.hir().body(*body_id).value;
                            vec![TopLevelItem::Definition {
                                name: item.ident.name.to_string(),
                                args: arg_names.zip(arg_tys).collect(),
                                ret_ty,
                                body: compile_expr(tcx, expr),
                            }]
                        }
                        ImplItemKind::Type(ty) => vec![TopLevelItem::TypeAlias {
                            name: item.ident.name.to_string(),
                            ty: Box::new(compile_type(&tcx, ty)),
                        }],
                    }
                })
                .collect();
            let self_ty = compile_type(&tcx, self_ty);
            match of_trait {
                Some(trait_ref) => vec![TopLevelItem::TraitImpl {
                    self_ty,
                    of_trait: compile_path(trait_ref.path),
                    body: TopLevel(items),
                }],
                None => vec![TopLevelItem::Impl {
                    self_ty,
                    body: TopLevel(items),
                }],
            }
        }
    }
}

pub fn compile_top_level(tcx: TyCtxt) -> TopLevel {
    TopLevel(
        tcx.hir()
            .items()
            .flat_map(|item_id| {
                let item = tcx.hir().item(item_id);
                compile_top_level_item(tcx, item)
            })
            .collect(),
    )
}

impl TraitItem {
    fn to_doc(&self) -> RcDoc {
        match self {
            TraitItem::Definition { ty } => ty.to_doc(),
            TraitItem::Type => RcDoc::text("Set"),
        }
    }
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
                    RcDoc::line(),
                    RcDoc::text(name),
                    RcDoc::line(),
                    if args.is_empty() {
                        RcDoc::text("(_ : unit)")
                    } else {
                        RcDoc::intersperse(
                            args.iter().map(|(name, ty)| {
                                RcDoc::concat([indent(
                                    RcDoc::concat([
                                        RcDoc::text("("),
                                        RcDoc::text(name),
                                        RcDoc::line(),
                                        RcDoc::text(":"),
                                        RcDoc::line(),
                                        ty.to_doc(),
                                        RcDoc::text(")"),
                                    ])
                                    .group(),
                                )])
                            }),
                            RcDoc::line(),
                        )
                    },
                    RcDoc::line(),
                    indent(RcDoc::concat([
                        match ret_ty {
                            Some(ty) => RcDoc::concat([
                                RcDoc::text(":"),
                                RcDoc::line(),
                                ty.to_doc(),
                                RcDoc::line(),
                            ]),
                            None => RcDoc::nil(),
                        },
                        RcDoc::text(":="),
                    ]))
                    .group(),
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
            ])),
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
            TopLevelItem::TypeRecord { name, fields } => {
                let fields = fields.iter().map(|(name, ty)| {
                    RcDoc::concat([
                        RcDoc::hardline(),
                        indent(RcDoc::concat([
                            RcDoc::text(name),
                            RcDoc::line(),
                            RcDoc::text(":"),
                            RcDoc::line(),
                            ty.to_doc(),
                            RcDoc::text(";"),
                        ]))
                        .group(),
                    ])
                });
                RcDoc::concat([
                    indent(RcDoc::concat([
                        RcDoc::text("Module"),
                        RcDoc::line(),
                        RcDoc::text(name),
                        RcDoc::text("."),
                    ]))
                    .group(),
                    indent(RcDoc::concat([
                        RcDoc::hardline(),
                        indent(RcDoc::concat([
                            RcDoc::text("Record"),
                            RcDoc::line(),
                            RcDoc::text("t"),
                            RcDoc::line(),
                            indent(RcDoc::concat([
                                RcDoc::text(":"),
                                RcDoc::line(),
                                RcDoc::text("Set"),
                                RcDoc::line(),
                                RcDoc::text(":="),
                                RcDoc::line(),
                                RcDoc::text("{"),
                            ]))
                            .group(),
                        ]))
                        .group(),
                        indent(RcDoc::concat([RcDoc::intersperse(fields, RcDoc::nil())])),
                        RcDoc::hardline(),
                        RcDoc::text("}."),
                    ])),
                    RcDoc::hardline(),
                    indent(RcDoc::concat([
                        RcDoc::text("End"),
                        RcDoc::line(),
                        RcDoc::text(name),
                        RcDoc::text("."),
                    ]))
                    .group(),
                    RcDoc::hardline(),
                    indent(RcDoc::concat([
                        RcDoc::text("Definition"),
                        RcDoc::line(),
                        RcDoc::text(name),
                        RcDoc::line(),
                        RcDoc::text(":"),
                        RcDoc::line(),
                        RcDoc::text("Set"),
                        RcDoc::line(),
                        RcDoc::text(":="),
                        RcDoc::line(),
                        RcDoc::text(name),
                        RcDoc::text("."),
                        RcDoc::text("t"),
                        RcDoc::text("."),
                    ]))
                    .group(),
                ])
            }
            TopLevelItem::Impl { self_ty, body } => RcDoc::concat([
                RcDoc::text("(* Impl ["),
                self_ty.to_doc(),
                RcDoc::text("] "),
                RcDoc::text("*)"),
                RcDoc::hardline(),
                indent(RcDoc::concat([
                    RcDoc::text("Module"),
                    RcDoc::line(),
                    RcDoc::text("Impl"),
                    self_ty.to_doc(),
                    RcDoc::text("."),
                ]))
                .group(),
                indent(RcDoc::concat([RcDoc::hardline(), body.to_doc()])),
                RcDoc::hardline(),
                indent(RcDoc::concat([
                    RcDoc::text("End"),
                    RcDoc::line(),
                    RcDoc::text("Impl"),
                    self_ty.to_doc(),
                    RcDoc::text("."),
                ]))
                .group(),
                RcDoc::hardline(),
                RcDoc::text("(* End impl ["),
                self_ty.to_doc(),
                RcDoc::text("] *)"),
            ]),
            TopLevelItem::Trait { name, body } => RcDoc::concat([
                indent(RcDoc::concat([
                    RcDoc::concat([
                        RcDoc::text("Class"),
                        RcDoc::line(),
                        RcDoc::text(name),
                        RcDoc::line(),
                        RcDoc::text(":"),
                        RcDoc::line(),
                        RcDoc::text("Set"),
                        RcDoc::line(),
                        RcDoc::text(":="),
                        RcDoc::line(),
                        RcDoc::text("{"),
                    ])
                    .group(),
                    RcDoc::concat(body.iter().map(|(name, item)| {
                        RcDoc::concat([
                            RcDoc::hardline(),
                            indent(RcDoc::concat([
                                RcDoc::text(name),
                                RcDoc::line(),
                                RcDoc::text(":"),
                                RcDoc::line(),
                                item.to_doc(),
                                RcDoc::text(";"),
                            ]))
                            .group(),
                        ])
                    })),
                ])),
                RcDoc::hardline(),
                RcDoc::text("}."),
            ]),
            TopLevelItem::TraitImpl {
                self_ty,
                of_trait,
                body,
            } => RcDoc::concat([
                indent(RcDoc::concat([
                    indent(RcDoc::concat([
                        RcDoc::text("Module"),
                        RcDoc::line(),
                        RcDoc::text("Impl_"),
                        RcDoc::text(of_trait.to_name()),
                        RcDoc::text("_for_"),
                        RcDoc::text(self_ty.to_name()),
                        RcDoc::text("."),
                    ]))
                    .group(),
                    RcDoc::hardline(),
                    indent(RcDoc::concat([
                        RcDoc::text("Definition"),
                        RcDoc::line(),
                        RcDoc::text("Self"),
                        RcDoc::line(),
                        RcDoc::text(":="),
                        RcDoc::line(),
                        self_ty.to_doc(),
                        RcDoc::text("."),
                    ]))
                    .group(),
                    RcDoc::hardline(),
                    RcDoc::hardline(),
                    indent(RcDoc::concat([
                        indent(RcDoc::concat([
                            indent(RcDoc::concat([
                                RcDoc::text("#[global]"),
                                RcDoc::line(),
                                RcDoc::text("Instance"),
                                RcDoc::line(),
                                RcDoc::text("I"),
                            ]))
                            .group(),
                            RcDoc::line(),
                            indent(RcDoc::concat([
                                RcDoc::text(":"),
                                RcDoc::line(),
                                of_trait.to_doc(),
                                RcDoc::text(".Class"),
                                RcDoc::line(),
                                RcDoc::text("Self"),
                                RcDoc::line(),
                                RcDoc::text(":="),
                                RcDoc::line(),
                                RcDoc::text("{|"),
                            ]))
                            .group(),
                        ]))
                        .group(),
                        RcDoc::concat(body.0.iter().map(|item| {
                            match item {
                                TopLevelItem::Definition {
                                    name,
                                    args,
                                    ret_ty,
                                    body,
                                } => RcDoc::concat([
                                    RcDoc::hardline(),
                                    indent(RcDoc::concat([
                                        RcDoc::text(name),
                                        RcDoc::line(),
                                        RcDoc::intersperse(
                                            args.iter().map(|(name, ty)| {
                                                indent(RcDoc::concat([
                                                    RcDoc::text("("),
                                                    RcDoc::text(name),
                                                    RcDoc::line(),
                                                    RcDoc::text(":"),
                                                    RcDoc::line(),
                                                    ty.to_doc(),
                                                    RcDoc::text(")"),
                                                ]))
                                                .group()
                                            }),
                                            RcDoc::line(),
                                        ),
                                        RcDoc::line(),
                                        match ret_ty {
                                            Some(ty) => RcDoc::concat([indent(RcDoc::concat([
                                                RcDoc::text(":"),
                                                RcDoc::line(),
                                                ty.to_doc(),
                                                RcDoc::line(),
                                                RcDoc::text(":="),
                                            ]))
                                            .group()]),
                                            None => RcDoc::text(":="),
                                        },
                                        RcDoc::line(),
                                        body.to_doc(false),
                                        RcDoc::text(";"),
                                    ]))
                                    .group(),
                                ]),
                                TopLevelItem::TypeAlias { name, ty } => RcDoc::concat([
                                    RcDoc::hardline(),
                                    indent(RcDoc::concat([
                                        RcDoc::text(name),
                                        RcDoc::line(),
                                        RcDoc::text(":="),
                                        RcDoc::line(),
                                        ty.to_doc(),
                                        RcDoc::text(";"),
                                    ]))
                                    .group(),
                                ]),
                                _ => todo!("trait impl item"),
                            }
                        })),
                    ]))
                    .group(),
                    RcDoc::hardline(),
                    RcDoc::text("|}."),
                ]))
                .group(),
                RcDoc::hardline(),
                indent(RcDoc::concat([
                    RcDoc::text("Module"),
                    RcDoc::line(),
                    RcDoc::text("Impl"),
                    RcDoc::text(self_ty.to_name()),
                    RcDoc::text("."),
                ]))
                .group(),
            ]),
            TopLevelItem::Error(message) => RcDoc::concat([
                RcDoc::text("Error"),
                RcDoc::space(),
                RcDoc::text(message),
                RcDoc::text("."),
            ]),
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
        format!("{}{}\n", HEADER, String::from_utf8(w).unwrap())
    }
}
