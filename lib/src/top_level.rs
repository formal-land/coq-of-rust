use crate::expression::*;
use crate::header::*;
use crate::path::*;
use crate::render::*;
use crate::ty::*;

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
    TypeStructStruct {
        name: String,
        fields: Vec<(String, CoqType)>,
    },
    TypeStructTuple {
        name: String,
        fields: Vec<CoqType>,
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
        ty_params: Vec<String>,
        body: Vec<(String, TraitItem)>,
    },
    TraitImpl {
        ty_params: Vec<CoqType>,
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
                vec![TopLevelItem::TypeStructStruct {
                    name: item.ident.name.to_string(),
                    fields,
                }]
            }
            VariantData::Tuple(fields, _, _) => {
                vec![TopLevelItem::TypeStructTuple {
                    name: item.ident.name.to_string(),
                    fields: fields
                        .iter()
                        .map(|field| compile_type(&tcx, field.ty))
                        .collect(),
                }]
            }
            VariantData::Unit(_, _) => vec![TopLevelItem::Error("StructUnit".to_string())],
        },
        ItemKind::Union(_, _) => vec![TopLevelItem::Error("Union".to_string())],
        ItemKind::Trait(_, _, generics, _, items) => {
            vec![TopLevelItem::Trait {
                name: item.ident.name.to_string(),
                ty_params: generics
                    .params
                    .iter()
                    .map(|param| param.name.ident().to_string())
                    .collect(),
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
                    ty_params: compile_path_ty_params(&tcx, trait_ref.path),
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
    fn to_doc(&self) -> Doc {
        match self {
            TraitItem::Definition { ty } => ty.to_doc(false),
            TraitItem::Type => text("Set"),
        }
    }
}

impl TopLevelItem {
    fn to_doc(&self) -> Doc {
        match self {
            TopLevelItem::Definition {
                name,
                args,
                ret_ty,
                body,
            } => nest([
                nest([
                    nest([text("Definition"), line(), text(name)]),
                    line(),
                    if args.is_empty() {
                        text("(_ : unit)")
                    } else {
                        intersperse(
                            args.iter().map(|(name, ty)| {
                                nest([
                                    text("("),
                                    text(name),
                                    line(),
                                    text(":"),
                                    line(),
                                    ty.to_doc(false),
                                    text(")"),
                                ])
                            }),
                            [line()],
                        )
                    },
                    match ret_ty {
                        Some(_) => line(),
                        None => nil(),
                    },
                    match ret_ty {
                        Some(ty) => nest([text(":"), line(), ty.to_doc(false), text(" :=")]),
                        None => text(" :="),
                    },
                ]),
                line(),
                body.to_doc(false),
                text("."),
            ]),
            TopLevelItem::Module { name, body } => nest([
                text("Module"),
                line(),
                text(name),
                line(),
                text(":="),
                hardline(),
                body.to_doc(),
                text("."),
            ]),
            TopLevelItem::TypeAlias { name, ty } => nest([
                nest([
                    text("Definition"),
                    line(),
                    text(name),
                    line(),
                    text(":"),
                    line(),
                    text("Set"),
                    line(),
                    text(":="),
                ]),
                line(),
                ty.to_doc(false),
                text("."),
            ]),
            TopLevelItem::TypeStructStruct { name, fields } => {
                let fields = fields.iter().map(|(name, ty)| {
                    group([
                        hardline(),
                        nest([
                            text(name),
                            line(),
                            text(":"),
                            line(),
                            ty.to_doc(false),
                            text(";"),
                        ]),
                    ])
                });
                group([
                    nest([text("Module"), line(), text(name), text(".")]),
                    nest([
                        hardline(),
                        nest([
                            text("Record"),
                            line(),
                            text("t"),
                            line(),
                            nest([
                                text(":"),
                                line(),
                                text("Set"),
                                line(),
                                text(":="),
                                line(),
                                text("{"),
                            ]),
                        ]),
                        nest(fields),
                        hardline(),
                        text("}."),
                    ]),
                    hardline(),
                    nest([text("End"), line(), text(name), text(".")]),
                    hardline(),
                    nest([
                        text("Definition"),
                        line(),
                        text(name),
                        line(),
                        text(":"),
                        line(),
                        text("Set"),
                        line(),
                        text(":="),
                        line(),
                        text(name),
                        text("."),
                        text("t"),
                        text("."),
                    ]),
                ])
            }
            TopLevelItem::TypeStructTuple { name, fields } => group([
                nest([text("Module"), line(), text(name), text(".")]),
                nest([
                    hardline(),
                    nest([
                        nest([
                            text("Inductive"),
                            line(),
                            text("t"),
                            line(),
                            nest([text(":"), line(), text("Set"), text(" :=")]),
                        ]),
                        line(),
                        nest([
                            text("Build"),
                            line(),
                            intersperse(
                                fields.iter().map(|ty| {
                                    nest([text("(_ :"), line(), ty.to_doc(false), text(")")])
                                }),
                                [line()],
                            ),
                        ]),
                        text("."),
                    ]),
                    hardline(),
                    intersperse(
                        fields.iter().enumerate().map(|(i, ty)| {
                            group([
                                hardline(),
                                nest([
                                    nest([
                                        nest([
                                            text("Global"),
                                            line(),
                                            text("Instance"),
                                            line(),
                                            text(format!("Get_{i}")),
                                            text(" :"),
                                        ]),
                                        line(),
                                        nest([
                                            text("IndexedField.Class"),
                                            line(),
                                            text("t"),
                                            line(),
                                            text(i.to_string()),
                                            line(),
                                            ty.to_doc(false),
                                            text(" := {|"),
                                        ]),
                                    ]),
                                    hardline(),
                                    nest([
                                        text("IndexedField.get"),
                                        line(),
                                        nest([
                                            text("'(Build"),
                                            line(),
                                            intersperse(
                                                (0..fields.len()).map(|j| {
                                                    if i == j {
                                                        text(format!("x{j}"))
                                                    } else {
                                                        text("_")
                                                    }
                                                }),
                                                [line()],
                                            ),
                                            text(")"),
                                        ]),
                                        line(),
                                        text(":="),
                                        line(),
                                        text(format!("x{i}")),
                                        text(";"),
                                    ]),
                                ]),
                                hardline(),
                                text("|}."),
                            ])
                        }),
                        [nil()],
                    ),
                ]),
                hardline(),
                nest([text("End"), line(), text(name), text(".")]),
                hardline(),
                nest([
                    text("Definition"),
                    line(),
                    text(name),
                    line(),
                    text(":="),
                    line(),
                    text(name),
                    text(".t."),
                ]),
            ]),
            TopLevelItem::Impl { self_ty, body } => group([
                text("(* Impl ["),
                self_ty.to_doc(false),
                text("] "),
                text("*)"),
                hardline(),
                nest([
                    text("Module"),
                    line(),
                    text("Impl"),
                    self_ty.to_doc(false),
                    text("."),
                ]),
                nest([hardline(), body.to_doc()]),
                hardline(),
                nest([
                    text("End"),
                    line(),
                    text("Impl"),
                    self_ty.to_doc(false),
                    text("."),
                ]),
                hardline(),
                text("(* End impl ["),
                self_ty.to_doc(false),
                text("] *)"),
            ]),
            TopLevelItem::Trait {
                name,
                ty_params,
                body,
            } => group([
                nest([text("Module"), line(), text(name), text(".")]),
                nest([
                    hardline(),
                    if body.is_empty() {
                        group([text("Unset Primitive Projections."), hardline()])
                    } else {
                        nil()
                    },
                    nest([
                        nest([
                            text("Class"),
                            line(),
                            text("Class"),
                            line(),
                            nest([
                                text("("),
                                concat(ty_params.iter().map(|ty| concat([text(ty), line()]))),
                                text("Self"),
                                line(),
                                text(":"),
                                line(),
                                text("Set"),
                                text(")"),
                            ]),
                            line(),
                            text(":"),
                            line(),
                            text("Set"),
                            line(),
                            text(":="),
                            line(),
                            text("{"),
                        ]),
                        intersperse(
                            body.iter().map(|(name, item)| {
                                group([
                                    hardline(),
                                    nest([
                                        text(name),
                                        line(),
                                        text(":"),
                                        line(),
                                        item.to_doc(),
                                        text(";"),
                                    ]),
                                ])
                            }),
                            [nil()],
                        ),
                    ]),
                    hardline(),
                    text("}."),
                    if body.is_empty() {
                        group([hardline(), text("Global Set Primitive Projections.")])
                    } else {
                        hardline()
                    },
                    concat(body.iter().map(|(name, item)| {
                        concat([
                            hardline(),
                            nest([
                                nest([
                                    text("Global Instance"),
                                    line(),
                                    text(format!("Method_{name}")),
                                    line(),
                                    nest([
                                        text("{"),
                                        concat(
                                            ty_params.iter().map(|ty| concat([text(ty), line()])),
                                        ),
                                        text("Self"),
                                        line(),
                                        text(": Set}"),
                                    ]),
                                    line(),
                                    nest([
                                        text("`{Class"),
                                        line(),
                                        concat(
                                            ty_params.iter().map(|ty| concat([text(ty), line()])),
                                        ),
                                        text("Self}"),
                                    ]),
                                ]),
                                line(),
                                nest([
                                    text(": Method"),
                                    line(),
                                    text(format!("\"{name}\"")),
                                    line(),
                                    text("_"),
                                    line(),
                                    text(":= {|"),
                                ]),
                            ]),
                            nest([
                                hardline(),
                                nest([
                                    text("method"),
                                    line(),
                                    text(":="),
                                    line(),
                                    text(name),
                                    text(";"),
                                ]),
                            ]),
                            hardline(),
                            text("|}."),
                        ])
                    })),
                ]),
                hardline(),
                nest([text("End"), line(), text(name), text(".")]),
            ]),
            TopLevelItem::TraitImpl {
                ty_params,
                self_ty,
                of_trait,
                body,
            } => group([
                nest([
                    nest([
                        text("Module"),
                        line(),
                        text("Impl_"),
                        text(of_trait.to_name()),
                        text("_for_"),
                        text(self_ty.to_name()),
                        text("."),
                    ]),
                    hardline(),
                    nest([
                        text("Definition"),
                        line(),
                        text("Self"),
                        line(),
                        text(":="),
                        line(),
                        self_ty.to_doc(false),
                        text("."),
                    ]),
                    hardline(),
                    hardline(),
                    nest([
                        nest([
                            nest([
                                nest([text("Global"), line(), text("Instance"), line(), text("I")]),
                                line(),
                                text(":"),
                                line(),
                                of_trait.to_doc(),
                                text(".Class"),
                                concat(
                                    ty_params
                                        .iter()
                                        .map(|ty_param| concat([line(), ty_param.to_doc(false)])),
                                ),
                                line(),
                                text("Self"),
                            ]),
                            text(" :="),
                            line(),
                            if body.0.is_empty() {
                                nest([of_trait.to_doc(), text(".Build_Class"), line(), text("_")])
                            } else {
                                text("{|")
                            },
                        ]),
                        group(body.0.iter().map(|item| match item {
                            TopLevelItem::Definition {
                                name,
                                args,
                                ret_ty: _,
                                body,
                            } => group([
                                hardline(),
                                nest([
                                    nest([
                                        of_trait.to_doc(),
                                        text("."),
                                        text(name),
                                        line(),
                                        intersperse(
                                            args.iter().map(|(name, ty)| {
                                                nest([
                                                    text("("),
                                                    text(name),
                                                    line(),
                                                    text(":"),
                                                    line(),
                                                    ty.to_doc(false),
                                                    text(")"),
                                                ])
                                                .group()
                                            }),
                                            [line()],
                                        ),
                                        text(" :="),
                                    ]),
                                    line(),
                                    body.to_doc(false),
                                    text(";"),
                                ]),
                            ]),
                            TopLevelItem::TypeAlias { name, ty } => group([
                                hardline(),
                                nest([
                                    of_trait.to_doc(),
                                    text("."),
                                    text(name),
                                    text(" :="),
                                    line(),
                                    ty.to_doc(false),
                                    text(";"),
                                ]),
                            ]),
                            _ => todo!("trait impl item"),
                        })),
                    ]),
                    if body.0.is_empty() {
                        text(".")
                    } else {
                        group([hardline(), text("|}.")])
                    },
                ]),
                hardline(),
                nest([
                    text("Module"),
                    line(),
                    text("Impl"),
                    text(self_ty.to_name()),
                    text("."),
                ]),
            ]),
            TopLevelItem::Error(message) => nest([text("Error"), line(), text(message), text(".")]),
        }
    }
}

impl TopLevel {
    fn to_doc(&self) -> Doc {
        intersperse(
            self.0.iter().map(|item| item.to_doc()),
            [hardline(), hardline()],
        )
    }

    pub fn to_pretty(&self, width: usize) -> String {
        let mut w = Vec::new();
        self.to_doc().render(width, &mut w).unwrap();
        format!("{}{}\n", HEADER, String::from_utf8(w).unwrap())
    }
}
