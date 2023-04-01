use std::collections::HashMap;

use crate::expression::*;
use crate::header::*;
use crate::path::*;
use crate::render::*;
use crate::ty::*;

use rustc_hir::{Impl, ImplItemKind, Item, ItemKind, PatKind, TraitFn, TraitItemKind, VariantData};
use rustc_middle::ty::TyCtxt;

#[derive(Debug)]
enum TraitItem {
    Definition {
        ty: CoqType,
    },
    DefinitionWithDefault {
        args: Vec<(String, CoqType)>,
        ret_ty: Option<CoqType>,
        body: Box<Expr>,
    },
    Type,
}

#[derive(Debug)]
enum ImplItem {
    Definition {
        args: Vec<(String, CoqType)>,
        ret_ty: Option<CoqType>,
        body: Box<Expr>,
        is_method: bool,
    },
    Type {
        ty: Box<CoqType>,
    },
}

#[derive(Debug)]
struct WherePredicate {
    name: Path,
    ty_params: Vec<CoqType>,
    ty: CoqType,
}

/// Representation of top-level hir [Item]s in coq-of-rust
/// See https://doc.rust-lang.org/reference/items.html
#[derive(Debug)]
enum TopLevelItem {
    Definition {
        name: String,
        ty_params: Vec<String>,
        where_predicates: Vec<WherePredicate>,
        args: Vec<(String, CoqType)>,
        ret_ty: Option<CoqType>,
        body: Box<Expr>,
    },
    TypeAlias {
        name: String,
        ty: Box<CoqType>,
    },
    TypeEnum {
        name: String,
        variants: Vec<(String, Vec<CoqType>)>,
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
        /// We use a counter to disambiguate several impls for the same type
        counter: u64,
        items: Vec<(String, ImplItem)>,
    },
    Trait {
        name: String,
        ty_params: Vec<String>,
        body: Vec<(String, TraitItem)>,
    },
    TraitImpl {
        generic_tys: Vec<String>,
        ty_params: Vec<CoqType>,
        self_ty: CoqType,
        of_trait: Path,
        items: Vec<(String, ImplItem)>,
        trait_non_default_items: Vec<String>,
    },
    Use {
        name: String,
        path: Path,
        is_glob: bool,
        is_type: bool,
    },
    Error(String),
}

#[derive(Debug)]
pub struct TopLevel(Vec<TopLevelItem>);

struct FnSigAndBody {
    args: Vec<(String, CoqType)>,
    ret_ty: Option<CoqType>,
    body: Box<Expr>,
}

fn compile_fn_sig_and_body_id(
    tcx: TyCtxt,
    fn_sig: &rustc_hir::FnSig<'_>,
    body_id: &rustc_hir::BodyId,
) -> FnSigAndBody {
    let body = tcx.hir().body(*body_id);
    let expr = body.value;
    FnSigAndBody {
        args: body
            .params
            .iter()
            .zip(fn_sig.decl.inputs.iter())
            .map(|(param, ty)| {
                let name = match &param.pat.kind {
                    PatKind::Binding(_, _, ident, _) => ident.name.to_string(),
                    _ => "arg".to_string(),
                };
                (name, compile_type(&tcx, ty))
            })
            .collect(),
        ret_ty: match fn_sig.decl.output {
            rustc_hir::FnRetTy::DefaultReturn(_) => Some(CoqType::unit()),
            rustc_hir::FnRetTy::Return(ty) => Some(compile_type(&tcx, ty)),
        },
        body: Box::new(compile_expr(tcx, expr)),
    }
}

/// [compile_top_level_item] compiles hir [Item]s into coq-of-rust (optional)
/// items.
/// - See https://doc.rust-lang.org/stable/nightly-rustc/rustc_hir/struct.Item.html
///   and the doc for [TopLevelItem]
/// - [rustc_middle::hir::map::Map] is intuitively the type for hir environments
/// - Method [body] allows retrievient the body of an identifier [body_id] in an
///   hir environment [hir]
fn compile_top_level_item(
    tcx: TyCtxt,
    impl_counter: &mut HashMap<CoqType, u64>,
    item: &Item,
) -> Vec<TopLevelItem> {
    match &item.kind {
        ItemKind::ExternCrate(_) => vec![],
        ItemKind::Use(path, use_kind) => {
            if matches!(use_kind, rustc_hir::UseKind::ListStem) {
                vec![]
            } else {
                vec![TopLevelItem::Use {
                    name: item.ident.name.to_string(),
                    path: compile_path(path),
                    is_glob: matches!(use_kind, rustc_hir::UseKind::Glob),
                    is_type: path.res.iter().any(|res| match res {
                        rustc_hir::def::Res::Def(def, _) => matches!(
                            def,
                            rustc_hir::def::DefKind::TyAlias
                                | rustc_hir::def::DefKind::Enum
                                | rustc_hir::def::DefKind::Struct
                                | rustc_hir::def::DefKind::Union
                        ),
                        _ => false,
                    }),
                }]
            }
        }
        ItemKind::Static(_, _, body_id) => {
            let expr = tcx.hir().body(*body_id).value;
            vec![TopLevelItem::Definition {
                name: item.ident.name.to_string(),
                ty_params: vec![],
                where_predicates: vec![],
                args: vec![],
                ret_ty: None,
                body: Box::new(compile_expr(tcx, expr)),
            }]
        }
        ItemKind::Const(_, body_id) => {
            let expr = tcx.hir().body(*body_id).value;
            vec![TopLevelItem::Definition {
                name: item.ident.name.to_string(),
                ty_params: vec![],
                where_predicates: vec![],
                args: vec![],
                ret_ty: None,
                body: Box::new(compile_expr(tcx, expr)),
            }]
        }
        ItemKind::Fn(fn_sig, generics, body_id) => {
            let FnSigAndBody { args, ret_ty, body } =
                compile_fn_sig_and_body_id(tcx, fn_sig, body_id);
            vec![TopLevelItem::Definition {
                name: item.ident.name.to_string(),
                ty_params: generics
                    .params
                    .iter()
                    .filter_map(|param| match param.kind {
                        rustc_hir::GenericParamKind::Type { .. } => {
                            Some(param.name.ident().to_string())
                        }
                        _ => None,
                    })
                    .collect(),
                where_predicates: generics
                    .predicates
                    .iter()
                    .flat_map(|predicate| match predicate {
                        rustc_hir::WherePredicate::BoundPredicate(predicate) => {
                            let names_and_ty_params =
                                predicate.bounds.iter().filter_map(|bound| match bound {
                                    rustc_hir::GenericBound::Trait(ref trait_ref, _) => {
                                        let path = trait_ref.trait_ref.path;
                                        Some((
                                            compile_path(path),
                                            compile_path_ty_params(&tcx, path),
                                        ))
                                    }
                                    _ => None,
                                });
                            names_and_ty_params
                                .map(|(name, ty_params)| WherePredicate {
                                    name,
                                    ty_params,
                                    ty: compile_type(&tcx, predicate.bounded_ty),
                                })
                                .collect()
                        }
                        _ => vec![],
                    })
                    .collect(),
                args,
                ret_ty,
                body,
            }]
        }
        ItemKind::Macro(_, _) => vec![],
        ItemKind::Mod(module) => {
            let items = module
                .item_ids
                .iter()
                .flat_map(|item_id| {
                    let item = tcx.hir().item(*item_id);
                    compile_top_level_item(tcx, impl_counter, item)
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
        ItemKind::TyAlias(ty, _) => vec![TopLevelItem::TypeAlias {
            name: item.ident.name.to_string(),
            ty: Box::new(compile_type(&tcx, ty)),
        }],
        ItemKind::OpaqueTy(_) => vec![TopLevelItem::Error("OpaqueTy".to_string())],
        ItemKind::Enum(enum_def, _) => vec![TopLevelItem::TypeEnum {
            name: item.ident.name.to_string(),
            variants: enum_def
                .variants
                .iter()
                .map(|variant| {
                    let name = variant.ident.name.to_string();
                    let fields = match &variant.data {
                        VariantData::Struct(fields, _) => fields
                            .iter()
                            .map(|field| compile_type(&tcx, field.ty))
                            .collect(),
                        VariantData::Tuple(fields, _, _) => fields
                            .iter()
                            .map(|field| compile_type(&tcx, field.ty))
                            .collect(),
                        VariantData::Unit(_, _) => vec![],
                    };
                    (name, fields)
                })
                .collect(),
        }],
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
                            TraitItemKind::Fn(fn_sig, trait_fn) => match trait_fn {
                                TraitFn::Required(_) => TraitItem::Definition {
                                    ty: compile_fn_decl(&tcx, fn_sig.decl),
                                },
                                TraitFn::Provided(body_id) => {
                                    let FnSigAndBody { args, ret_ty, body } =
                                        compile_fn_sig_and_body_id(tcx, fn_sig, body_id);
                                    TraitItem::DefinitionWithDefault { args, ret_ty, body }
                                }
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
            generics,
            of_trait,
            self_ty,
            items,
            ..
        }) => {
            let generic_tys = generics
                .params
                .iter()
                .map(|param| param.name.ident().to_string())
                .collect();
            let items = items
                .iter()
                .map(|item| {
                    let is_method = match item.kind {
                        rustc_hir::AssocItemKind::Fn { has_self } => has_self,
                        _ => false,
                    };
                    let item = tcx.hir().impl_item(item.id);
                    let value = match &item.kind {
                        ImplItemKind::Const(_, body_id) => {
                            let expr = tcx.hir().body(*body_id).value;
                            ImplItem::Definition {
                                args: vec![],
                                ret_ty: None,
                                body: Box::new(compile_expr(tcx, expr)),
                                is_method,
                            }
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
                            ImplItem::Definition {
                                args: arg_names.zip(arg_tys).collect(),
                                ret_ty,
                                body: Box::new(compile_expr(tcx, expr)),
                                is_method,
                            }
                        }
                        ImplItemKind::Type(ty) => ImplItem::Type {
                            ty: Box::new(compile_type(&tcx, ty)),
                        },
                    };
                    (item.ident.name.to_string(), value)
                })
                .collect();
            let self_ty = compile_type(&tcx, self_ty);
            match of_trait {
                Some(trait_ref) => {
                    let trait_non_default_items = tcx
                        .associated_items(trait_ref.trait_def_id().unwrap())
                        .in_definition_order()
                        .filter(|item| !item.defaultness(tcx).has_value())
                        .map(|item| item.name.to_string())
                        .collect();

                    vec![TopLevelItem::TraitImpl {
                        generic_tys,
                        ty_params: compile_path_ty_params(&tcx, trait_ref.path),
                        self_ty,
                        of_trait: compile_path(trait_ref.path),
                        items,
                        trait_non_default_items,
                    }]
                }
                None => {
                    let entry = impl_counter.entry(self_ty.clone());
                    let counter = *entry.and_modify(|counter| *counter += 1).or_insert(1);

                    vec![TopLevelItem::Impl {
                        self_ty,
                        counter,
                        items,
                    }]
                }
            }
        }
    }
}

pub fn compile_top_level(tcx: TyCtxt) -> TopLevel {
    let mut impl_counter = HashMap::new();

    TopLevel(
        tcx.hir()
            .items()
            .flat_map(|item_id| {
                let item = tcx.hir().item(item_id);
                compile_top_level_item(tcx, &mut impl_counter, item)
            })
            .collect(),
    )
}

fn fn_to_doc<'a>(
    name: &'a String,
    ty_params: Option<&'a Vec<String>>,
    where_predicates: Option<&'a Vec<WherePredicate>>,
    args: &'a Vec<(String, CoqType)>,
    ret_ty: &'a Option<CoqType>,
    body: &'a Expr,
) -> Doc<'a> {
    nest([
        nest([
            nest([text("Definition"), line(), text(name)]),
            match ty_params {
                None => nil(),
                Some(ty_params) => {
                    if ty_params.is_empty() {
                        nil()
                    } else {
                        concat([
                            line(),
                            nest([
                                text("{"),
                                intersperse(ty_params.iter().map(text), [line()]),
                                line(),
                                text(": Set}"),
                            ]),
                        ])
                    }
                }
            },
            line(),
            match where_predicates {
                None => nil(),
                Some(where_predicates) => concat(where_predicates.iter().map(
                    |WherePredicate {
                         name,
                         ty_params,
                         ty,
                     }| {
                        concat([
                            nest([
                                text("`{"),
                                name.to_doc(),
                                text(".Class"),
                                line(),
                                concat(
                                    ty_params
                                        .iter()
                                        .map(|param| concat([param.to_doc(true), line()])),
                                ),
                                ty.to_doc(true),
                                text("}"),
                            ]),
                            line(),
                        ])
                    },
                )),
            },
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
    ])
}

fn associated_function_class_to_doc<'a>() -> Doc<'a> {
    concat([
        nest([
            text("Class"),
            line(),
            text("AssociatedFunction"),
            line(),
            text("(name : string)"),
            line(),
            text("(T : Set)"),
            line(),
            text(":"),
            line(),
            text("Set"),
            line(),
            text(":="),
            line(),
            text("{"),
        ]),
        nest([hardline(), text("associated_function : T;")]),
        hardline(),
        text("}."),
        hardline(),
        text("Arguments associated_function name {T AssociatedFunction}."),
    ])
}

impl ImplItem {
    fn class_instance_to_doc<'a>(
        instance_prefix: &'a str,
        name: &'a str,
        class_prefix: Option<Doc<'a>>,
        class_name: &'a str,
        method_name: &'a str,
    ) -> Doc<'a> {
        let class_prefix = match class_prefix {
            None => nil(),
            Some(class_prefix) => concat([class_prefix, text(".")]),
        };

        group([
            nest([
                text("Global Instance"),
                line(),
                text(format!("{instance_prefix}_{name}")),
                line(),
                text(":"),
                line(),
                class_prefix.clone(),
                text(class_name),
                line(),
                text(format!("\"{name}\"")),
                line(),
                text("_"),
                line(),
                text(":="),
                line(),
                text("{|"),
            ]),
            nest([
                hardline(),
                nest([
                    class_prefix,
                    text(method_name),
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
    }

    fn to_doc<'a>(
        &'a self,
        self_ty: &'a CoqType,
        trait_path: Option<&'a Path>,
        name: &'a String,
    ) -> Doc<'a> {
        match self {
            ImplItem::Definition {
                args,
                ret_ty,
                body,
                is_method,
            } => concat([
                fn_to_doc(name, None, None, args, ret_ty, body),
                hardline(),
                hardline(),
                if *is_method {
                    concat([
                        Self::class_instance_to_doc("M", name, None, "Method", "method"),
                        hardline(),
                    ])
                } else {
                    nil()
                },
                Self::class_instance_to_doc(
                    "AF",
                    name,
                    Some(self_ty.to_path_doc()),
                    "AssociatedFunction",
                    "associated_function",
                ),
                match trait_path {
                    None => nil(),
                    Some(trait_path) => concat([
                        hardline(),
                        Self::class_instance_to_doc(
                            "AFT",
                            name,
                            Some(trait_path.to_doc()),
                            "AssociatedFunction",
                            "associated_function",
                        ),
                    ]),
                },
            ]),
            ImplItem::Type { ty } => nest([
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
        }
    }
}

impl TopLevelItem {
    fn to_doc(&self) -> Doc {
        match self {
            TopLevelItem::Definition {
                name,
                ty_params,
                where_predicates,
                args,
                ret_ty,
                body,
            } => fn_to_doc(
                name,
                Some(ty_params),
                Some(where_predicates),
                args,
                ret_ty,
                body,
            ),
            TopLevelItem::Module { name, body } => group([
                nest([text("Module"), line(), text(name), text(".")]),
                nest([hardline(), body.to_doc()]),
                hardline(),
                nest([text("End"), line(), text(name), text(".")]),
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
            TopLevelItem::TypeEnum { name, variants } => group([
                nest([text("Module"), line(), text(name), text(".")]),
                nest([
                    hardline(),
                    nest([
                        text("Inductive"),
                        line(),
                        text("t"),
                        line(),
                        text(":"),
                        line(),
                        text("Set"),
                        line(),
                        text(":="),
                    ]),
                    hardline(),
                    intersperse(
                        variants.iter().map(|(name, tys)| {
                            nest([
                                text("|"),
                                line(),
                                text(name),
                                concat(tys.iter().map(|ty| {
                                    concat([
                                        line(),
                                        nest([
                                            text("(_"),
                                            line(),
                                            text(":"),
                                            line(),
                                            ty.to_doc(false),
                                            text(")"),
                                        ]),
                                    ])
                                })),
                            ])
                        }),
                        [line()],
                    ),
                    text("."),
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
            TopLevelItem::TypeStructStruct { name, fields } => group([
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
                    nest(fields.iter().map(|(name, ty)| {
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
                    })),
                    hardline(),
                    text("}."),
                    if !fields.is_empty() {
                        hardline()
                    } else {
                        nil()
                    },
                    concat(fields.iter().enumerate().map(|(i, (name, _))| {
                        group([
                            hardline(),
                            nest([
                                nest([
                                    nest([
                                        text("Global"),
                                        line(),
                                        text("Instance"),
                                        line(),
                                        text(format!("Get_{name}")),
                                        text(" :"),
                                    ]),
                                    line(),
                                    nest([
                                        text("NamedField.Class"),
                                        line(),
                                        text("t"),
                                        line(),
                                        text(format!("\"{name}\"")),
                                        line(),
                                        text("_"),
                                        text(" := {|"),
                                    ]),
                                ]),
                                hardline(),
                                nest([
                                    text("NamedField.get"),
                                    line(),
                                    nest([
                                        text("'(Build_t"),
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
                    })),
                    hardline(),
                    associated_function_class_to_doc(),
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
            ]),
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
                        fields.iter().enumerate().map(|(i, _)| {
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
                                            text("_"),
                                            text(" := {|"),
                                        ]),
                                    ]),
                                    if !fields.is_empty() {
                                        hardline()
                                    } else {
                                        nil()
                                    },
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
            TopLevelItem::Impl {
                self_ty,
                counter,
                items,
            } => {
                let module_name = concat([
                    text("Impl"),
                    self_ty.to_doc(false),
                    if *counter != 1 {
                        text(format!("_{counter}"))
                    } else {
                        nil()
                    },
                ]);

                group([
                    nest([text("Module"), line(), module_name.clone(), text(".")]),
                    nest([
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
                        concat(items.iter().map(|(name, item)| {
                            concat([hardline(), hardline(), item.to_doc(self_ty, None, name)])
                        })),
                    ]),
                    hardline(),
                    nest([text("End"), line(), module_name, text(".")]),
                ])
            }
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
                            body.iter().map(|(name, item)| match item {
                                TraitItem::Definition { ty } => group([
                                    hardline(),
                                    nest([
                                        text(name),
                                        line(),
                                        text(":"),
                                        line(),
                                        ty.to_doc(false),
                                        text(";"),
                                    ]),
                                ]),
                                TraitItem::DefinitionWithDefault { .. } => nil(),
                                TraitItem::Type => group([
                                    hardline(),
                                    nest([
                                        text(name),
                                        line(),
                                        text(":"),
                                        line(),
                                        text("Set"),
                                        text(";"),
                                    ]),
                                ]),
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
                                    text(format!("M_{name}")),
                                    line(),
                                    text("`(Class)"),
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
                                match item {
                                    TraitItem::Definition { .. } | TraitItem::Type => nest([
                                        text("method"),
                                        line(),
                                        text(":="),
                                        line(),
                                        text(name),
                                        text(";"),
                                    ]),
                                    TraitItem::DefinitionWithDefault { args, ret_ty, body } => {
                                        nest([
                                            nest([
                                                text("method"),
                                                if args.is_empty() {
                                                    concat([line(), text("tt")])
                                                } else {
                                                    concat(args.iter().map(|(name, ty)| {
                                                        concat([
                                                            line(),
                                                            nest([
                                                                text("("),
                                                                text(name),
                                                                line(),
                                                                text(": "),
                                                                ty.to_doc(false),
                                                                text(")"),
                                                            ]),
                                                        ])
                                                    }))
                                                },
                                                text(" :="),
                                            ]),
                                            line(),
                                            match ret_ty {
                                                Some(_) => text("("),
                                                None => nil(),
                                            },
                                            body.to_doc(false),
                                            match ret_ty {
                                                Some(ty) => concat([
                                                    line(),
                                                    nest([
                                                        text(":"),
                                                        line(),
                                                        ty.to_doc(false),
                                                        text(")"),
                                                    ]),
                                                ]),
                                                None => nil(),
                                            },
                                            text(";"),
                                        ])
                                    }
                                },
                            ]),
                            hardline(),
                            text("|}."),
                        ])
                    })),
                    hardline(),
                    associated_function_class_to_doc(),
                ]),
                hardline(),
                nest([text("End"), line(), text(name), text(".")]),
            ]),
            TopLevelItem::TraitImpl {
                generic_tys,
                ty_params,
                self_ty,
                of_trait,
                items,
                trait_non_default_items,
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
                    concat(items.iter().map(|(name, item)| {
                        concat([
                            item.to_doc(self_ty, Some(of_trait), name),
                            hardline(),
                            hardline(),
                        ])
                    })),
                    nest([
                        nest([
                            nest([text("Global"), line(), text("Instance"), line(), text("I")]),
                            line(),
                            concat(
                                generic_tys
                                    .iter()
                                    .map(|generic_ty| concat([text(generic_ty), line()])),
                            ),
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
                        if items.is_empty() {
                            nest([of_trait.to_doc(), text(".Build_Class"), line(), text("_")])
                        } else {
                            text("{|")
                        },
                    ]),
                    nest(trait_non_default_items.iter().map(|name| {
                        concat([
                            hardline(),
                            nest([
                                of_trait.to_doc(),
                                text("."),
                                text(name),
                                line(),
                                text(":="),
                                line(),
                                text(name),
                                text(";"),
                            ]),
                        ])
                    })),
                    if items.is_empty() {
                        text(".")
                    } else {
                        group([hardline(), text("|}.")])
                    },
                ]),
                hardline(),
                nest([
                    text("End"),
                    line(),
                    text("Impl_"),
                    text(of_trait.to_name()),
                    text("_for_"),
                    text(self_ty.to_name()),
                    text("."),
                ]),
            ]),
            TopLevelItem::Use {
                name,
                path,
                is_glob,
                is_type,
            } => {
                if *is_glob {
                    nest([text("Import"), line(), path.to_doc(), text(".")])
                } else {
                    group([
                        nest([
                            text("Module"),
                            line(),
                            text(name),
                            line(),
                            text(":="),
                            line(),
                            path.to_doc(),
                            text("."),
                        ]),
                        if *is_type {
                            concat([
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
                            ])
                        } else {
                            nil()
                        },
                    ])
                }
            }
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
