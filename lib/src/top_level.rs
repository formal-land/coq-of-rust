use crate::expression::*;
use crate::header::*;
use crate::path::*;
use crate::render::*;
use crate::ty::*;
use rustc_ast::ast::{AttrArgs, AttrKind};
use rustc_hir::{
    Impl, ImplItemKind, Item, ItemKind, PatKind, QPath, TraitFn, TraitItemKind, Ty, TyKind,
    VariantData,
};
use rustc_middle::ty::TyCtxt;
use rustc_span::symbol::sym;
use std::collections::HashMap;
use std::string::ToString;

#[derive(Debug)]
enum TraitItem {
    Definition {
        ty: Box<CoqType>,
    },
    DefinitionWithDefault {
        args: Vec<(String, Box<CoqType>)>,
        ret_ty: Box<CoqType>,
        body: Box<Expr>,
    },
    Type,
}

#[derive(Debug)]
enum ImplItem {
    Const {
        body: Box<Expr>,
        is_dead_code: bool,
    },
    Definition {
        args: Vec<(String, Box<CoqType>)>,
        ret_ty: Box<CoqType>,
        body: Box<Expr>,
        is_method: bool,
        is_dead_code: bool,
    },
    Type {
        ty: Box<CoqType>,
    },
}

#[derive(Debug)]
struct WherePredicate {
    name: Path,
    ty_params: Vec<Box<CoqType>>,
    ty: Box<CoqType>,
}

#[derive(Debug)]
enum VariantItem {
    Struct { fields: Vec<(String, Box<CoqType>)> },
    Tuple { tys: Vec<Box<CoqType>> },
}

/// Representation of top-level hir [Item]s in coq-of-rust
/// See https://doc.rust-lang.org/reference/items.html
#[derive(Debug)]
enum TopLevelItem {
    Const {
        name: String,
        ty: Box<CoqType>,
        value: Box<Expr>,
    },
    Definition {
        name: String,
        ty_params: Vec<String>,
        where_predicates: Vec<WherePredicate>,
        args: Vec<(String, Box<CoqType>)>,
        ret_ty: Box<CoqType>,
        body: Box<Expr>,
        is_dead_code: bool,
    },
    TypeAlias {
        name: String,
        ty: Box<CoqType>,
    },
    TypeEnum {
        name: String,
        variants: Vec<(String, VariantItem)>,
    },
    TypeStructStruct {
        name: String,
        fields: Vec<(String, Box<CoqType>)>,
        is_dead_code: bool,
    },
    TypeStructTuple {
        name: String,
        fields: Vec<Box<CoqType>>,
    },
    TypeStructUnit {
        name: String,
    },
    Module {
        name: String,
        body: TopLevel,
        is_dead_code: bool,
    },
    Impl {
        self_ty: Box<CoqType>,
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
        // The boolean is there to indicate if the type parameter has a default
        ty_params: Vec<(Box<CoqType>, bool)>,
        self_ty: Box<CoqType>,
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
    args: Vec<(String, Box<CoqType>)>,
    ret_ty: Box<CoqType>,
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
            rustc_hir::FnRetTy::DefaultReturn(_) => CoqType::unit(),
            rustc_hir::FnRetTy::Return(ty) => compile_type(&tcx, ty),
        },
        body: Box::new(compile_expr(tcx, expr)),
    }
}

/// Check if the function body is actually the main test function calling to all
/// tests in the file. If so, we do not want to compile it.
fn check_if_is_test_main_function(tcx: TyCtxt, body_id: &rustc_hir::BodyId) -> bool {
    let body = tcx.hir().body(*body_id);
    let expr = body.value;
    match expr.kind {
        rustc_hir::ExprKind::Block(block, _) => match block.expr {
            Some(expr) => match expr.kind {
                rustc_hir::ExprKind::Call(func, _) => match &func.kind {
                    rustc_hir::ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) => {
                        match path.segments {
                            [base, path] => {
                                base.ident.name.to_string() == "test"
                                    && path.ident.name.to_string() == "test_main_static"
                            }
                            _ => false,
                        }
                    }
                    _ => false,
                },
                _ => false,
            },
            None => false,
        },
        _ => false,
    }
}

/// Check if a top-level definition is actually test metadata. If so, we ignore
/// it.
fn check_if_test_declaration(ty: &Ty) -> bool {
    match &ty.kind {
        TyKind::Path(QPath::Resolved(_, path)) => match path.segments {
            [base, path] => {
                base.ident.name.to_string() == "test"
                    && path.ident.name.to_string() == "TestDescAndFn"
            }
            _ => false,
        },
        _ => false,
    }
}

// Function checks if code block is having any `allow` attributes, and if it does,
// it returns [true] if one of attributes disables "dead_code" lint.
// Returns [false] if attribute is related to something else
fn check_dead_code_lint_in_attributes(tcx: &TyCtxt, item: &Item) -> bool {
    if tcx.has_attr(item.owner_id.to_def_id(), sym::allow) {
        for attr in tcx.get_attrs(item.owner_id.to_def_id(), sym::allow) {
            if let AttrKind::Normal(value) = &attr.kind {
                if let AttrArgs::Delimited(value2) = &value.item.args {
                    let into_trees = &value2.tokens.trees();
                    let in_the_tree = into_trees.look_ahead(0);
                    match in_the_tree {
                        Some(res) => {
                            if let rustc_ast::tokenstream::TokenTree::Token(res2, _) = res {
                                if let rustc_ast::token::TokenKind::Ident(a, _) = res2.kind {
                                    // since we can have many attributes on top of each piece of code,
                                    // when we face "dead_code", we return [true] right away,
                                    // otherwise we keep looking
                                    if sym::dead_code == a {
                                        return true;
                                    }
                                }
                            }
                        }
                        _ => return false,
                    }
                }
            }
        }
    }
    false
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
                return vec![];
            }
            let is_trait_use = path.res.iter().any(|res| {
                matches!(
                    res,
                    rustc_hir::def::Res::Def(rustc_hir::def::DefKind::Trait, _)
                )
            });
            if is_trait_use {
                return vec![];
            }
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
        ItemKind::Static(ty, _, body_id) | ItemKind::Const(ty, body_id) => {
            if check_if_test_declaration(ty) {
                return vec![];
            }
            let value = tcx.hir().body(*body_id).value;
            vec![TopLevelItem::Const {
                name: item.ident.name.to_string(),
                ty: compile_type(&tcx, ty),
                value: Box::new(compile_expr(tcx, value)),
            }]
        }
        ItemKind::Fn(fn_sig, generics, body_id) => {
            if check_if_is_test_main_function(tcx, body_id) {
                return vec![];
            }
            let if_marked_as_dead_code = check_dead_code_lint_in_attributes(&tcx, item);
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
                is_dead_code: if_marked_as_dead_code,
            }]
        }
        ItemKind::Macro(_, _) => vec![],
        ItemKind::Mod(module) => {
            let if_marked_as_dead_code = check_dead_code_lint_in_attributes(&tcx, item);
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
                is_dead_code: if_marked_as_dead_code,
            }]
        }
        ItemKind::ForeignMod { .. } => {
            vec![TopLevelItem::Error("ForeignMod".to_string())]
        }
        ItemKind::GlobalAsm(_) => vec![TopLevelItem::Error("GlobalAsm".to_string())],
        ItemKind::TyAlias(ty, _) => vec![TopLevelItem::TypeAlias {
            name: item.ident.name.to_string(),
            ty: compile_type(&tcx, ty),
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
                        VariantData::Struct(fields, _) => {
                            let fields = fields
                                .iter()
                                .map(|field| {
                                    (field.ident.to_string(), compile_type(&tcx, field.ty))
                                })
                                .collect();
                            VariantItem::Struct { fields }
                        }
                        VariantData::Tuple(fields, _, _) => {
                            let tys = fields
                                .iter()
                                .map(|field| compile_type(&tcx, field.ty))
                                .collect();
                            VariantItem::Tuple { tys }
                        }
                        VariantData::Unit(_, _) => VariantItem::Tuple { tys: vec![] },
                    };
                    (name, fields)
                })
                .collect(),
        }],
        ItemKind::Struct(body, _) => {
            let if_marked_as_dead_code = check_dead_code_lint_in_attributes(&tcx, item);
            match body {
                VariantData::Struct(fields, _) => {
                    let fields = fields
                        .iter()
                        .map(|field| (field.ident.name.to_string(), compile_type(&tcx, field.ty)))
                        .collect();
                    vec![TopLevelItem::TypeStructStruct {
                        name: item.ident.name.to_string(),
                        fields,
                        is_dead_code: if_marked_as_dead_code,
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
                VariantData::Unit(_, _) => {
                    vec![TopLevelItem::TypeStructUnit {
                        name: item.ident.name.to_string(),
                    }]
                }
            }
        }
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
            let if_marked_as_dead_code = check_dead_code_lint_in_attributes(&tcx, item);
            let generic_tys: Vec<String> = generics
                .params
                .iter()
                .filter(|param| matches!(param.kind, rustc_hir::GenericParamKind::Type { .. }))
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
                            ImplItem::Const {
                                body: Box::new(compile_expr(tcx, expr)),
                                is_dead_code: if_marked_as_dead_code,
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
                                is_dead_code: if_marked_as_dead_code,
                            }
                        }
                        ImplItemKind::Type(ty) => ImplItem::Type {
                            ty: compile_type(&tcx, ty),
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
                        .filter(|item| item.kind != rustc_middle::ty::AssocKind::Type)
                        .map(|item| item.name.to_string())
                        .collect();

                    // Get the generics for the trait
                    let generics = tcx.generics_of(trait_ref.trait_def_id().unwrap());

                    // Get the list of type parameters default status (true if it has a default)
                    let mut type_params_default_status: Vec<bool> = generics
                        .params
                        .iter()
                        .filter_map(|param| match param.kind {
                            rustc_middle::ty::GenericParamDefKind::Type { has_default, .. } => {
                                Some(has_default)
                            }
                            _ => None,
                        })
                        .collect();
                    // The first type parameter is always the Self type, that we do not consider as
                    // part of the list of type parameters.
                    type_params_default_status.remove(0);

                    let ty_params = compile_path_ty_params(&tcx, trait_ref.path);

                    vec![TopLevelItem::TraitImpl {
                        generic_tys,
                        ty_params: ty_params
                            .into_iter()
                            .zip(type_params_default_status)
                            .collect(),
                        self_ty,
                        of_trait: compile_path(trait_ref.path),
                        items,
                        trait_non_default_items,
                    }]
                }
                None => {
                    let entry = impl_counter.entry(*self_ty.clone());
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
    args: &'a Vec<(String, Box<CoqType>)>,
    ret_ty: &'a CoqType,
    body: &'a Expr,
    is_dead_code: bool,
) -> Doc<'a> {
    group([
        if is_dead_code {
            concat([
                text("(* #[allow(dead_code)] - function was ignored by the compiler *)"),
                hardline(),
            ])
        } else {
            nil()
        },
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
                                    text(".Trait"),
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
                line(),
                nest([text(":"), line(), ret_ty.to_doc(false), text(" :=")]),
            ]),
            line(),
            body.to_doc(false),
            text("."),
        ]),
    ])
}

fn mt_impl_item(item: ImplItem) -> ImplItem {
    match item {
        ImplItem::Const { body, is_dead_code } => {
            let (body, _fresh_vars) = mt_expression(FreshVars::new(), *body);
            ImplItem::Const {
                body: Box::new(Expr::Block(Box::new(body))),
                is_dead_code,
            }
        }
        ImplItem::Definition {
            args,
            ret_ty,
            body,
            is_method,
            is_dead_code,
        } => {
            let (body, _fresh_vars) = mt_expression(FreshVars::new(), *body);
            ImplItem::Definition {
                args,
                ret_ty: CoqType::monad(mt_ty(ret_ty)),
                body: Box::new(Expr::Block(Box::new(body))),
                is_method,
                is_dead_code,
            }
        }
        ImplItem::Type { .. } => item,
    }
}

fn mt_impl_items(items: Vec<(String, ImplItem)>) -> Vec<(String, ImplItem)> {
    items
        .into_iter()
        .map(|(s, item)| (s, mt_impl_item(item)))
        .collect()
}

fn mt_trait_item(body: TraitItem) -> TraitItem {
    match body {
        TraitItem::Definition { ty } => TraitItem::Definition { ty: mt_ty(ty) },
        TraitItem::Type => TraitItem::Type,
        TraitItem::DefinitionWithDefault { args, ret_ty, body } => {
            let (body, _fresh_vars) = mt_expression(FreshVars::new(), *body);
            TraitItem::DefinitionWithDefault {
                args,
                ret_ty: CoqType::monad(mt_ty(ret_ty)),
                body: Box::new(Expr::Block(Box::new(body))),
            }
        }
    }
}

fn mt_trait_items(body: Vec<(String, TraitItem)>) -> Vec<(String, TraitItem)> {
    body.into_iter()
        .map(|(s, item)| (s, mt_trait_item(item)))
        .collect()
}

/// Monad transform for [TopLevelItem]
fn mt_top_level_item(item: TopLevelItem) -> TopLevelItem {
    match item {
        TopLevelItem::Const { name, ty, value } => {
            let (value, _fresh_vars) = mt_expression(FreshVars::new(), *value);
            TopLevelItem::Const {
                name,
                ty,
                value: Box::new(Expr::Block(Box::new(value))),
            }
        }
        TopLevelItem::Definition {
            name,
            ty_params,
            where_predicates,
            args,
            ret_ty,
            body,
            is_dead_code,
        } => {
            let (body, _fresh_vars) = mt_expression(FreshVars::new(), *body);
            TopLevelItem::Definition {
                name,
                ty_params,
                where_predicates,
                args,
                ret_ty: CoqType::monad(mt_ty(ret_ty)),
                body: Box::new(Expr::Block(Box::new(body))),
                is_dead_code,
            }
        }
        TopLevelItem::TypeAlias { name, ty } => TopLevelItem::TypeAlias { name, ty },
        TopLevelItem::TypeEnum { name, variants } => TopLevelItem::TypeEnum { name, variants },
        TopLevelItem::TypeStructStruct {
            name,
            fields,
            is_dead_code,
        } => TopLevelItem::TypeStructStruct {
            name,
            fields,
            is_dead_code,
        },
        TopLevelItem::TypeStructTuple { name, fields } => {
            TopLevelItem::TypeStructTuple { name, fields }
        }
        TopLevelItem::TypeStructUnit { name } => TopLevelItem::TypeStructUnit { name },
        TopLevelItem::Module {
            name,
            body,
            is_dead_code,
        } => TopLevelItem::Module {
            name,
            body: mt_top_level(body),
            is_dead_code,
        },
        TopLevelItem::Impl {
            self_ty,
            counter,
            items,
        } => TopLevelItem::Impl {
            self_ty,
            counter,
            items: mt_impl_items(items),
        },
        TopLevelItem::Trait {
            name,
            ty_params,
            body,
        } => TopLevelItem::Trait {
            name,
            ty_params,
            body: mt_trait_items(body),
        },
        TopLevelItem::TraitImpl {
            generic_tys,
            ty_params,
            self_ty,
            of_trait,
            items,
            trait_non_default_items,
        } => TopLevelItem::TraitImpl {
            generic_tys,
            ty_params,
            self_ty,
            of_trait,
            items: mt_impl_items(items),
            trait_non_default_items,
        },
        TopLevelItem::Use {
            name,
            path,
            is_glob,
            is_type,
        } => TopLevelItem::Use {
            name,
            path,
            is_glob,
            is_type,
        },
        TopLevelItem::Error(err) => TopLevelItem::Error(err),
    }
}

pub fn mt_top_level(top_level: TopLevel) -> TopLevel {
    TopLevel(top_level.0.into_iter().map(mt_top_level_item).collect())
}

impl ImplItem {
    fn class_instance_to_doc<'a>(
        instance_prefix: &'a str,
        name: &'a str,
        class_name: &'a str,
        method_name: &'a str,
    ) -> Doc<'a> {
        group([
            nest([
                nest([
                    text("Global Instance"),
                    line(),
                    text(format!("{instance_prefix}_{name}")),
                    text(" :"),
                ]),
                line(),
                nest([
                    text(class_name),
                    line(),
                    text(format!("\"{name}\"")),
                    text(" := {"),
                ]),
            ]),
            nest([
                hardline(),
                nest([
                    text(method_name),
                    line(),
                    text(":="),
                    line(),
                    text(name),
                    text(";"),
                ]),
            ]),
            hardline(),
            text("}."),
        ])
    }

    fn to_doc<'a>(&'a self, name: &'a String) -> Doc<'a> {
        match self {
            ImplItem::Const { body, is_dead_code } => concat([
                if *is_dead_code {
                    concat([
                        text("(* #[allow(dead_code)] - function was ignored by the compiler *)"),
                        hardline(),
                    ])
                } else {
                    nil()
                },
                nest([
                    text("Definition"),
                    line(),
                    text(name),
                    body.to_doc(false),
                    text("."),
                ]),
                hardline(),
                hardline(),
                Self::class_instance_to_doc(
                    "AssociatedFunction",
                    name,
                    "Notation.DoubleColon Self",
                    "Notation.double_colon",
                ),
            ]),
            ImplItem::Definition {
                args,
                ret_ty,
                body,
                is_method,
                is_dead_code,
            } => concat([
                fn_to_doc(name, None, None, args, ret_ty, body, *is_dead_code),
                hardline(),
                hardline(),
                if *is_method {
                    concat([Self::class_instance_to_doc(
                        "Method",
                        name,
                        "Notation.Dot",
                        "Notation.dot",
                    )])
                } else {
                    Self::class_instance_to_doc(
                        "AssociatedFunction",
                        name,
                        "Notation.DoubleColon Self",
                        "Notation.double_colon",
                    )
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
            TopLevelItem::Const { name, ty, value } => nest([
                nest([
                    text("Definition"),
                    line(),
                    text(name),
                    text(" :"),
                    line(),
                    ty.to_doc(false),
                    text(" :="),
                ]),
                line(),
                nest([
                    text("run"),
                    line(),
                    // We have to force the parenthesis because otherwise they
                    // are lost when printing a statement in the expression
                    text("("),
                    value.to_doc(true),
                    text(")"),
                ]),
                text("."),
            ]),
            TopLevelItem::Definition {
                name,
                ty_params,
                where_predicates,
                args,
                ret_ty,
                body,
                is_dead_code,
            } => fn_to_doc(
                name,
                Some(ty_params),
                Some(where_predicates),
                args,
                ret_ty,
                body,
                *is_dead_code,
            ),
            TopLevelItem::Module {
                name,
                body,
                is_dead_code,
            } => group([
                if *is_dead_code {
                    concat([
                        text("(* #[allow(dead_code)] - module was ignored by the compiler *)"),
                        hardline(),
                    ])
                } else {
                    nil()
                },
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
                    concat(variants.iter().map(|(name, fields)| match fields {
                        VariantItem::Tuple { .. } => nil(),
                        VariantItem::Struct { fields } => concat([
                            nest([text("Module"), line(), text(name), text(".")]),
                            nest([
                                hardline(),
                                nest([
                                    text("Record"),
                                    line(),
                                    text("t"),
                                    text(" :"),
                                    line(),
                                    text("Set"),
                                    text(" := {"),
                                ]),
                                nest([concat(fields.iter().map(|(name, ty)| {
                                    concat([
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
                                }))]),
                                hardline(),
                                text("}."),
                            ]),
                            hardline(),
                            nest([text("End"), line(), text(name), text(".")]),
                            hardline(),
                            hardline(),
                        ]),
                    })),
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
                        variants.iter().map(|(name, fields)| {
                            nest([
                                text("|"),
                                line(),
                                text(name),
                                match fields {
                                    VariantItem::Struct { .. } => concat([
                                        line(),
                                        nest([
                                            text("(_ :"),
                                            line(),
                                            text(format!("{name}.t")),
                                            text(")"),
                                        ]),
                                    ]),
                                    VariantItem::Tuple { tys } => concat(tys.iter().map(|ty| {
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
                                },
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
            TopLevelItem::TypeStructStruct {
                name,
                fields,
                is_dead_code,
            } => group([
                if *is_dead_code {
                    concat([
                        text("(* #[allow(dead_code)] - struct was ignored by the compiler *)"),
                        hardline(),
                    ])
                } else {
                    nil()
                },
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
                                        text("Global Instance"),
                                        line(),
                                        text(format!("Get_{name}")),
                                        text(" :"),
                                    ]),
                                    line(),
                                    nest([
                                        text("Notation.Dot"),
                                        line(),
                                        text(format!("\"{name}\"")),
                                        text(" := {"),
                                    ]),
                                ]),
                                hardline(),
                                nest([
                                    text("Notation.dot"),
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
                            text("}."),
                        ])
                    })),
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
                            text("Record"),
                            line(),
                            text("t"),
                            line(),
                            nest([text(":"), line(), text("Set"), text(" :=")]),
                        ]),
                        line(),
                        nest([
                            text("{"),
                            line(),
                            intersperse(
                                fields.iter().map(|ty| {
                                    nest([text("_ :"), line(), ty.to_doc(false), text(";")])
                                }),
                                [line()],
                            ),
                            text("}"),
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
                                            text("Global Instance"),
                                            line(),
                                            text(format!("Get_{i}")),
                                            text(" :"),
                                        ]),
                                        line(),
                                        nest([
                                            text("Notation.Dot"),
                                            line(),
                                            text(i.to_string()),
                                            text(" := {"),
                                        ]),
                                    ]),
                                    if !fields.is_empty() {
                                        hardline()
                                    } else {
                                        nil()
                                    },
                                    nest([
                                        text("Notation.dot"),
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
                                text("}."),
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
            TopLevelItem::TypeStructUnit { name } => group([
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
                        nest([text("Build"), text(".")]),
                    ]),
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
                            concat([hardline(), hardline(), item.to_doc(name)])
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
                            text("Trait"),
                            line(),
                            nest([
                                text("{"),
                                text("Self"),
                                line(),
                                concat(ty_params.iter().map(|ty| concat([text(ty), line()]))),
                                text(":"),
                                line(),
                                text("Set"),
                                text("}"),
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
                                    text(format!("Method_{name}")),
                                    line(),
                                    text("`(Trait)"),
                                ]),
                                line(),
                                nest([
                                    text(": Notation.Dot"),
                                    line(),
                                    text(format!("\"{name}\"")),
                                    line(),
                                    text(":= {"),
                                ]),
                            ]),
                            nest([
                                hardline(),
                                match item {
                                    TraitItem::Definition { .. } | TraitItem::Type => nest([
                                        text("Notation.dot"),
                                        line(),
                                        text(":="),
                                        line(),
                                        text(name),
                                        text(";"),
                                    ]),
                                    TraitItem::DefinitionWithDefault { args, ret_ty, body } => {
                                        nest([
                                            nest([
                                                text("Notation.dot"),
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
                                            text("("),
                                            body.to_doc(false),
                                            line(),
                                            nest([
                                                text(":"),
                                                line(),
                                                ret_ty.to_doc(false),
                                                text(")"),
                                            ]),
                                            text(";"),
                                        ])
                                    }
                                },
                            ]),
                            hardline(),
                            text("}."),
                        ])
                    })),
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
            } => {
                group([
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
                            concat([item.to_doc(name), hardline(), hardline()])
                        })),
                        nest([
                            nest([
                                nest([text("Global Instance"), line(), text("I")]),
                                line(),
                                concat(
                                    generic_tys
                                        .iter()
                                        .map(|generic_ty| concat([text(generic_ty), line()])),
                                ),
                                text(":"),
                                line(),
                                of_trait.to_doc(),
                                text(".Trait"),
                                line(),
                                text("Self"),
                                concat(ty_params.iter().map(|(ty_param, has_default)| {
                                    concat([
                                        line(),
                                        (if *has_default {
                                            nest([
                                                text("(Some"),
                                                line(),
                                                ty_param.to_doc(false),
                                                text(")"),
                                            ])
                                        } else {
                                            ty_param.to_doc(false)
                                        }),
                                    ])
                                })),
                            ]),
                            text(" :="),
                            line(),
                            if items.is_empty() {
                                nest([of_trait.to_doc(), text(".Build_Class"), line(), text("_")])
                            } else {
                                text("{")
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
                            group([hardline(), text("}.")])
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
                ])
            }
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
