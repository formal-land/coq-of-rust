use crate::configuration::*;
use crate::coq;
use crate::env::*;
use crate::expression::*;
use crate::header::*;
use crate::path::*;
use crate::render::*;
use crate::reorder::*;
use crate::ty::*;
use itertools::Itertools;
use rustc_ast::ast::{AttrArgs, AttrKind};
use rustc_hir::{
    GenericBound, GenericBounds, GenericParamKind, Impl, ImplItemKind, ImplItemRef, Item, ItemId,
    ItemKind, PatKind, QPath, TraitFn, TraitItemKind, Ty, TyKind, VariantData,
};
use rustc_middle::ty::TyCtxt;
use rustc_span::symbol::sym;
use std::collections::HashMap;
use std::iter::repeat;
use std::string::ToString;

pub(crate) struct TopLevelOptions {
    pub(crate) configuration_file: String,
    pub(crate) filename: String,
    pub(crate) axiomatize: bool,
    pub(crate) generate_reorder: bool,
}

#[derive(Clone, Debug)]
struct HirFnSigAndBody<'a> {
    fn_sig: &'a rustc_hir::FnSig<'a>,
    body: &'a rustc_hir::Body<'a>,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct FnSigAndBody {
    args: Vec<(String, Box<CoqType>)>,
    ret_ty: Box<CoqType>,
    body: Option<Box<Expr>>,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum TraitItem {
    Definition {
        ty_params: Vec<String>,
        where_predicates: Vec<WherePredicate>,
        ty: Box<CoqType>,
    },
    DefinitionWithDefault {
        ty_params: Vec<String>,
        where_predicates: Vec<WherePredicate>,
        signature_and_body: FnSigAndBody,
    },
    Type(Vec<TraitBound>),
}

/// fields common for all function definitions
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct FunDefinition {
    name: String,
    ty_params: Vec<String>,
    where_predicates: Vec<WherePredicate>,
    signature_and_body: FnSigAndBody,
    is_dead_code: bool,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum ImplItem {
    Const {
        name: String,
        body: Box<Expr>,
        is_dead_code: bool,
    },
    Definition {
        definition: FunDefinition,
        is_method: bool,
    },
    Type {
        name: String,
        ty: Box<CoqType>,
    },
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct WherePredicate {
    bound: TraitBound,
    ty: Box<CoqType>,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct TraitBound {
    name: Path,
    ty_params: Vec<Box<TraitTyParamValue>>,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum VariantItem {
    Struct { fields: Vec<(String, Box<CoqType>)> },
    Tuple { tys: Vec<Box<CoqType>> },
}

/// The actual value of the type parameter of the trait's generic parameter
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum TraitTyParamValue {
    /// the value of the parameter that has no default
    JustValue { name: String, ty: Box<CoqType> },
    /// the value that replaces the default value of the parameter
    ValWithDef { name: String, ty: Box<CoqType> },
    /// means the default value of the type parameter is used
    JustDefault { name: String },
}

/// Representation of top-level hir [Item]s in coq-of-rust
/// See https://doc.rust-lang.org/reference/items.html
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum TopLevelItem {
    Const {
        name: String,
        ty: Box<CoqType>,
        value: Option<Box<Expr>>,
    },
    Definition(FunDefinition),
    TypeAlias {
        name: String,
        ty_params: Vec<String>,
        ty: Box<CoqType>,
    },
    TypeEnum {
        name: String,
        variants: Vec<(String, VariantItem)>,
    },
    TypeStructStruct {
        name: String,
        ty_params: Vec<String>,
        fields: Vec<(String, Box<CoqType>)>,
        is_dead_code: bool,
    },
    TypeStructTuple {
        name: String,
        ty_params: Vec<String>,
        fields: Vec<Box<CoqType>>,
    },
    TypeStructUnit {
        name: String,
        ty_params: Vec<String>,
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
        items: Vec<ImplItem>,
    },
    Trait {
        name: String,
        ty_params: Vec<(String, Option<Box<CoqType>>)>,
        predicates: Vec<WherePredicate>,
        bounds: Vec<TraitBound>,
        body: Vec<(String, TraitItem)>,
    },
    TraitImpl {
        generic_tys: Vec<String>,
        ty_params: Vec<Box<TraitTyParamValue>>,
        self_ty: Box<CoqType>,
        of_trait: Path,
        items: Vec<ImplItem>,
        trait_non_default_items: Vec<String>,
    },
    Error(String),
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct TopLevel(Vec<TopLevelItem>);

/// emits a warning with the given messages
fn emit_warning_with_note(env: &Env, span: &rustc_span::Span, warning_msg: &str, note_msg: &str) {
    env.tcx
        .sess
        .struct_span_warn(*span, warning_msg)
        .note(note_msg)
        .emit();
}

/// returns Some(item) if the condition is satisfied
fn give_if<T>(item: T, condition: bool) -> Option<T> {
    if condition {
        Some(item)
    } else {
        None
    }
}

/// returns Some(item) if the condition is not satisfied
fn give_if_not<T>(item: T, condition: bool) -> Option<T> {
    give_if(item, !condition)
}

/// compiles a function with the given signature and body
fn compile_fn_sig_and_body(
    env: &mut Env,
    fn_sig_and_body: &HirFnSigAndBody,
    default: &str,
) -> FnSigAndBody {
    let decl = fn_sig_and_body.fn_sig.decl;
    FnSigAndBody {
        args: get_args(env, fn_sig_and_body.body, decl.inputs, default),
        ret_ty: compile_fn_ret_ty(env, &decl.output),
        body: compile_function_body(env, fn_sig_and_body.body),
    }
}

/// Check if the function body is actually the main test function calling to all
/// tests in the file. If so, we do not want to compile it.
fn check_if_is_test_main_function(tcx: &TyCtxt, body_id: &rustc_hir::BodyId) -> bool {
    let body = tcx.hir().body(*body_id);
    let expr = body.value;
    if let rustc_hir::ExprKind::Block(block, _) = expr.kind {
        if let Some(expr) = block.expr {
            if let rustc_hir::ExprKind::Call(func, _) = expr.kind {
                if let rustc_hir::ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) = &func.kind {
                    if let [base, path] = path.segments {
                        return base.ident.name.to_string() == "test"
                            && path.ident.name.to_string() == "test_main_static";
                    }
                }
            }
        }
    }
    false
}

/// Check if a top-level definition is actually test metadata. If so, we ignore
/// it.
fn check_if_test_declaration(ty: &Ty) -> bool {
    if let TyKind::Path(QPath::Resolved(_, path)) = &ty.kind {
        if let [base, path] = path.segments {
            return base.ident.name.to_string() == "test"
                && path.ident.name.to_string() == "TestDescAndFn";
        }
    }
    false
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

/// We deduplicate items while keeping there order. Often, items are duplicated
/// due to module imports or such.
fn deduplicate_top_level_items(items: Vec<TopLevelItem>) -> Vec<TopLevelItem> {
    items.into_iter().unique().collect()
}

/// [compile_top_level_item] compiles hir [Item]s into coq-of-rust (optional)
/// items.
/// - See https://doc.rust-lang.org/stable/nightly-rustc/rustc_hir/struct.Item.html
///   and the doc for [TopLevelItem]
/// - [rustc_middle::hir::map::Map] is intuitively the type for hir environments
/// - Method [body] allows retrievient the body of an identifier [body_id] in an
///   hir environment [hir]
fn compile_top_level_item(tcx: &TyCtxt, env: &mut Env, item: &Item) -> Vec<TopLevelItem> {
    let name = to_valid_coq_name(item.ident.name.to_string());
    if env.axiomatize {
        let def_id = item.owner_id.to_def_id();
        let is_public = tcx.visibility(def_id).is_public();
        if !is_public {
            // Do not generate anything if the item is not public and we are
            // axiomatizing the definitions (for a library). Also, still
            // generate the modules, since they may contain public items.
            match &item.kind {
                ItemKind::Mod(_) => {}
                _ => return vec![],
            }
        }
    }

    match &item.kind {
        ItemKind::ExternCrate(_) => vec![],
        ItemKind::Use(..) => vec![],
        ItemKind::Static(ty, _, body_id) | ItemKind::Const(ty, body_id) => {
            if check_if_test_declaration(ty) {
                return vec![];
            }
            // skip const _ : () = ...
            if name == "_" && matches!(ty.kind, TyKind::Tup([])) {
                return vec![];
            }

            let value = if env.axiomatize {
                None
            } else {
                let value = tcx.hir().body(*body_id).value;
                Some(Box::new(compile_expr(env, value)))
            };
            vec![TopLevelItem::Const {
                name,
                ty: compile_type(env, ty),
                value,
            }]
        }
        ItemKind::Fn(fn_sig, generics, body_id) => {
            if check_if_is_test_main_function(tcx, body_id) {
                return vec![];
            }
            let is_dead_code = check_dead_code_lint_in_attributes(tcx, item);
            let fn_sig_and_body = get_hir_fn_sig_and_body(tcx, fn_sig, body_id);
            vec![TopLevelItem::Definition(compile_fun_definition(
                env,
                &name,
                generics,
                &fn_sig_and_body,
                "arg",
                is_dead_code,
            ))]
        }
        ItemKind::Macro(_, _) => vec![],
        ItemKind::Mod(module) => {
            let is_dead_code = check_dead_code_lint_in_attributes(tcx, item);
            let mut items: Vec<ItemId> = module.item_ids.to_vec();
            reorder_definitions_inplace(tcx, env, &mut items);
            let items = deduplicate_top_level_items(
                items
                    .iter()
                    .flat_map(|item_id| {
                        let item = tcx.hir().item(*item_id);
                        compile_top_level_item(tcx, env, item)
                    })
                    .collect(),
            );
            // We remove empty modules in the translation
            if items.is_empty() {
                return vec![];
            }
            vec![TopLevelItem::Module {
                name,
                body: TopLevel(items),
                is_dead_code,
            }]
        }
        ItemKind::ForeignMod { .. } => {
            vec![TopLevelItem::Error("ForeignMod".to_string())]
        }
        ItemKind::GlobalAsm(_) => vec![TopLevelItem::Error("GlobalAsm".to_string())],
        ItemKind::TyAlias(ty, generics) => vec![TopLevelItem::TypeAlias {
            name,
            ty: compile_type(env, ty),
            ty_params: get_ty_params_names(env, generics),
        }],
        ItemKind::OpaqueTy(_) => vec![TopLevelItem::Error("OpaqueTy".to_string())],
        ItemKind::Enum(enum_def, _) => vec![TopLevelItem::TypeEnum {
            name,
            variants: enum_def
                .variants
                .iter()
                .map(|variant| {
                    let name = variant.ident.name.to_string();
                    let fields = match &variant.data {
                        VariantData::Struct(fields, _) => {
                            let fields = fields
                                .iter()
                                .map(|field| (field.ident.to_string(), compile_type(env, field.ty)))
                                .collect();
                            VariantItem::Struct { fields }
                        }
                        VariantData::Tuple(fields, _, _) => {
                            let tys = fields
                                .iter()
                                .map(|field| compile_type(env, field.ty))
                                .collect();
                            VariantItem::Tuple { tys }
                        }
                        VariantData::Unit(_, _) => VariantItem::Tuple { tys: vec![] },
                    };
                    (name, fields)
                })
                .collect(),
        }],
        ItemKind::Struct(body, generics) => {
            let is_dead_code = check_dead_code_lint_in_attributes(tcx, item);
            let ty_params = get_ty_params_names(env, generics);

            match body {
                VariantData::Struct(fields, _) => {
                    let fields = fields
                        .iter()
                        .map(|field| (field.ident.name.to_string(), compile_type(env, field.ty)))
                        .collect();
                    vec![TopLevelItem::TypeStructStruct {
                        name,
                        ty_params,
                        fields,
                        is_dead_code,
                    }]
                }
                VariantData::Tuple(fields, _, _) => {
                    vec![TopLevelItem::TypeStructTuple {
                        name,
                        ty_params,
                        fields: fields
                            .iter()
                            .map(|field| compile_type(env, field.ty))
                            .collect(),
                    }]
                }
                VariantData::Unit(_, _) => {
                    vec![TopLevelItem::TypeStructUnit { name, ty_params }]
                }
            }
        }
        ItemKind::Union(_, _) => vec![TopLevelItem::Error("Union".to_string())],
        ItemKind::Trait(_, _, generics, generic_bounds, items) => {
            vec![TopLevelItem::Trait {
                name,
                ty_params: get_ty_params(env, generics),
                predicates: get_where_predicates(tcx, env, generics),
                bounds: compile_generic_bounds(tcx, env, generic_bounds),
                body: items
                    .iter()
                    .map(|item| {
                        let item = tcx.hir().trait_item(item.id);
                        let ty_params = get_ty_params_names(env, item.generics);
                        let where_predicates = get_where_predicates(tcx, env, item.generics);
                        let body =
                            compile_trait_item_body(tcx, env, ty_params, where_predicates, item);
                        (to_valid_coq_name(item.ident.name.to_string()), body)
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
            let is_dead_code = check_dead_code_lint_in_attributes(tcx, item);
            let generic_tys = get_ty_params_names(env, generics);
            let self_ty = compile_type(env, self_ty);
            let entry = env.impl_counter.entry(*self_ty.clone());
            let counter = *entry.and_modify(|counter| *counter += 1).or_insert(1);
            let mut items: Vec<ImplItemRef> = items.to_vec();
            reorder_definitions_inplace(tcx, env, &mut items);

            let items = compile_impl_item_refs(tcx, env, &items, is_dead_code);

            match of_trait {
                Some(trait_ref) => {
                    let trait_non_default_items = tcx
                        .associated_items(trait_ref.trait_def_id().unwrap())
                        .in_definition_order()
                        .filter(|item| !item.defaultness(*tcx).has_value())
                        .filter(|item| item.kind != rustc_middle::ty::AssocKind::Type)
                        .map(|item| item.name.to_string())
                        .collect();

                    // Get the generics for the trait
                    let generics = tcx.generics_of(trait_ref.trait_def_id().unwrap());

                    vec![TopLevelItem::TraitImpl {
                        generic_tys,
                        ty_params: get_ty_params_with_default_status(env, generics, trait_ref.path),
                        self_ty,
                        of_trait: compile_path(env, trait_ref.path),
                        items,
                        trait_non_default_items,
                    }]
                }
                None => {
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

/// returns a pair of function signature and its body
fn get_hir_fn_sig_and_body<'a>(
    tcx: &'a TyCtxt,
    fn_sig: &'a rustc_hir::FnSig<'a>,
    body_id: &rustc_hir::BodyId,
) -> HirFnSigAndBody<'a> {
    HirFnSigAndBody {
        fn_sig,
        body: get_body(tcx, body_id),
    }
}

/// compiles a list of references to items
fn compile_impl_item_refs(
    tcx: &TyCtxt,
    env: &mut Env,
    item_refs: &[ImplItemRef],
    is_dead_code: bool,
) -> Vec<ImplItem> {
    item_refs
        .iter()
        .map(|item_ref| {
            compile_impl_item(
                tcx,
                env,
                tcx.hir().impl_item(item_ref.id),
                is_method(item_ref),
                is_dead_code,
            )
        })
        .collect()
}

/// tells if the referenced item is a method
fn is_method(item_ref: &ImplItemRef) -> bool {
    if let rustc_hir::AssocItemKind::Fn { has_self } = item_ref.kind {
        has_self
    } else {
        false
    }
}

/// compiles an item
fn compile_impl_item(
    tcx: &TyCtxt,
    env: &mut Env,
    item: &rustc_hir::ImplItem,
    is_method: bool,
    is_dead_code: bool,
) -> ImplItem {
    let name = item.ident.name.to_string();
    match &item.kind {
        ImplItemKind::Const(_, body_id) => {
            let expr = tcx.hir().body(*body_id).value;
            ImplItem::Const {
                name,
                body: Box::new(compile_expr(env, expr)),
                is_dead_code,
            }
        }
        ImplItemKind::Fn(fn_sig, body_id) => ImplItem::Definition {
            definition: compile_fun_definition(
                env,
                &name,
                item.generics,
                &get_hir_fn_sig_and_body(tcx, fn_sig, body_id),
                "Pattern",
                is_dead_code,
            ),
            is_method,
        },
        ImplItemKind::Type(ty) => ImplItem::Type {
            name,
            ty: compile_type(env, ty),
        },
    }
}

/// compiles a given function
fn compile_fun_definition(
    env: &mut Env,
    name: &str,
    generics: &rustc_hir::Generics,
    fn_sig_and_body: &HirFnSigAndBody,
    default: &str,
    is_dead_code: bool,
) -> FunDefinition {
    let tcx = env.tcx;
    FunDefinition {
        name: name.to_owned(),
        ty_params: get_ty_params_names(env, generics),
        where_predicates: get_where_predicates(&tcx, env, generics),
        signature_and_body: compile_fn_sig_and_body(env, fn_sig_and_body, default),
        is_dead_code,
    }
}

/// returns the body corresponding to the given body_id
fn get_body<'a>(tcx: &'a TyCtxt, body_id: &rustc_hir::BodyId) -> &'a rustc_hir::Body<'a> {
    tcx.hir().body(*body_id)
}

// compiles the body of a function
fn compile_function_body(env: &mut Env, body: &rustc_hir::Body) -> Option<Box<Expr>> {
    give_if_not(Box::new(compile_expr(env, body.value)), env.axiomatize)
}

/// returns a list of pairs of argument names and their types
fn get_args(
    env: &Env,
    body: &rustc_hir::Body,
    inputs: &[rustc_hir::Ty],
    default: &str,
) -> Vec<(String, Box<CoqType>)> {
    get_arg_names(body, default)
        .zip(inputs.iter().map(|ty| compile_type(env, ty)))
        .collect()
}

/// returns names of the arguments
fn get_arg_names<'a>(
    body: &'a rustc_hir::Body,
    default: &'a str,
) -> impl Iterator<Item = String> + 'a {
    body.params.iter().map(|param| match param.pat.kind {
        PatKind::Binding(_, _, ident, _) => ident.name.to_string(),
        _ => default.to_string(),
    })
}

/// filters out type parameters and compiles them with the given function
fn compile_ty_params<T>(
    env: &Env,
    generics: &rustc_hir::Generics,
    f: impl Fn(&Env, String, Option<&Ty>) -> T,
) -> Vec<T> {
    generics
        .params
        .iter()
        .filter_map(|param| match param.kind {
            // we ignore lifetimes
            GenericParamKind::Lifetime { .. } => None,
            GenericParamKind::Type { default, .. } => {
                Some(f(env, param.name.ident().to_string(), default))
            }
            // @TODO: do we want to also support constant parameters?
            GenericParamKind::Const { ty: _, default: _ } => {
                let span = &param.span;
                let warning_msg = "Constant parameters are not supported yet.";
                let note_msg = "It should be supported in future versions.";
                emit_warning_with_note(env, span, warning_msg, note_msg);
                None
            }
        })
        .collect()
}

/// extracts type parameters with their optional default value from the generics
fn get_ty_params(env: &Env, generics: &rustc_hir::Generics) -> Vec<(String, Option<Box<CoqType>>)> {
    compile_ty_params(env, generics, |env, name, default| {
        let default = default.map(|default| compile_type(env, default));
        let name = to_valid_coq_name(name);
        (name, default)
    })
}

/// extracts the names of type parameters from the generics
fn get_ty_params_names(env: &Env, generics: &rustc_hir::Generics) -> Vec<String> {
    compile_ty_params(env, generics, |_, name, _| to_valid_coq_name(name))
}

/// extracts where predicates from the generics
fn get_where_predicates(
    tcx: &TyCtxt,
    env: &Env,
    generics: &rustc_hir::Generics,
) -> Vec<WherePredicate> {
    generics
        .predicates
        .iter()
        .flat_map(|predicate| match predicate {
            rustc_hir::WherePredicate::BoundPredicate(predicate) => {
                let names_and_ty_params = compile_generic_bounds(tcx, env, predicate.bounds);
                names_and_ty_params
                    .into_iter()
                    .map(|bound| {
                        trait_bound_to_where_predicate(
                            bound,
                            compile_type(env, predicate.bounded_ty),
                        )
                    })
                    .collect()
            }
            _ => vec![],
        })
        .collect()
}

/// converts a trait bound to a where predicate
fn trait_bound_to_where_predicate(bound: TraitBound, ty: Box<CoqType>) -> WherePredicate {
    WherePredicate { bound, ty }
}

/// [compile_generic_bounds] compiles generic bounds in [compile_trait_item_body]
fn compile_generic_bounds(
    tcx: &TyCtxt,
    env: &Env,
    generic_bounds: GenericBounds,
) -> Vec<TraitBound> {
    generic_bounds
        .iter()
        .filter_map(|generic_bound| match generic_bound {
            GenericBound::Trait(ptraitref, _) => Some(compile_trait_bound(tcx, env, ptraitref)),
            GenericBound::LangItemTrait { .. } => {
                let warning_msg = "LangItem trait bounds are not supported yet.";
                let note_msg = "It will change in the future.";
                let span = &generic_bound.span();
                emit_warning_with_note(env, span, warning_msg, note_msg);
                None
            }
            // we ignore lifetimes
            GenericBound::Outlives { .. } => None,
        })
        .collect()
}

/// Get the generics for the trait
fn compile_trait_bound(tcx: &TyCtxt, env: &Env, ptraitref: &rustc_hir::PolyTraitRef) -> TraitBound {
    TraitBound {
        name: compile_path(env, ptraitref.trait_ref.path),
        ty_params: get_ty_params_with_default_status(
            env,
            tcx.generics_of(ptraitref.trait_ref.trait_def_id().unwrap()),
            ptraitref.trait_ref.path,
        ),
    }
}

/// computes tre list of actual type parameters with their default status
fn get_ty_params_with_default_status(
    env: &Env,
    generics: &rustc_middle::ty::Generics,
    path: &rustc_hir::Path,
) -> Vec<Box<TraitTyParamValue>> {
    let mut type_params_name_and_default_status = type_params_name_and_default_status(generics);
    // The first type parameter is always the Self type, that we do not consider as
    // part of the list of type parameters.
    type_params_name_and_default_status.remove(0);

    let ty_params = compile_path_ty_params(env, path);
    add_default_status_to_ty_params(&ty_params, &type_params_name_and_default_status)
}

/// takes a list of actual type parameters
/// and the information about required and default type parameters
/// and returns a list that combines them
fn add_default_status_to_ty_params(
    ty_params: &[Box<CoqType>],
    names_and_default_status: &[(String, bool)],
) -> Vec<Box<TraitTyParamValue>> {
    ty_params
        .iter()
        .map(Some)
        .chain(repeat(None))
        .zip(names_and_default_status)
        .map(|(ty, (name, has_default))| {
            compile_ty_param_value(name, ty.map(|ty| &**ty), has_default)
        })
        .collect()
}

/// compiles a type parameter
fn compile_ty_param_value(
    name: &str,
    ty: Option<&CoqType>,
    has_default: &bool,
) -> Box<TraitTyParamValue> {
    Box::new(match ty {
        Some(ty) => {
            if *has_default {
                TraitTyParamValue::ValWithDef {
                    name: name.to_string(),
                    ty: Box::new(ty.clone()),
                }
            } else {
                TraitTyParamValue::JustValue {
                    name: name.to_string(),
                    ty: Box::new(ty.clone()),
                }
            }
        }
        None => TraitTyParamValue::JustDefault {
            name: name.to_string(),
        },
    })
}

/// Get the list of type parameters names and default status (true if it has a default)
fn type_params_name_and_default_status(
    generics: &rustc_middle::ty::Generics,
) -> Vec<(String, bool)> {
    generics
        .params
        .iter()
        .filter_map(|param| match param.kind {
            rustc_middle::ty::GenericParamDefKind::Type { has_default, .. } => {
                Some((param.name.to_string(), has_default))
            }
            _ => None,
        })
        .collect()
}

/// [compile_trait_item_body] compiles the body of the trait item
fn compile_trait_item_body(
    tcx: &TyCtxt,
    env: &mut Env,
    ty_params: Vec<String>,
    where_predicates: Vec<WherePredicate>,
    item: &rustc_hir::TraitItem,
) -> TraitItem {
    match &item.kind {
        TraitItemKind::Const(ty, _) => TraitItem::Definition {
            ty_params,
            where_predicates,
            ty: compile_type(env, ty),
        },
        TraitItemKind::Fn(fn_sig, trait_fn) => match trait_fn {
            TraitFn::Required(_) => TraitItem::Definition {
                ty_params,
                where_predicates,
                ty: compile_fn_decl(env, fn_sig.decl),
            },
            TraitFn::Provided(body_id) => {
                let env_tcx = env.tcx;
                let fn_sig_and_body = get_hir_fn_sig_and_body(&env_tcx, fn_sig, body_id);
                let signature_and_body = compile_fn_sig_and_body(env, &fn_sig_and_body, "arg");
                TraitItem::DefinitionWithDefault {
                    ty_params,
                    where_predicates,
                    signature_and_body,
                }
            }
        },
        TraitItemKind::Type(generic_bounds, concrete_type) => {
            if concrete_type.is_some() {
                let span = &item.span;
                let warning_msg = "Concrete value of associated types is not supported yet.";
                let note_msg = "It may change in future versions.";
                emit_warning_with_note(env, span, warning_msg, note_msg);
            }
            let generic_bounds = compile_generic_bounds(tcx, env, generic_bounds);
            TraitItem::Type(generic_bounds)
        }
    }
}

fn compile_top_level(tcx: &TyCtxt, opts: TopLevelOptions) -> TopLevel {
    let mut env = Env {
        impl_counter: HashMap::new(),
        tcx: *tcx,
        axiomatize: opts.axiomatize,
        file: opts.filename,
        reorder_map: HashMap::new(),
        configuration: get_configuration(&opts.configuration_file),
    };

    let mut results: Vec<ItemId> = tcx.hir().items().collect();
    reorder_definitions_inplace(tcx, &mut env, &mut results);

    let results = deduplicate_top_level_items(
        results
            .iter()
            .flat_map(|item_id| {
                let item = tcx.hir().item(*item_id);
                compile_top_level_item(tcx, &mut env, item)
            })
            .collect(),
    );

    if opts.generate_reorder {
        let json = serde_json::json!({ "reorder": HashMap::from([(env.file.to_string(), env.reorder_map)])});
        println!("{}", serde_json::to_string_pretty(&json).expect("json"));
    }
    TopLevel(results)
}

const LINE_WIDTH: usize = 80;

pub(crate) fn top_level_to_coq(tcx: &TyCtxt, opts: TopLevelOptions) -> String {
    let configuration = get_configuration(&opts.configuration_file);
    let opts = TopLevelOptions {
        // @TODO create a function to read configuration file and
        // merge command line options and return a single Configuration
        // object instead of using TopLevelOptions + Configuration
        axiomatize: opts.axiomatize || configuration.axiomatize,
        ..opts
    };
    let top_level = compile_top_level(tcx, opts);
    let top_level = mt_top_level(top_level);
    top_level.to_pretty(LINE_WIDTH)
}

fn types_for_f(extra_data: Option<&TopLevelItem>) -> Doc {
    match extra_data {
        // @TODO this is support for TypeStructStruct,
        // add support for more items
        Some(TopLevelItem::TypeStructStruct {
            name: _,
            fields,
            is_dead_code: _,
            .. // @TODO do generic params should be used here?
        }) => {
            concat([
                text("string"),
                text(" -> "),
                line(),
                intersperse(
                    fields.iter().map(|(_str, boxed_coq_type)| {
                        let nm = boxed_coq_type.to_name();
                        let nn = if nm == *"StaticRef_str" {
                            String::from("string")
                        } else {
                            boxed_coq_type.to_name()
                        };
                        group([
                            // print field name
                            text("string"),
                            text(" -> "),
                            // print field type
                            text(nn),
                            text(" -> "),
                        ])
                    }),
                    [line()],
                ),
                line(),
            ])
        }
        // @TODO unreachable branch, extend to cover more cases
        _ => nil(),
    }
}

// additional check. can be eliminated when all possible cases will be covered
fn is_extra(extra_data: Option<&TopLevelItem>) -> bool {
    match extra_data {
        // @TODO this is support for TypeStructStruct,
        // add support for more items
        Some(TopLevelItem::TypeStructStruct {
            name: _,
            fields: _,
            is_dead_code: _,
            ..
        }) => true,
        _ => false,
    }
}

fn mt_impl_item(item: ImplItem) -> ImplItem {
    match item {
        ImplItem::Const {
            name,
            body,
            is_dead_code,
        } => {
            let (body, _fresh_vars) = mt_expression(FreshVars::new(), *body);
            ImplItem::Const {
                name,
                body: Box::new(Expr::Block(Box::new(body))),
                is_dead_code,
            }
        }
        ImplItem::Definition {
            definition:
                FunDefinition {
                    name,
                    ty_params,
                    where_predicates,
                    signature_and_body,
                    is_dead_code,
                },
            is_method,
        } => ImplItem::Definition {
            definition: FunDefinition {
                name,
                ty_params,
                where_predicates,
                signature_and_body: mt_fn_sig_and_body(signature_and_body),
                is_dead_code,
            },
            is_method,
        },
        ImplItem::Type { .. } => item,
    }
}

fn mt_impl_items(items: Vec<ImplItem>) -> Vec<ImplItem> {
    items.into_iter().map(mt_impl_item).collect()
}

fn mt_fn_sig_and_body(signature_and_body: FnSigAndBody) -> FnSigAndBody {
    let FnSigAndBody { args, ret_ty, body } = signature_and_body;
    FnSigAndBody {
        args,
        ret_ty: CoqType::monad(mt_ty(ret_ty)),
        body: match body {
            None => body,
            Some(body) => {
                let (body, _fresh_vars) = mt_expression(FreshVars::new(), *body);
                Some(Box::new(Expr::Block(Box::new(body))))
            }
        },
    }
}

fn mt_trait_item(body: TraitItem) -> TraitItem {
    match body {
        TraitItem::Definition {
            ty_params,
            where_predicates,
            ty,
        } => TraitItem::Definition {
            ty_params,
            where_predicates,
            ty: mt_ty(ty),
        },
        TraitItem::Type(x) => TraitItem::Type(x), // @TODO apply MT
        TraitItem::DefinitionWithDefault {
            ty_params,
            where_predicates,
            signature_and_body,
        } => TraitItem::DefinitionWithDefault {
            ty_params,
            where_predicates,
            signature_and_body: mt_fn_sig_and_body(signature_and_body),
        },
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
        TopLevelItem::Const { name, ty, value } => TopLevelItem::Const {
            name,
            ty,
            value: match value {
                None => value,
                Some(value) => {
                    let (value, _fresh_vars) = mt_expression(FreshVars::new(), *value);
                    Some(Box::new(Expr::Block(Box::new(value))))
                }
            },
        },
        TopLevelItem::Definition(FunDefinition {
            name,
            ty_params,
            where_predicates,
            signature_and_body,
            is_dead_code,
        }) => TopLevelItem::Definition(FunDefinition {
            name,
            ty_params,
            where_predicates,
            signature_and_body: mt_fn_sig_and_body(signature_and_body),
            is_dead_code,
        }),
        TopLevelItem::TypeAlias { .. } => item,
        TopLevelItem::TypeEnum { .. } => item,
        TopLevelItem::TypeStructStruct { .. } => item,
        TopLevelItem::TypeStructTuple { .. } => item,
        TopLevelItem::TypeStructUnit { .. } => item,
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
            predicates,
            bounds,
            body,
        } => TopLevelItem::Trait {
            name,
            ty_params,
            predicates,
            bounds,
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
        TopLevelItem::Error(_) => item,
    }
}

pub fn mt_top_level(top_level: TopLevel) -> TopLevel {
    TopLevel(top_level.0.into_iter().map(mt_top_level_item).collect())
}

impl FunDefinition {
    fn to_doc<'a>(&'a self, extra_data: Option<&'a TopLevelItem>) -> Doc<'a> {
        let types_for_f = types_for_f(extra_data);

        group([
            if self.is_dead_code {
                concat([
                    coq::Comment::new("#[allow(dead_code)] - function was ignored by the compiler")
                        .to_doc(),
                    hardline(),
                ])
            } else {
                nil()
            },
            // Printing instance of DoubleColon Class for [f]
            // (fmt;  #[derive(Debug)]; Struct std::fmt::Formatter)
            if ((&self.name) == "fmt") && is_extra(extra_data) {
                match &self.signature_and_body.body {
                    Some(body) => group([
                        nest([
                            text("Parameter "),
                            body.parameter_name_for_fmt(),
                            text(" : "),
                            // get type of argument named f
                            // (see: https://doc.rust-lang.org/std/fmt/struct.Formatter.html)
                            concat(self.signature_and_body.args.iter().map(|(name, ty)| {
                                if name == "f" {
                                    ty.to_doc_tuning(false)
                                } else {
                                    nil()
                                }
                            })),
                            text(" -> "),
                            types_for_f,
                            self.signature_and_body.ret_ty.to_doc(false),
                            text("."),
                        ]),
                        hardline(),
                        hardline(),
                        nest([
                            text("Global Instance Deb_"),
                            body.parameter_name_for_fmt(),
                            text(" : "),
                            Path::new(&["Notation", "DoubleColon"]).to_doc(),
                            line(),
                            concat(self.signature_and_body.args.iter().map(|(name, ty)| {
                                if name == "f" {
                                    ty.to_doc_tuning(false)
                                } else {
                                    nil()
                                }
                            })),
                            text(" \""),
                            body.parameter_name_for_fmt(),
                            text("\""),
                            text(" := "),
                            text("{"),
                            line(),
                            nest([
                                Path::new(&["Notation", "double_colon"]).to_doc(),
                                text(" := "),
                                body.parameter_name_for_fmt(),
                                text(";"),
                                line(),
                            ]),
                            text("}."),
                        ]),
                        hardline(),
                        hardline(),
                    ]),
                    None => nil(),
                }
            } else {
                nil()
            },
            match &self.signature_and_body.body {
                None => concat([
                    // if the return type is opaque define a corresponding opaque type
                    // @TODO: use also the parameter
                    if self.signature_and_body.ret_ty.has_opaque_types() {
                        concat([
                            nest([
                                text("Parameter"),
                                line(),
                                text([&self.name, "_", "ret_ty"].concat()),
                                line(),
                                text(":"),
                                line(),
                                text("Set."),
                            ]),
                            hardline(),
                        ])
                    } else {
                        nil()
                    },
                    nest([nest([
                        nest([
                            text("Parameter"),
                            line(),
                            text(&self.name),
                            line(),
                            text(":"),
                            line(),
                        ]),
                        nest([
                            text("forall"),
                            line(),
                            monadic_typeclass_parameter(),
                            text(","),
                        ]),
                        line(),
                        // Type parameters a, b, c... compiles to forall {a : Set} {b : Set} ...,
                        {
                            let ty_params = &self.ty_params;
                            if ty_params.is_empty() {
                                nil()
                            } else {
                                concat([
                                    text("forall"),
                                    line(),
                                    nest([intersperse(
                                        ty_params.iter().map(|t| {
                                            concat([text("{"), text(t), text(" : "), text("Set}")])
                                        }),
                                        [line()],
                                    )]),
                                    text(","),
                                    line(),
                                ])
                            }
                        },
                        // where predicates types
                        {
                            let where_predicates = &self.where_predicates;
                            concat(where_predicates.iter().map(|predicate| {
                                nest([
                                    text("forall"),
                                    line(),
                                    predicate.to_doc(),
                                    text(","),
                                    line(),
                                ])
                            }))
                        },
                        // argument types
                        concat(
                            self.signature_and_body
                                .args
                                .iter()
                                .map(|(_, ty)| concat([ty.to_doc(false), text(" ->"), line()])),
                        ),
                        // return type
                        if self.signature_and_body.ret_ty.has_opaque_types() {
                            let ret_ty_name = [&self.name, "_", "ret_ty"].concat();
                            let ret_ty = &mut self.signature_and_body.ret_ty.clone();
                            ret_ty.subst_opaque_types(&ret_ty_name);
                            ret_ty.to_doc(false)
                        } else {
                            self.signature_and_body.ret_ty.to_doc(false)
                        },
                        text("."),
                    ])]),
                ]),
                Some(body) => nest([
                    nest([
                        nest([text("Definition"), line(), text(&self.name)]),
                        line(),
                        monadic_typeclass_parameter(),
                        {
                            let ty_params = &self.ty_params;
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
                        },
                        line(),
                        {
                            let where_predicates = &self.where_predicates;
                            concat(
                                where_predicates
                                    .iter()
                                    .map(|predicate| concat([predicate.to_doc(), line()])),
                            )
                        },
                        concat(self.signature_and_body.args.iter().map(|(name, ty)| {
                            concat([
                                nest([
                                    text("("),
                                    text(name),
                                    line(),
                                    text(":"),
                                    line(),
                                    ty.to_doc(false),
                                    text(")"),
                                ]),
                                line(),
                            ])
                        })),
                        nest([
                            text(":"),
                            line(),
                            // @TODO: improve for opaque types with trait bounds
                            self.signature_and_body.ret_ty.to_doc(false),
                            text(" :="),
                        ]),
                    ]),
                    line(),
                    body.to_doc(false),
                    text("."),
                ]),
            },
        ])
    }
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
                    line(),
                    monadic_typeclass_parameter(),
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

    fn to_doc<'a>(&'a self, extra_data: &Option<&'a TopLevelItem>) -> Doc<'a> {
        match self {
            ImplItem::Const {
                name,
                body,
                is_dead_code,
            } => concat([
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
                    text(" := "),
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
                definition,
                is_method,
            } => concat([
                definition.to_doc(*extra_data),
                hardline(),
                hardline(),
                if *is_method {
                    concat([Self::class_instance_to_doc(
                        "Method",
                        &definition.name,
                        "Notation.Dot",
                        "Notation.dot",
                    )])
                } else {
                    Self::class_instance_to_doc(
                        "AssociatedFunction",
                        &definition.name,
                        "Notation.DoubleColon Self",
                        "Notation.double_colon",
                    )
                },
            ]),
            ImplItem::Type { name, ty } => nest([
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

impl WherePredicate {
    /// turns the predicate into its representation as constraint
    fn to_doc(&self) -> Doc {
        self.bound.to_doc(self.ty.to_doc(true))
    }
}

impl TraitBound {
    /// turns the trait bound into its representation as constraint
    fn to_doc<'a>(&'a self, self_doc: Doc<'a>) -> Doc<'a> {
        nest([
            text("`{"),
            self.name.to_doc(),
            text(".Trait"),
            line(),
            self_doc,
            if self.ty_params.is_empty() {
                nil()
            } else {
                concat([
                    line(),
                    intersperse(
                        self.ty_params
                            .iter()
                            .map(|ty_param| ty_param.to_doc())
                            .collect::<Vec<_>>(),
                        [line()],
                    ),
                ])
            },
            text("}"),
        ])
    }
}

impl TraitTyParamValue {
    fn to_doc(&self) -> Doc {
        match self {
            TraitTyParamValue::ValWithDef { name, ty } => apply_argument(
                name,
                concat([text("(Some"), line(), ty.to_doc(false), text(")")]),
            ),
            TraitTyParamValue::JustValue { name, ty } => apply_argument(name, ty.to_doc(false)),
            TraitTyParamValue::JustDefault { name } => apply_argument(name, text("None")),
        }
    }
}

impl TopLevelItem {
    fn to_doc<'a>(&'a self, extra_data: &Option<&'a TopLevelItem>) -> Doc {
        match self {
            TopLevelItem::Const { name, ty, value } => match value {
                None => nest([
                    nest([text("Parameter"), line(), text(name), text(" :")]),
                    line(),
                    text("forall "),
                    monadic_typeclass_parameter(),
                    text(","),
                    line(),
                    ty.to_doc(false),
                    text("."),
                ]),
                Some(value) => nest([
                    nest([
                        text("Definition"),
                        line(),
                        text(name),
                        line(),
                        monadic_typeclass_parameter(),
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
            },
            TopLevelItem::Definition(definition) => definition.to_doc(*extra_data),
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
            TopLevelItem::TypeAlias {
                name,
                ty,
                ty_params,
            } => nest([
                nest([
                    text("Definition"),
                    line(),
                    text(name),
                    if ty_params.is_empty() {
                        nil()
                    } else {
                        concat([
                            line(),
                            text("("),
                            concat(ty_params.iter().map(|ty| concat([text(ty), line()]))),
                            text(":"),
                            line(),
                            text("Set)"),
                        ])
                    },
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
                            module(
                                name,
                                vec![coq::TopLevelItem::Code(
                                    locally_unset_primitive_projections(&concat([
                                        nest([
                                            text("Record"),
                                            line(),
                                            text("t"),
                                            line(),
                                            text(":"),
                                            line(),
                                            text("Set"),
                                            line(),
                                            text(":="),
                                            line(),
                                            text("{"),
                                        ]),
                                        if fields.is_empty() {
                                            text(" ")
                                        } else {
                                            concat([
                                                nest([
                                                    hardline(),
                                                    intersperse(
                                                        fields.iter().map(|(name, ty)| {
                                                            nest([
                                                                text(name),
                                                                line(),
                                                                text(":"),
                                                                line(),
                                                                ty.to_doc(false),
                                                                text(";"),
                                                            ])
                                                        }),
                                                        [hardline()],
                                                    ),
                                                ]),
                                                hardline(),
                                            ])
                                        },
                                        text("}."),
                                    ])),
                                )],
                            ),
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
                ty_params,
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
                module(
                    name,
                    vec![coq::TopLevelItem::add_context_in_section_if_necessary(
                        name,
                        ty_params,
                        group([
                            text("Unset Primitive Projections."),
                            hardline(),
                            nest([
                                text("Record"),
                                line(),
                                text("t"),
                                line(),
                                text(":"),
                                line(),
                                text("Set"),
                                line(),
                                text(":="),
                                line(),
                                text("{"),
                            ]),
                            if fields.is_empty() {
                                text(" ")
                            } else {
                                concat([
                                    nest([
                                        hardline(),
                                        intersperse(
                                            fields.iter().map(|(name, ty)| {
                                                nest([
                                                    text(name),
                                                    line(),
                                                    text(":"),
                                                    line(),
                                                    ty.to_doc(false),
                                                    text(";"),
                                                ])
                                            }),
                                            [hardline()],
                                        ),
                                    ]),
                                    hardline(),
                                ])
                            },
                            text("}."),
                            hardline(),
                            text("Global Set Primitive Projections."),
                            // gy@TODO: I think the below code blocks, since { and } are not at the same level, can be
                            // optimized. I will work on eliminating redundant wrappers...
                            if !fields.is_empty() {
                                concat([
                                    hardline(),
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
                                ])
                            } else {
                                nil()
                            },
                        ]),
                    )],
                ),
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
                    text("@"),
                    text(name),
                    text("."),
                    text("t"),
                    text("."),
                ]),
            ]),
            TopLevelItem::TypeStructTuple {
                name,
                ty_params,
                fields,
            } => group([
                module(
                    name,
                    vec![coq::TopLevelItem::add_context_in_section_if_necessary(
                        name,
                        ty_params,
                        group([
                            text("Unset Primitive Projections."),
                            hardline(),
                            nest([
                                text("Record"),
                                line(),
                                text("t"),
                                line(),
                                text(":"),
                                line(),
                                text("Set"),
                                line(),
                                text(":="),
                                line(),
                                text("{"),
                            ]),
                            if fields.is_empty() {
                                text(" ")
                            } else {
                                concat([
                                    nest([
                                        hardline(),
                                        intersperse(
                                            fields.iter().map(|ty| {
                                                nest([
                                                    text("_ :"),
                                                    line(),
                                                    ty.to_doc(false),
                                                    text(";"),
                                                ])
                                            }),
                                            [hardline()],
                                        ),
                                    ]),
                                    hardline(),
                                ])
                            },
                            text("}."),
                            hardline(),
                            text("Global Set Primitive Projections."),
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
                    )],
                ),
                hardline(),
                nest([
                    text("Definition"),
                    line(),
                    text(name),
                    line(),
                    text(":="),
                    line(),
                    text("@"),
                    text(name),
                    text(".t."),
                ]),
            ]),
            TopLevelItem::TypeStructUnit { name, ty_params } => group([
                module(
                    name,
                    vec![coq::TopLevelItem::add_context_in_section_if_necessary(
                        name,
                        ty_params,
                        group([
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
                    )],
                ),
                hardline(),
                nest([
                    text("Definition"),
                    line(),
                    text(name),
                    line(),
                    text(":="),
                    line(),
                    text("@"),
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
                    text("Impl_"),
                    text(self_ty.to_name()),
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
                        concat(
                            items.iter().map(|item| {
                                concat([hardline(), hardline(), item.to_doc(extra_data)])
                            }),
                        ),
                    ]),
                    hardline(),
                    nest([text("End"), line(), module_name, text(".")]),
                ])
            }
            TopLevelItem::Trait {
                name,
                ty_params,
                predicates,
                bounds,
                body,
            } => coq::TopLevelItem::Module(coq::Module::trait_module(
                name,
                &ty_params
                    .iter()
                    .map(|(ty, default)| {
                        (
                            ty.to_owned(),
                            default.as_ref().map(|default| default.to_doc(true)),
                        )
                    })
                    .collect::<Vec<_>>(),
                &predicates
                    .iter()
                    .map(|predicate| predicate.to_doc())
                    .collect::<Vec<_>>(),
                &bounds
                    .iter()
                    .map(|bound| bound.to_doc(text("Self")))
                    .collect::<Vec<_>>(),
                &body
                    .iter()
                    .filter_map(|(item_name, item)| match item {
                        TraitItem::Definition { .. } => None,
                        TraitItem::DefinitionWithDefault { .. } => None,
                        TraitItem::Type(bounds) => Some((
                            item_name.to_string(),
                            bounds
                                .iter()
                                .map(|bound| bound.to_doc(text(item_name)))
                                .collect(),
                        )),
                    })
                    .collect::<Vec<_>>(),
                body.iter()
                    .map(|(name, item)| match item {
                        TraitItem::Definition {
                            ty_params,
                            where_predicates,
                            ty,
                        } => typeclass_definition_item(
                            name,
                            ty_params,
                            where_predicates
                                .iter()
                                .map(|predicate| predicate.to_doc())
                                .collect::<Vec<Doc>>(),
                            ty.to_doc(false),
                        ),
                        TraitItem::DefinitionWithDefault { .. } => nil(),
                        TraitItem::Type { .. } => typeclass_type_item(name),
                    })
                    .collect(),
                body.iter()
                    .map(|(name, item)| match item {
                        TraitItem::Definition {
                            ty_params,
                            where_predicates,
                            ty: _,
                        } => coq::Instance::new(
                            name,
                            &[
                                coq::ArgSpec::monadic_typeclass_parameter(),
                                coq::ArgSpec::new(
                                    &coq::ArgDecl::Generalized {
                                        idents: vec![],
                                        ty: coq::Expression::Variable(Path::new(&["Trait"])),
                                    },
                                    coq::ArgSpecKind::Explicit,
                                ),
                            ],
                            coq::Expression::Variable(Path::new(&["Notation", "Dot"])),
                            nest([coq::function_header(
                                "Notation.dot",
                                ty_params,
                                where_predicates
                                    .iter()
                                    .map(|predicate| predicate.to_doc())
                                    .collect(),
                                &Vec::<(&String, _)>::new(),
                            )]),
                            text(name),
                        ),
                        TraitItem::Type { .. } => coq::Instance::new(
                            name,
                            &[
                                coq::ArgSpec::new(
                                    &coq::ArgDecl::Normal {
                                        idents: vec![name.to_owned()],
                                        ty: None,
                                    },
                                    coq::ArgSpecKind::Implicit,
                                ),
                                coq::ArgSpec::new(
                                    &coq::ArgDecl::Generalized {
                                        idents: vec![],
                                        ty: coq::Expression::Application {
                                            func: Box::new(coq::Expression::Variable(Path::new(
                                                &["Trait"],
                                            ))),
                                            param: Some(name.to_string()),
                                            arg: Box::new(coq::Expression::Variable(Path::new(&[
                                                name,
                                            ]))),
                                        },
                                    },
                                    coq::ArgSpecKind::Explicit,
                                ),
                            ],
                            coq::Expression::Application {
                                func: Box::new(coq::Expression::Variable(Path::new(&[
                                    "Notation",
                                    "DoubleColonType",
                                ]))),
                                param: None,
                                arg: Box::new(coq::Expression::Variable(Path::new(&["Self"]))),
                            },
                            text("Notation.double_colon_type"),
                            text(name),
                        ),
                        TraitItem::DefinitionWithDefault {
                            ty_params,
                            where_predicates,
                            signature_and_body,
                        } => coq::Instance::new(
                            name,
                            &[
                                coq::ArgSpec::monadic_typeclass_parameter(),
                                coq::ArgSpec::new(
                                    &coq::ArgDecl::Generalized {
                                        idents: vec![],
                                        ty: coq::Expression::Variable(Path::new(&["Trait"])),
                                    },
                                    coq::ArgSpecKind::Explicit,
                                ),
                            ],
                            coq::Expression::Variable(Path::new(&["Notation", "Dot"])),
                            nest([coq::function_header(
                                "Notation.dot",
                                ty_params,
                                where_predicates
                                    .iter()
                                    .map(|predicate| predicate.to_doc())
                                    .collect(),
                                &signature_and_body
                                    .args
                                    .iter()
                                    .map(|(name, ty)| (name, ty.to_doc(false)))
                                    .collect::<Vec<_>>(),
                            )]),
                            group([
                                text("("),
                                match &signature_and_body.body {
                                    None => text("axiom"),
                                    Some(body) => body.to_doc(false),
                                },
                                line(),
                                nest([
                                    text(":"),
                                    line(),
                                    signature_and_body.ret_ty.to_doc(false),
                                    text(")"),
                                ]),
                            ]),
                        ),
                    })
                    .collect(),
            ))
            .to_doc(),
            TopLevelItem::TraitImpl {
                generic_tys,
                ty_params,
                self_ty,
                of_trait,
                items,
                trait_non_default_items,
            } => {
                let module_name = format!("Impl_{}_for_{}", of_trait.to_name(), self_ty.to_name());
                group([
                    nest([text("Module"), line(), text(module_name.clone()), text(".")]),
                    if generic_tys.is_empty() {
                        nil()
                    } else {
                        concat([
                            hardline(),
                            nest([
                                text("Section"),
                                line(),
                                text(module_name.clone()),
                                text("."),
                            ]),
                        ])
                    },
                    nest([
                        hardline(),
                        if generic_tys.is_empty() {
                            nil()
                        } else {
                            concat([
                                nest([
                                    text("Context"),
                                    line(),
                                    nest([
                                        text("{"),
                                        concat(
                                            generic_tys.iter().map(|ty| concat([text(ty), line()])),
                                        ),
                                        text(":"),
                                        line(),
                                        text("Set"),
                                        text("}"),
                                    ]),
                                    text("."),
                                ]),
                                hardline(),
                                hardline(),
                            ])
                        },
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
                        concat(
                            items.iter().map(|item| {
                                concat([item.to_doc(extra_data), hardline(), hardline()])
                            }),
                        ),
                        nest([
                            nest([
                                text("Global Instance I :"),
                                line(),
                                nest([
                                    of_trait.to_doc(),
                                    text(".Trait"),
                                    line(),
                                    text("Self"),
                                    concat(ty_params.iter().map(|ty_param| {
                                        let ty_param = *ty_param.clone();
                                        concat([
                                            line(),
                                            match ty_param {
                                                TraitTyParamValue::ValWithDef { name, ty } => {
                                                    nest([
                                                        text("("),
                                                        text(name),
                                                        line(),
                                                        text(":="),
                                                        line(),
                                                        nest([
                                                            text("(Some"),
                                                            line(),
                                                            ty.to_doc(false),
                                                            text(")"),
                                                            text(")"),
                                                        ]),
                                                    ])
                                                }
                                                TraitTyParamValue::JustValue { name, ty } => {
                                                    nest([
                                                        text("("),
                                                        text(name),
                                                        line(),
                                                        text(":="),
                                                        line(),
                                                        ty.to_doc(false),
                                                        text(")"),
                                                    ])
                                                }
                                                TraitTyParamValue::JustDefault { name } => nest([
                                                    text("("),
                                                    text(name),
                                                    line(),
                                                    text(":="),
                                                    line(),
                                                    text("None"),
                                                    text(")"),
                                                ]),
                                            },
                                        ])
                                    })),
                                ]),
                            ]),
                            text(" :="),
                            if items.is_empty() {
                                concat([
                                    line(),
                                    nest([
                                        of_trait.to_doc(),
                                        text(".Build_Trait"),
                                        line(),
                                        text("_"),
                                    ]),
                                ])
                            } else {
                                text(" {")
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
                                    monadic_typeclass_parameter(),
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
                    if generic_tys.is_empty() {
                        nil()
                    } else {
                        concat([
                            nest([text("End"), line(), text(module_name.clone()), text(".")]),
                            hardline(),
                        ])
                    },
                    nest([text("End"), line(), text(module_name), text(".")]),
                ])
            }
            TopLevelItem::Error(message) => nest([text("Error"), line(), text(message), text(".")]),
        }
    }
}

impl TopLevel {
    // function returns TopLevelItem::TypeStructStruct (comparing name)
    fn find_tli_by_name(&self, self_ty: &CoqType) -> Option<&TopLevelItem> {
        //Option<TopLevelItem> {
        self.0.iter().find(|item_ins| match item_ins {
            TopLevelItem::TypeStructStruct {
                name,
                fields: _,
                is_dead_code: _,
                .. // @TODO should generic parameters be used here?
            } => {
                // check if it is the struct we are looking for
                *name == self_ty.to_item_name()
            }
            _ => false,
        })
    }

    fn to_doc(&self) -> Doc {
        // check if there is a Debug Trait implementation in the code (#[derive(Debug)])
        // for a TopLevelItem::TypeStructStruct (@TODO extend to cover more cases)
        // if "yes" - get both TopLevelItems (Struct itself and TraitImpl for it)
        // in order to have all required data for printing instance for DoubleColon Class

        // We go through whole tree and if we face TraitImpl, we need to save previous item too
        // (the one for which Impl is being printed), in order to have all the extra_data
        intersperse(
            self.0.iter().map(|item| {
                // if item is DeriveDebug, get struct's fields
                match item {
                    TopLevelItem::TraitImpl {
                        generic_tys: _,
                        ty_params: _,
                        self_ty,
                        of_trait,
                        items: _,
                        trait_non_default_items: _,
                    } =>
                    // if item is DeriveDebug we are getting missing datatypes for Struct, and
                    // printing DoubleColon instance for fmt function
                    {
                        // @TODO. below is support for deriveDebug (add code to support more traits)
                        if of_trait.to_name() == "core_fmt_Debug" {
                            let strct = self.find_tli_by_name(self_ty); // self.get_struct_types(self_ty);
                                                                        // add structs types here (for printing)
                            item.to_doc(&strct)
                        } else {
                            // @TODO add more cases (only Derive debug for Struct supported)");
                            // if no DeriveDebug - we just convert item to doc, no extra data required.
                            item.to_doc(&None)
                        }
                    }
                    _ => {
                        // if item is not TopLevelItem::TraitImpl - we just convert item to doc, no extra data required.
                        item.to_doc(&None)
                    }
                }
            }),
            [hardline(), hardline()],
        )
    }

    pub fn to_pretty(&self, width: usize) -> String {
        let mut w = Vec::new();
        self.to_doc().render(width, &mut w).unwrap();
        format!("{}{}\n", HEADER, String::from_utf8(w).unwrap())
    }
}
