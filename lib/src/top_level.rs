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
use std::collections::HashSet;
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
enum TraitItemData {
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
    TypeStructStruct(TypeStructStruct),
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
    Trait(Trait),
    TraitImpl {
        generic_tys: Vec<String>,
        ty_params: Vec<Box<TraitTyParamValue>>,
        self_ty: Box<CoqType>,
        of_trait: Path,
        items: Vec<ImplItem>,
        trait_non_default_items: Vec<(String, bool)>,
        has_predicates_on_assoc_ty: bool,
    },
    Error(String),
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct TypeStructStruct {
    name: String,
    ty_params: Vec<String>,
    predicates: Vec<WherePredicate>,
    fields: Vec<(String, Box<CoqType>)>,
    is_dead_code: bool,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct TraitItem {
    item_name: String,
    item_data: TraitItemData,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct Trait {
    name: String,
    ty_params: Vec<(String, Option<Box<CoqType>>)>,
    predicates: Vec<WherePredicate>,
    bounds: Vec<TraitBound>,
    body: Vec<TraitItem>,
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
fn compile_top_level_item(
    tcx: &TyCtxt,
    env: &mut Env,
    item: &Item,
    path: Path,
) -> Vec<TopLevelItem> {
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
            vec![TopLevelItem::Definition(FunDefinition::compile(
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
            let context = get_full_name(tcx, item.hir_id());
            let mut items: Vec<ItemId> = module.item_ids.to_vec();
            reorder_definitions_inplace(tcx, env, &context, &mut items);
            let items = deduplicate_top_level_items(
                items
                    .iter()
                    .flat_map(|item_id| {
                        let item = tcx.hir().item(*item_id);
                        let path = path.push(&name);
                        compile_top_level_item(tcx, env, item, path)
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
            let predicates = get_where_predicates(tcx, env, generics);

            match body {
                VariantData::Struct(fields, _) => {
                    let fields = fields
                        .iter()
                        .map(|field| (field.ident.name.to_string(), compile_type(env, field.ty)))
                        .collect();
                    vec![TopLevelItem::TypeStructStruct(TypeStructStruct {
                        name,
                        ty_params,
                        predicates,
                        fields,
                        is_dead_code,
                    })]
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
            collect_supertraits(env, generic_bounds, path.push(name.clone()));
            vec![TopLevelItem::Trait(Trait {
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

                        TraitItem {
                            item_name: to_valid_coq_name(item.ident.name.to_string()),
                            item_data: body,
                        }
                    })
                    .collect(),
            })]
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
            let context = get_full_name(tcx, item.hir_id());
            reorder_definitions_inplace(tcx, env, &context, &mut items);
            let items = compile_impl_item_refs(tcx, env, &items, is_dead_code);

            match of_trait {
                Some(trait_ref) => {
                    let rustc_non_default_items: Vec<_> = tcx
                        .associated_items(trait_ref.trait_def_id().unwrap())
                        .in_definition_order()
                        .filter(|item| !item.defaultness(*tcx).has_value())
                        .collect();
                    let trait_non_default_items = rustc_non_default_items
                        .iter()
                        .map(|item| {
                            (
                                item.name.to_string(),
                                item.kind == rustc_middle::ty::AssocKind::Type,
                            )
                        })
                        .collect();
                    let has_predicates_on_assoc_ty = rustc_non_default_items.iter().any(|item| {
                        if let Some(item_id) = item.trait_item_def_id {
                            let trait_item = tcx.hir().get_if_local(item_id);
                            if let Some(trait_item) = trait_item {
                                if let rustc_hir::TraitItemKind::Type(bounds, _) =
                                    trait_item.expect_trait_item().kind
                                {
                                    !bounds.is_empty()
                                } else {
                                    false
                                }
                            } else {
                                false
                            }
                        } else {
                            false
                        }
                    });

                    // Get the generics for the trait
                    let generics = tcx.generics_of(trait_ref.trait_def_id().unwrap());

                    vec![TopLevelItem::TraitImpl {
                        generic_tys,
                        ty_params: get_ty_params_with_default_status(env, generics, trait_ref.path),
                        self_ty,
                        of_trait: compile_path(env, trait_ref.path),
                        items,
                        trait_non_default_items,
                        has_predicates_on_assoc_ty,
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

/// inserts paths of all immediate supertraits of a trait with
/// the given generic_bounds to [env.supertraits]
fn collect_supertraits(env: &mut Env, generic_bounds: &GenericBounds, path: Path) {
    eprintln!("{:?}\n", path);
    let supertraits = generic_bounds
        .iter()
        .filter_map(|generic_bound| match generic_bound {
            GenericBound::Trait(ptraitref, _) => {
                Some(compile_path(env, ptraitref.trait_ref.path))
            },
            // @TODO: should we include GenericBound::LangItemTrait ?
            GenericBound::LangItemTrait { .. }
            // we ignore lifetimes
            | GenericBound::Outlives { .. } => None,
        })
        .collect();
    env.supertraits.insert(path, supertraits);
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
            definition: FunDefinition::compile(
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

/// [compile_generic_bounds] compiles generic bounds
fn compile_generic_bounds(
    tcx: &TyCtxt,
    env: &Env,
    generic_bounds: GenericBounds,
) -> Vec<TraitBound> {
    generic_bounds
        .iter()
        .filter_map(|generic_bound| match generic_bound {
            GenericBound::Trait(ptraitref, _) => Some(TraitBound::compile(tcx, env, ptraitref)),
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

/// computes the list of actual type parameters with their default status
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

/// computes the full list of actual type parameters with their default status
/// (for items other than traits)
fn get_full_ty_params_with_default_status(
    env: &Env,
    generics: &rustc_middle::ty::Generics,
    path: &rustc_hir::Path,
) -> Vec<Box<TraitTyParamValue>> {
    let type_params_name_and_default_status = type_params_name_and_default_status(generics);
    let ty_params = compile_path_ty_params(env, path);
    add_default_status_to_ty_params(&ty_params, &type_params_name_and_default_status)
}

#[allow(dead_code)]
/// computes the full list of actual type parameters
/// (for items other than traits)
pub(crate) fn get_full_ty_params(
    env: &Env,
    generics: &rustc_middle::ty::Generics,
    path: &rustc_hir::Path,
) -> Vec<Box<CoqType>> {
    get_full_ty_params_with_default_status(env, generics, path)
        .into_iter()
        .map(|ty_param| ty_param.to_coq_type())
        .collect()
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
) -> TraitItemData {
    match &item.kind {
        TraitItemKind::Const(ty, _) => TraitItemData::Definition {
            ty_params,
            where_predicates,
            ty: compile_type(env, ty),
        },
        TraitItemKind::Fn(fn_sig, trait_fn) => match trait_fn {
            TraitFn::Required(_) => TraitItemData::Definition {
                ty_params,
                where_predicates,
                ty: compile_fn_decl(env, fn_sig.decl),
            },
            TraitFn::Provided(body_id) => {
                let env_tcx = env.tcx;
                let fn_sig_and_body = get_hir_fn_sig_and_body(&env_tcx, fn_sig, body_id);
                let signature_and_body = compile_fn_sig_and_body(env, &fn_sig_and_body, "arg");
                TraitItemData::DefinitionWithDefault {
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
            TraitItemData::Type(generic_bounds)
        }
    }
}

fn compile_top_level(
    tcx: &TyCtxt,
    opts: TopLevelOptions,
    supertraits_map: &mut HashMap<Path, HashSet<Path>>,
) -> TopLevel {
    let file = opts.filename;
    // the path to the item being compiled
    let path = Path::new(&[file.clone()]);

    let mut env = Env {
        impl_counter: HashMap::new(),
        tcx: *tcx,
        axiomatize: opts.axiomatize,
        file,
        reorder_map: HashMap::new(),
        configuration: get_configuration(&opts.configuration_file),
        supertraits: supertraits_map,
    };

    let mut results: Vec<ItemId> = tcx.hir().items().collect();
    reorder_definitions_inplace(tcx, &mut env, "top_level", &mut results);

    let results = deduplicate_top_level_items(
        results
            .iter()
            .flat_map(|item_id| {
                let item = tcx.hir().item(*item_id);
                compile_top_level_item(tcx, &mut env, item, path.clone())
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
    let mut supertraits_map = HashMap::new();
    let top_level = compile_top_level(tcx, opts, &mut supertraits_map);
    let top_level = mt_top_level(top_level);
    top_level.to_pretty(LINE_WIDTH, &supertraits_map)
}

// additional check. can be eliminated when all possible cases will be covered
fn is_extra(extra_data: Option<&TopLevelItem>) -> bool {
    match extra_data {
        // @TODO this is support for TypeStructStruct,
        // add support for more items
        Some(TopLevelItem::TypeStructStruct(TypeStructStruct {
            name: _,
            fields: _,
            is_dead_code: _,
            ..
        })) => true,
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
            definition,
            is_method,
        } => ImplItem::Definition {
            definition: definition.mt(),
            is_method,
        },
        ImplItem::Type { .. } => item,
    }
}

fn mt_impl_items(items: Vec<ImplItem>) -> Vec<ImplItem> {
    items.into_iter().map(mt_impl_item).collect()
}

impl FnSigAndBody {
    fn mt(self) -> Self {
        FnSigAndBody {
            args: self.args,
            ret_ty: CoqType::monad(mt_ty(self.ret_ty)),
            body: match self.body {
                None => self.body,
                Some(body) => {
                    let (body, _fresh_vars) = mt_expression(FreshVars::new(), *body);
                    Some(Box::new(Expr::Block(Box::new(body))))
                }
            },
        }
    }
}

impl TraitItem {
    fn mt(&self) -> Self {
        TraitItem {
            item_name: self.item_name.to_owned(),
            item_data: match self.item_data.to_owned() {
                TraitItemData::Definition {
                    ty_params,
                    where_predicates,
                    ty,
                } => TraitItemData::Definition {
                    ty_params,
                    where_predicates,
                    ty: mt_ty(ty),
                },
                TraitItemData::Type(x) => TraitItemData::Type(x), // @TODO apply MT
                TraitItemData::DefinitionWithDefault {
                    ty_params,
                    where_predicates,
                    signature_and_body,
                } => TraitItemData::DefinitionWithDefault {
                    ty_params,
                    where_predicates,
                    signature_and_body: signature_and_body.mt(),
                },
            },
        }
    }
}

fn mt_trait_items(body: Vec<TraitItem>) -> Vec<TraitItem> {
    body.into_iter().map(|trait_item| trait_item.mt()).collect()
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
        TopLevelItem::Definition(definiiton) => TopLevelItem::Definition(definiiton.mt()),
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
        TopLevelItem::Trait(Trait {
            name,
            ty_params,
            predicates,
            bounds,
            body,
        }) => TopLevelItem::Trait(Trait {
            name,
            ty_params,
            predicates,
            bounds,
            body: mt_trait_items(body),
        }),
        TopLevelItem::TraitImpl {
            generic_tys,
            ty_params,
            self_ty,
            of_trait,
            items,
            trait_non_default_items,
            has_predicates_on_assoc_ty,
        } => TopLevelItem::TraitImpl {
            generic_tys,
            ty_params,
            self_ty,
            of_trait,
            items: mt_impl_items(items),
            trait_non_default_items,
            has_predicates_on_assoc_ty,
        },
        TopLevelItem::Error(_) => item,
    }
}

pub fn mt_top_level(top_level: TopLevel) -> TopLevel {
    TopLevel(top_level.0.into_iter().map(mt_top_level_item).collect())
}

impl FunDefinition {
    /// compiles a given function
    fn compile(
        env: &mut Env,
        name: &str,
        generics: &rustc_hir::Generics,
        fn_sig_and_body: &HirFnSigAndBody,
        default: &str,
        is_dead_code: bool,
    ) -> Self {
        let tcx = env.tcx;
        FunDefinition {
            name: name.to_owned(),
            ty_params: get_ty_params_names(env, generics),
            where_predicates: get_where_predicates(&tcx, env, generics),
            signature_and_body: compile_fn_sig_and_body(env, fn_sig_and_body, default),
            is_dead_code,
        }
    }

    fn mt(self) -> Self {
        FunDefinition {
            name: self.name,
            ty_params: self.ty_params,
            where_predicates: self.where_predicates,
            signature_and_body: self.signature_and_body.mt(),
            is_dead_code: self.is_dead_code,
        }
    }

    // [types_for_f] is moved here because it is used only in to_coq below
    fn types_for_f(extra_data: Option<&TopLevelItem>) -> Vec<coq::Expression> {
        match extra_data {
            // @TODO this is support for TypeStructStruct,
            // add support for more items
            Some(TopLevelItem::TypeStructStruct(TypeStructStruct {
                name: _,
                fields,
                is_dead_code: _,
                .. // @TODO do generic params should be used here?
            })) => {
                [
                    vec![coq::Expression::just_name("string")],
                    fields
                        .iter()
                        .flat_map(|(_str, boxed_coq_type)| {
                            let nm = boxed_coq_type.to_name();
                            let nn = if nm == *"StaticRef_str" {
                                String::from("string")
                            } else {
                                boxed_coq_type.to_name()
                            };
                            [
                                // print field name
                                coq::Expression::just_name("string"),
                                // print field type
                                coq::Expression::just_name(&nn),
                            ]
                        })
                        .collect(),
                ]
                .concat()
            }
            // @TODO unreachable branch, extend to cover more cases
            _ => vec![],
        }
    }

    fn to_coq<'a>(&'a self, extra_data: Option<&'a TopLevelItem>) -> coq::TopLevel<'a> {
        coq::TopLevel::new(
            &[
                if self.is_dead_code {
                    vec![coq::TopLevelItem::Comment(coq::Comment::new(
                        "#[allow(dead_code)] - function was ignored by the compiler",
                    ))]
                } else {
                    vec![]
                },
                // Printing instance of DoubleColon Class for [f]
                // (fmt;  #[derive(Debug)]; Struct std::fmt::Formatter)
                if ((&self.name) == "fmt") && is_extra(extra_data) {
                    match &self.signature_and_body.body {
                        Some(body) => {
                            let body_parameter_name_for_fmt = body.parameter_name_for_fmt();

                            vec![
                                coq::TopLevelItem::Definition(coq::Definition::new(
                                    &body_parameter_name_for_fmt,
                                    &coq::DefinitionKind::Assumption {
                                        ty: self
                                            .signature_and_body
                                            .ret_ty
                                            .to_coq()
                                            .arrows_from(&FunDefinition::types_for_f(extra_data))
                                            .arrows_from({
                                                // get type of argument named f
                                                // (see: https://doc.rust-lang.org/std/fmt/struct.Formatter.html)
                                                &self
                                                    .signature_and_body
                                                    .args
                                                    .iter()
                                                    .filter_map(|(name, ty)| {
                                                        if name == "f" {
                                                            Some(ty.to_coq_tuning())
                                                        } else {
                                                            None
                                                        }
                                                    })
                                                    .collect::<Vec<_>>()
                                            }),
                                    },
                                )),
                                coq::TopLevelItem::Line,
                                coq::TopLevelItem::Code(nest([
                                    text("Global Instance "),
                                    text(format!("Deb_{body_parameter_name_for_fmt}")),
                                    text(" : "),
                                    Path::new(&["Notation", "DoubleColon"]).to_doc(),
                                    line(),
                                    concat(self.signature_and_body.args.iter().map(
                                        |(name, ty)| {
                                            if name == "f" {
                                                ty.to_coq_tuning().to_doc(false)
                                            } else {
                                                nil()
                                            }
                                        },
                                    )),
                                    text(format!(" \"{body_parameter_name_for_fmt}\"")),
                                    text(" := "),
                                    text("{"),
                                    line(),
                                    nest([
                                        Path::new(&["Notation", "double_colon"]).to_doc(),
                                        text(" := "),
                                        text(body_parameter_name_for_fmt),
                                        text(";"),
                                        line(),
                                    ]),
                                    text("}."),
                                ])),
                                coq::TopLevelItem::Line,
                            ]
                        }
                        None => vec![],
                    }
                } else {
                    vec![]
                },
                match &self.signature_and_body.body {
                    None => {
                        let ret_ty_name = [&self.name, "_", "ret_ty"].concat();
                        let ret_opaque_ty = CoqType::Application {
                            func: CoqType::var("projT1".to_string()),
                            args: vec![CoqType::var(ret_ty_name.clone())],
                        };
                        let opaque_return_tys_bounds =
                            self.signature_and_body.ret_ty.opaque_types_bounds();
                        let bounds_to_definition = |bounds: &Vec<Path>| {
                            coq::TopLevelItem::Definition(coq::Definition::new(
                                &ret_ty_name,
                                &coq::DefinitionKind::Assumption {
                                    ty: coq::Expression::SigmaType {
                                        args: [
                                            vec![coq::ArgDecl::new(
                                                &coq::ArgDeclVar::Simple {
                                                    idents: vec!["Ty".to_string()],
                                                    ty: Some(coq::Expression::Set),
                                                },
                                                coq::ArgSpecKind::Explicit,
                                            )],
                                            bounds
                                                .iter()
                                                .map(|bound| {
                                                    coq::ArgDecl::new(
                                                        &coq::ArgDeclVar::Generalized {
                                                            idents: vec![],
                                                            ty: coq::Expression::Variable {
                                                                ident: Path::concat(&[
                                                                    bound.to_owned(),
                                                                    Path::new(&["Trait"]),
                                                                ]),
                                                                no_implicit: false,
                                                            }
                                                            .apply(&coq::Expression::just_name(
                                                                "Ty",
                                                            )),
                                                        },
                                                        coq::ArgSpecKind::Explicit,
                                                    )
                                                })
                                                .collect::<Vec<_>>(),
                                        ]
                                        .concat(),
                                        image: Box::new(coq::Expression::Unit),
                                    },
                                },
                            ))
                        };
                        // if the return type is opaque define a corresponding opaque type
                        let (ret_ty_defs_vec, ret_ty) =
                            if self.signature_and_body.ret_ty.has_opaque_types() {
                                let ret_ty_defs_vec = opaque_return_tys_bounds
                                    .iter()
                                    .map(bounds_to_definition)
                                    .collect();

                                let ret_ty = &mut self.signature_and_body.ret_ty.clone();
                                ret_ty.subst_opaque_types(&ret_opaque_ty);

                                (ret_ty_defs_vec, ret_ty.to_coq())
                            } else {
                                (vec![], self.signature_and_body.ret_ty.to_coq())
                            };
                        [
                            ret_ty_defs_vec,
                            vec![coq::TopLevelItem::Definition(coq::Definition::new(
                                &self.name,
                                &coq::DefinitionKind::Assumption {
                                    ty: coq::Expression::PiType {
                                        args: [
                                            vec![coq::ArgDecl::monadic_typeclass_parameter()],
                                            // Type parameters a, b, c... compiles to forall {a b c ... : Set},
                                            if self.ty_params.is_empty() {
                                                vec![]
                                            } else {
                                                vec![coq::ArgDecl::of_ty_params(
                                                    &self.ty_params,
                                                    coq::ArgSpecKind::Implicit,
                                                )]
                                            },
                                            // where predicates types
                                            self.where_predicates
                                                .iter()
                                                .map(|predicate| predicate.to_coq())
                                                .collect(),
                                        ]
                                        .concat(),
                                        image: Box::new(
                                            // return type
                                            ret_ty
                                                // argument types
                                                .arrows_from(
                                                    &self
                                                        .signature_and_body
                                                        .args
                                                        .iter()
                                                        .map(|(_, ty)| ty.to_coq())
                                                        .collect::<Vec<_>>(),
                                                ),
                                        ),
                                    },
                                },
                            ))],
                        ]
                        .concat()
                    }
                    Some(body) => vec![coq::TopLevelItem::Definition(coq::Definition::new(
                        &self.name,
                        &coq::DefinitionKind::Alias {
                            args: [
                                vec![coq::ArgDecl::monadic_typeclass_parameter()],
                                // Type parameters a, b, c... compiles to forall {a b c ... : Set},
                                if self.ty_params.is_empty() {
                                    vec![]
                                } else {
                                    vec![coq::ArgDecl::of_ty_params(
                                        &self.ty_params,
                                        coq::ArgSpecKind::Implicit,
                                    )]
                                },
                                // where predicates types
                                self.where_predicates
                                    .iter()
                                    .map(|predicate| predicate.to_coq())
                                    .collect(),
                                // argument types
                                self.signature_and_body
                                    .args
                                    .iter()
                                    .map(|(name, ty)| {
                                        coq::ArgDecl::new(
                                            &coq::ArgDeclVar::Simple {
                                                idents: vec![name.to_owned()],
                                                ty: Some(ty.to_coq()),
                                            },
                                            coq::ArgSpecKind::Explicit,
                                        )
                                    })
                                    .collect(),
                            ]
                            .concat(),
                            // @TODO: improve for opaque types with trait bounds
                            ty: Some(self.signature_and_body.ret_ty.to_coq()),
                            body: coq::Expression::Code(body.to_doc(false)),
                        },
                    ))],
                },
            ]
            .concat(),
        )
    }

    fn to_doc<'a>(&'a self, extra_data: Option<&'a TopLevelItem>) -> Doc<'a> {
        self.to_coq(extra_data).to_doc()
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
                    line(),
                    monadic_typeclass_parameter(),
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
    fn to_coq(&self) -> coq::ArgDecl {
        self.bound
            .to_coq(self.ty.to_coq(), coq::ArgSpecKind::Implicit)
    }
}

impl TraitBound {
    /// Get the generics for the trait
    fn compile(tcx: &TyCtxt, env: &Env, ptraitref: &rustc_hir::PolyTraitRef) -> Self {
        TraitBound {
            name: compile_path(env, ptraitref.trait_ref.path),
            ty_params: get_ty_params_with_default_status(
                env,
                tcx.generics_of(ptraitref.trait_ref.trait_def_id().unwrap()),
                ptraitref.trait_ref.path,
            ),
        }
    }

    /// turns the trait bound into its representation as constraint
    fn to_coq<'a>(&self, self_ty: coq::Expression<'a>, kind: coq::ArgSpecKind) -> coq::ArgDecl<'a> {
        coq::ArgDecl::new(
            &coq::ArgDeclVar::Generalized {
                idents: vec![],
                ty: coq::Expression::Application {
                    func: Box::new(
                        coq::Expression::Variable {
                            ident: Path::concat(&[self.name.to_owned(), Path::new(&["Trait"])]),
                            no_implicit: false,
                        }
                        .apply(&self_ty),
                    ),
                    args: self
                        .ty_params
                        .iter()
                        .map(|ty_param| ty_param.to_coq_arg_value(&self.name))
                        .collect(),
                },
            },
            kind,
        )
    }
}

impl TraitTyParamValue {
    fn to_coq_arg_value<'a>(&self, bound_name: &Path) -> (Option<String>, coq::Expression<'a>) {
        match self {
            TraitTyParamValue::JustValue { name, ty }
            | TraitTyParamValue::ValWithDef { name, ty } => (Some(name.to_owned()), ty.to_coq()),
            TraitTyParamValue::JustDefault { name } => (
                Some(name.clone()),
                coq::Expression::single_var(&Path::concat(&[
                    bound_name.to_owned(),
                    Path::new(&["Default", name]),
                ]))
                .apply(&coq::Expression::just_name("Self")),
            ),
        }
    }
}

impl TraitTyParamValue {
    #[allow(dead_code)] // @TODO
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

    fn to_coq_type(&self) -> Box<CoqType> {
        match self {
            TraitTyParamValue::JustValue { name: _, ty } => ty.to_owned(),
            TraitTyParamValue::ValWithDef { name: _, ty } => ty.to_owned(),
            TraitTyParamValue::JustDefault { name: _ } => CoqType::var("None".to_string()),
        }
    }
}

struct ToDocContext<'a, 'b> {
    extra_data: Option<&'a TopLevelItem>,
    previous_module_names: Vec<String>,
    supertraits_map: &'b HashMap<Path, HashSet<Path>>,
}

impl TopLevelItem {
    fn to_doc<'a>(&'a self, to_doc_context: ToDocContext<'a, '_>) -> Doc {
        match self {
            TopLevelItem::Const { name, ty, value } => match value {
                None => coq::TopLevel::new(&[
                    coq::TopLevelItem::Definition(coq::Definition::new(
                        name,
                        &coq::DefinitionKind::Assumption {
                            ty: coq::Expression::PiType {
                                args: vec![coq::ArgDecl::monadic_typeclass_parameter()],
                                image: Box::new(ty.to_coq()),
                            },
                        },
                    )),
                ])
                .to_doc(),
                Some(value) => coq::TopLevel::new(&[
                    coq::TopLevelItem::Definition(coq::Definition::new(
                        name,
                        &coq::DefinitionKind::Alias {
                            args: vec![coq::ArgDecl::monadic_typeclass_parameter()],
                            ty: Some(ty.to_coq()),
                            body: coq::Expression::Code(nest([
                                text("run"),
                                line(),
                                // We have to force the parenthesis because otherwise they
                                // are lost when printing a statement in the expression
                                text("("),
                                value.to_doc(true),
                                text(")"),
                            ])),
                        },
                    )),
                ])
                .to_doc(),
            },
            TopLevelItem::Definition(definition) => definition.to_doc(to_doc_context.extra_data),
            TopLevelItem::Module {
                name,
                body,
                is_dead_code,
            } => {
                let nb_previous_occurrences_of_module_name =
                    to_doc_context.previous_module_names.iter().filter(|&current_name| current_name == name).count();
                coq::TopLevel::new(
                    &[
                        if *is_dead_code {
                            vec![coq::TopLevelItem::Comment(coq::Comment::new(
                                "#[allow(dead_code)] - module was ignored by the compiler",
                            ))]
                        } else {
                            vec![]
                        },
                        vec![coq::TopLevelItem::Module(coq::Module::new_with_repeat(
                            name,
                            nb_previous_occurrences_of_module_name,
                            coq::TopLevel::new(&[coq::TopLevelItem::Code(body.to_doc(to_doc_context.supertraits_map))]),
                        ))],
                    ]
                    .concat(),
                )
                .to_doc()
            },
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
                    concat(variants.iter().map(|(name, fields)| {
                        match fields {
                            VariantItem::Tuple { .. } => nil(),
                            VariantItem::Struct { fields } => concat([
                                coq::Module::new(
                                    name,
                                    coq::TopLevel::locally_unset_primitive_projections(&[
                                        coq::TopLevelItem::Code(concat([
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
                                    ]),
                                )
                                .to_doc(),
                                hardline(),
                                hardline(),
                            ]),
                        }
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
            TopLevelItem::TypeStructStruct(tss) => tss.to_doc(),
            TopLevelItem::TypeStructTuple {
                name,
                ty_params,
                fields,
            } => group([
                coq::TopLevel::new(&[
                    coq::TopLevelItem::Module(coq::Module::new(
                        name,
                        coq::TopLevel::add_context_in_section_if_necessary(
                            name,
                            ty_params,
                            &coq::TopLevel::concat(&[
                                coq::TopLevel::locally_unset_primitive_projections(&[
                                    coq::TopLevelItem::Record(coq::Record::new(
                                        "t",
                                        &coq::Expression::Set,
                                        &fields
                                            .iter()
                                            .map(|ty| coq::FieldDef::new(&None, &ty.to_coq()))
                                            .collect::<Vec<_>>(),
                                    )),
                                ]),
                                coq::TopLevel::new(&[coq::TopLevelItem::Line]),
                                coq::TopLevel::new(
                                    &fields
                                        .iter()
                                        .enumerate()
                                        .map(|(i, _)| {
                                            coq::TopLevelItem::Instance(coq::Instance::new(
                                                false,
                                                &format!("Get_{i}"),
                                                &[],
                                                coq::Expression::Variable {
                                                    ident: Path::new(&["Notation", "Dot"]),
                                                    no_implicit: false,
                                                }
                                                .apply(&coq::Expression::just_name(&i.to_string())),
                                                &Some(coq::Expression::Record {
                                                    fields: vec![coq::Field::new(
                                                        &Path::new(&["Notation", "dot"]),
                                                        &[coq::ArgDecl::new(
                                                            &coq::ArgDeclVar::Destructured {
                                                                pattern: coq::Expression::just_name("Build_t")
                                                                    .apply_many(
                                                                        &fields
                                                                            .iter()
                                                                            .enumerate()
                                                                            .map(|(j, _)| if i == j {
                                                                                coq::Expression::just_name(&format!("x{j}"))
                                                                            } else {
                                                                                coq::Expression::Wild
                                                                            }
                                                                        )
                                                                        .collect::<Vec<_>>(),
                                                                    ),
                                                            },
                                                            coq::ArgSpecKind::Explicit,
                                                        )],
                                                        &coq::Expression::just_name(&format!("x{i}")),
                                                    )],
                                                }),
                                                vec![],
                                            ))
                                        })
                                        .collect::<Vec<_>>(),
                                ),
                            ]),
                        ),
                    )),
                    coq::TopLevelItem::Definition(coq::Definition::new(
                        name,
                        &coq::DefinitionKind::Alias {
                            args: vec![],
                            ty: None,
                            body: coq::Expression::Variable {
                                ident: Path::new(&[name, &"t".to_string()]),
                                no_implicit: true,
                            },
                        },
                    )),
                ])
                .to_doc(),
            ]),
            TopLevelItem::TypeStructUnit { name, ty_params } => coq::TopLevel::new(&[
                coq::TopLevelItem::Module(coq::Module::new(
                    name,
                    coq::TopLevel::add_context_in_section_if_necessary(
                        name,
                        ty_params,
                        &coq::TopLevel::new(&[coq::TopLevelItem::Code(group([
                            nest([
                                text("Inductive"),
                                line(),
                                text("t"),
                                line(),
                                nest([text(":"), line(), text("Set"), text(" :=")]),
                            ]),
                            line(),
                            nest([text("Build"), text(".")]),
                        ]))]),
                    ),
                )),
                coq::TopLevelItem::Definition(coq::Definition::new(
                    name,
                    &coq::DefinitionKind::Alias {
                        args: vec![],
                        ty: None,
                        body: coq::Expression::Variable {
                            ident: Path::new(&[name, &"t".to_string()]),
                            no_implicit: true,
                        },
                    },
                )),
            ])
            .to_doc(),
            TopLevelItem::Impl {
                self_ty,
                counter,
                items,
            } => {
                let message = self_ty.to_name();
                let module_name = if *counter != 1 {
                    format!("Impl_{message}_{counter}")
                } else {
                    format!("Impl_{message}")
                };
                coq::TopLevel::new(&[coq::TopLevelItem::Module(coq::Module::new(
                    &module_name,
                    coq::TopLevel::concat(&[
                        coq::TopLevel::new(&[coq::TopLevelItem::Definition(coq::Definition::new(
                            "Self",
                            &coq::DefinitionKind::Alias {
                                args: vec![],
                                ty: None,
                                body: self_ty.to_coq(),
                            },
                        ))]),
                        coq::TopLevel::new(
                            &items
                                .iter()
                                .flat_map(|item| {
                                    [
                                        coq::TopLevelItem::Line,
                                        coq::TopLevelItem::Code(concat([item.to_doc(&to_doc_context.extra_data)])),
                                    ]
                                })
                                .collect::<Vec<_>>(),
                        ),
                    ]),
                ))])
                .to_doc()
            }
            TopLevelItem::Trait(tr) => tr.to_doc(to_doc_context.supertraits_map),
            TopLevelItem::TraitImpl {
                generic_tys,
                ty_params,
                self_ty,
                of_trait,
                items,
                trait_non_default_items,
                has_predicates_on_assoc_ty,
            } => {
                let module_name = format!("Impl_{}_for_{}", of_trait.to_name(), self_ty.to_name());
                coq::Module::new(
                    &module_name,
                    coq::TopLevel::concat(&[
                        coq::TopLevel::add_context_in_section_if_necessary(
                            &module_name,
                            generic_tys,
                            &coq::TopLevel::new(&[
                                vec![
                                    coq::TopLevelItem::Definition(coq::Definition::new(
                                        "Self",
                                        &coq::DefinitionKind::Alias {
                                            args: vec![],
                                            ty: None,
                                            body: self_ty.to_coq(),
                                        },
                                    )),
                                    coq::TopLevelItem::Line,
                                ],
                                items
                                    .iter()
                                    .map(|item| {
                                        vec![
                                            coq::TopLevelItem::Code(item.to_doc(&to_doc_context.extra_data)),
                                            coq::TopLevelItem::Line,
                                        ]
                                    })
                                    .concat(),
                                vec![coq::TopLevelItem::Instance(coq::Instance::new(
                                    *has_predicates_on_assoc_ty,
                                    "I",
                                    &[],
                                    coq::Expression::Variable {
                                        ident: Path::concat(&[
                                            of_trait.to_owned(),
                                            Path::new(&["Trait"]),
                                        ]),
                                        no_implicit: false,
                                    }
                                    .apply(&coq::Expression::just_name("Self"))
                                    .apply_many_args(
                                        &ty_params
                                            .iter()
                                            .map(|ty_param| {
                                                let ty_param = *ty_param.clone();
                                                match ty_param {
                                                    TraitTyParamValue::JustValue { name, ty } | TraitTyParamValue::ValWithDef { name, ty } => {
                                                        (Some(name), ty.to_coq())
                                                    }
                                                    TraitTyParamValue::JustDefault { name } => (
                                                        Some(name.clone()),
                                                        coq::Expression::Code(
                                                            concat([of_trait.to_doc(), text(".Default."), text(name)])
                                                        ).apply(&coq::Expression::just_name("Self")
                                                        ),
                                                    ),
                                                }
                                            })
                                            .collect::<Vec<_>>(),
                                    ),
                                    &Some(if items.is_empty() {
                                        coq::Expression::Variable {
                                            ident: Path::concat(&[
                                                of_trait.to_owned(),
                                                Path::new(&["Build_Trait"]),
                                            ]),
                                            no_implicit: false,
                                        }
                                        .apply(&coq::Expression::Wild)
                                    } else {
                                        coq::Expression::Record {
                                            fields: trait_non_default_items
                                                .iter()
                                                .map(|(name, is_type)| {
                                                    coq::Field::new(
                                                        &Path::concat(&[of_trait.to_owned(), Path::new(&[name])]),
                                                        &if *is_type {
                                                            vec![]
                                                        } else {
                                                            vec![coq::ArgDecl::monadic_typeclass_parameter()]
                                                        },
                                                        &coq::Expression::just_name(name),
                                                    )
                                                })
                                                .collect::<Vec<_>>(),
                                        }
                                    }),
                                    if *has_predicates_on_assoc_ty {
                                        vec![text("eauto.")]
                                    } else {
                                        vec![]
                                    },
                                ))],
                            ]
                            .concat()),
                        ),
                        coq::TopLevel::new(&[coq::TopLevelItem::Hint(
                            coq::Hint::standard_resolve(),
                        )]),
                    ]),
                )
                .to_doc()
            }
            TopLevelItem::Error(message) => nest([text("Error"), line(), text(message), text(".")]),
        }
    }
}

impl TypeStructStruct {
    fn to_doc(&self) -> Doc {
        let TypeStructStruct {
            name,
            ty_params,
            predicates,
            fields,
            is_dead_code,
        } = self;

        // making fields mutable to extract trait objects from the types
        let mut fields = fields.clone();
        let trait_objects_traits: HashSet<_> = fields
            .iter_mut()
            .flat_map(|(_, ty)| ty.collect_and_subst_trait_objects())
            .collect();

        // making fields immutable, just in case
        let fields = fields;

        coq::TopLevel::new(
            &[
                if *is_dead_code {
                    vec![coq::TopLevelItem::Comment(coq::Comment::new(
                        "#[allow(dead_code)] - struct was ignored by the compiler",
                    ))]
                } else {
                    vec![]
                },
                vec![
                    coq::TopLevelItem::Module(coq::Module::new(
                        name,
                        coq::TopLevel::add_context_in_section_if_necessary(
                            name,
                            ty_params,
                            &coq::TopLevel::concat(&[
                                coq::TopLevel::new(&if predicates.is_empty() {
                                    vec![]
                                } else {
                                    vec![coq::TopLevelItem::Context(coq::Context::new(
                                        &predicates
                                            .iter()
                                            .map(|predicate| predicate.to_coq())
                                            .collect::<Vec<_>>(),
                                    ))]
                                }),
                                coq::TopLevel::new(&if trait_objects_traits.is_empty() {
                                    vec![]
                                } else {
                                    trait_objects_traits
                                        .iter()
                                        .flat_map(|single_trait_object_traits| {
                                            let trait_object_name =
                                                &CoqType::trait_object_to_name(
                                                    single_trait_object_traits,
                                                );
                                            [
                                                coq::TopLevelItem::Module(coq::Module::new(
                                                    trait_object_name,
                                                    coq::TopLevel::new(&[
                                                        vec![coq::TopLevelItem::Definition(
                                                            coq::Definition::new(
                                                                "t",
                                                                &coq::DefinitionKind::Assumption {
                                                                    ty: coq::Expression::Set,
                                                                },
                                                            ),
                                                        )],
                                                        single_trait_object_traits
                                                            .iter()
                                                            .map(|single_trait_object_trait| {
                                                                coq::TopLevelItem::Instance(
                                                                    coq::Instance::new(
                                                                        false,
                                                                        &[
                                                                            "I_",
                                                                            &single_trait_object_trait.to_name(),
                                                                        ]
                                                                        .concat(),
                                                                        &[],
                                                                        coq::Expression::Variable {
                                                                            ident: Path::concat(&[
                                                                                single_trait_object_trait.to_owned(),
                                                                                Path::new(&["Trait"]),
                                                                            ]),
                                                                            no_implicit: false,
                                                                        }
                                                                        .apply(&coq::Expression::just_name("t")),
                                                                        &Some(coq::Expression::just_name("axiom")),
                                                                        vec![],
                                                                    ),
                                                                )
                                                            })
                                                            .collect(),
                                                        vec![coq::TopLevelItem::Definition(coq::Definition::new(
                                                            "conv_Dyn",
                                                            &coq::DefinitionKind::Assumption {
                                                                ty: coq::Expression::PiType {
                                                                    args: [
                                                                        vec![coq::ArgDecl::new(
                                                                            &coq::ArgDeclVar::Simple {
                                                                                idents: vec!["A".to_string()],
                                                                                ty: Some(coq::Expression::Set),
                                                                            },
                                                                            coq::ArgSpecKind::Implicit,
                                                                        )],
                                                                        single_trait_object_traits
                                                                            .iter()
                                                                            .map(|single_trait_object_trait| {
                                                                                coq::ArgDecl::new(
                                                                                    &coq::ArgDeclVar::Generalized {
                                                                                        idents: vec![],
                                                                                        ty: coq::Expression::Variable {
                                                                                            ident: Path::concat(&[
                                                                                                single_trait_object_trait.to_owned(),
                                                                                                Path::new(&["Trait"]),
                                                                                            ]),
                                                                                            no_implicit: false,
                                                                                        }
                                                                                        .apply(&coq::Expression::just_name("t")),
                                                                                    },
                                                                                    coq::ArgSpecKind::Implicit,
                                                                                )
                                                                            })
                                                                            .collect()
                                                                    ]
                                                                    .concat(),
                                                                    image: Box::new(
                                                                        coq::Expression::just_name("t")
                                                                            .arrows_from(&[
                                                                                coq::Expression::just_name("A"),
                                                                            ]),
                                                                    ),
                                                                },
                                                            },
                                                        ))],
                                                    ].concat()),
                                                )),
                                                coq::TopLevelItem::Definition(
                                                    coq::Definition::new(
                                                        trait_object_name,
                                                        &coq::DefinitionKind::Alias {
                                                            args: vec![],
                                                            ty: Some(coq::Expression::Set),
                                                            body: coq::Expression::Variable {
                                                                ident: Path::new(&[
                                                                    trait_object_name.as_ref(),
                                                                    "t",
                                                                ]),
                                                                no_implicit: false,
                                                            },
                                                        },
                                                    ),
                                                ),
                                                coq::TopLevelItem::Line,
                                            ]
                                        })
                                        .collect()
                                }),
                                coq::TopLevel::locally_unset_primitive_projections(&[
                                    coq::TopLevelItem::Record(coq::Record::new(
                                        "t",
                                        &coq::Expression::Set,
                                        &fields
                                            .iter()
                                            .map(|(name, ty)| {
                                                coq::FieldDef::new(
                                                    &Some(name.to_owned()),
                                                    &ty.to_coq(),
                                                )
                                            })
                                            .collect::<Vec<_>>(),
                                    )),
                                ]),
                                coq::TopLevel::new(&if fields.is_empty() {
                                    vec![]
                                } else {
                                    vec![coq::TopLevelItem::Line]
                                }),
                                coq::TopLevel::new(
                                    &fields
                                        .iter()
                                        .enumerate()
                                        .flat_map(|(i, (name, _))| {
                                            let projection_pattern = [coq::ArgDecl::new(
                                                &coq::ArgDeclVar::Destructured {
                                                    pattern: coq::Expression::just_name("Build_t")
                                                        .apply_many(
                                                            &fields
                                                                .iter()
                                                                .enumerate()
                                                                .map(|(j, _)| {
                                                                    if i == j {
                                                                        coq::Expression::just_name(
                                                                            &format!("x{j}"),
                                                                        )
                                                                    } else {
                                                                        coq::Expression::Wild
                                                                    }
                                                                })
                                                                .collect::<Vec<_>>(),
                                                        ),
                                                },
                                                coq::ArgSpecKind::Explicit,
                                            )];
                                            [
                                                coq::TopLevelItem::Instance(coq::Instance::new(
                                                    false,
                                                    &format!("Get_{name}"),
                                                    &[],
                                                    coq::Expression::Variable {
                                                        ident: Path::new(&["Notation", "Dot"]),
                                                        no_implicit: false,
                                                    }
                                                    .apply(&coq::Expression::String(
                                                        name.to_owned(),
                                                    )),
                                                    &Some(coq::Expression::Record {
                                                        fields: vec![coq::Field::new(
                                                            &Path::new(&["Notation", "dot"]),
                                                            &projection_pattern,
                                                            &coq::Expression::just_name(&format!(
                                                                "x{i}"
                                                            )),
                                                        )],
                                                    }),
                                                    vec![],
                                                )),
                                                coq::TopLevelItem::Instance(coq::Instance::new(
                                                    false,
                                                    &format!("Get_AF_{name}"),
                                                    &[],
                                                    coq::Expression::Variable {
                                                        ident: Path::new(&[
                                                            "Notation",
                                                            "DoubleColon",
                                                        ]),
                                                        no_implicit: false,
                                                    }
                                                    .apply_many(&[
                                                        coq::Expression::just_name("t"),
                                                        coq::Expression::String(name.to_owned()),
                                                    ]),
                                                    &Some(coq::Expression::Record {
                                                        fields: vec![coq::Field::new(
                                                            &Path::new(&[
                                                                "Notation",
                                                                "double_colon",
                                                            ]),
                                                            &projection_pattern,
                                                            &coq::Expression::just_name(&format!(
                                                                "x{i}"
                                                            )),
                                                        )],
                                                    }),
                                                    vec![],
                                                )),
                                            ]
                                        })
                                        .collect::<Vec<_>>(),
                                ),
                            ]),
                        ),
                    )),
                    coq::TopLevelItem::Definition(coq::Definition::new(
                        name,
                        &coq::DefinitionKind::Alias {
                            args: [
                                if ty_params.is_empty() {
                                    vec![]
                                } else {
                                    vec![coq::ArgDecl::of_ty_params(
                                        ty_params,
                                        coq::ArgSpecKind::Explicit,
                                    )]
                                },
                                predicates
                                    .iter()
                                    .map(|predicate| predicate.to_coq())
                                    .collect(),
                            ]
                            .concat(),
                            ty: Some(coq::Expression::Set),
                            body: coq::Expression::Variable {
                                ident: Path::new(&[name, &"t".to_string()]),
                                no_implicit: false,
                            }
                            .apply_many_args(
                                &ty_params
                                    .iter()
                                    .map(|ty_param| {
                                        (
                                            Some(ty_param.to_owned()),
                                            coq::Expression::just_name(ty_param),
                                        )
                                    })
                                    .collect::<Vec<_>>(),
                            ),
                        },
                    )),
                ],
            ]
            .concat(),
        )
        .to_doc()
    }
}

impl Trait {
    fn to_doc(&self, _supertraits_map: &HashMap<Path, HashSet<Path>>) -> Doc {
        let Trait {
            name,
            ty_params,
            predicates,
            bounds,
            body,
        } = self;

        let items = &body
            .iter()
            .map(|item| match &item.item_data {
                TraitItemData::Definition {
                    ty_params,
                    where_predicates,
                    ty,
                } => vec![coq::ClassFieldDef::new(
                    &Some(item.item_name.to_owned()),
                    &[
                        vec![coq::ArgDecl::monadic_typeclass_parameter()],
                        if ty_params.is_empty() {
                            vec![]
                        } else {
                            vec![coq::ArgDecl::new(
                                &coq::ArgDeclVar::Simple {
                                    idents: ty_params.to_owned(),
                                    ty: Some(coq::Expression::Set),
                                },
                                coq::ArgSpecKind::Implicit,
                            )]
                        },
                        where_predicates
                            .iter()
                            .enumerate()
                            .map(|(i, predicate)| {
                                predicate
                                    .to_coq()
                                    .add_var(&["H'".to_string(), i.to_string()].concat())
                            })
                            .collect(),
                    ]
                    .concat(),
                    &ty.to_coq(),
                )],
                TraitItemData::DefinitionWithDefault { .. } => vec![],
                TraitItemData::Type(bounds) => [
                    vec![coq::ClassFieldDef::new(
                        &Some(item.item_name.to_owned()),
                        &[],
                        &coq::Expression::Set,
                    )],
                    if bounds.is_empty() {
                        vec![]
                    } else {
                        vec![coq::ClassFieldDef::new(
                            &Some(["__the_bounds_of_", &item.item_name].concat()),
                            &[],
                            &coq::Expression::SigmaType {
                                args: bounds
                                    .iter()
                                    .map(|bound| {
                                        bound.to_coq(
                                            coq::Expression::just_name(&item.item_name),
                                            coq::ArgSpecKind::Explicit,
                                        )
                                    })
                                    .collect::<Vec<_>>(),
                                image: Box::new(coq::Expression::Unit),
                            },
                        )]
                    },
                ]
                .concat(),
            })
            .concat();

        coq::TopLevelItem::Module(coq::Module::new(
            name,
            coq::TopLevel::concat(&[
                coq::TopLevel::locally_unset_primitive_projections_if(
                    items.is_empty(),
                    &[coq::TopLevelItem::Class(coq::Class::new(
                        "Trait",
                        &[
                            vec![coq::ArgDecl::new(
                                &coq::ArgDeclVar::Simple {
                                    idents: vec!["Self".to_string()],
                                    ty: Some(coq::Expression::Set),
                                },
                                coq::ArgSpecKind::Explicit,
                            )],
                            bounds
                                .iter()
                                .map(|bound| {
                                    bound.to_coq(
                                        coq::Expression::just_name("Self"),
                                        coq::ArgSpecKind::Implicit,
                                    )
                                })
                                .collect(),
                            if ty_params.is_empty() {
                                vec![]
                            } else {
                                vec![coq::ArgDecl::new(
                                    &coq::ArgDeclVar::Simple {
                                        idents: ty_params
                                            .iter()
                                            .map(|(ty, default)| {
                                                match default {
                                                    // @TODO: implement the translation of type parameters with default
                                                    Some(_default) => ["(* TODO *) ", ty].concat(),
                                                    None => ty.to_string(),
                                                }
                                            })
                                            .collect(),
                                        ty: Some(coq::Expression::Set),
                                    },
                                    coq::ArgSpecKind::Implicit,
                                )]
                            },
                            predicates
                                .iter()
                                .map(|predicate| predicate.to_coq())
                                .collect(),
                        ]
                        .concat(),
                        items,
                    ))],
                ),
                coq::TopLevel::new(
                    &body
                        .iter()
                        .map(|item| match &item.item_data {
                            TraitItemData::Definition {
                                ty_params,
                                where_predicates,
                                ty: _,
                            } => coq::Instance::new(
                                false,
                                &["Method_", &item.item_name].concat(),
                                &[
                                    coq::ArgDecl::monadic_typeclass_parameter(),
                                    coq::ArgDecl::new(
                                        &coq::ArgDeclVar::Generalized {
                                            idents: vec![],
                                            ty: coq::Expression::just_name("Trait"),
                                        },
                                        coq::ArgSpecKind::Explicit,
                                    ),
                                ],
                                coq::Expression::Variable {
                                    ident: Path::new(&["Notation", "Dot"]),
                                    no_implicit: false,
                                }
                                .apply(&coq::Expression::String(item.item_name.to_owned())),
                                &Some(coq::Expression::Record {
                                    fields: vec![coq::Field::new(
                                        &Path::new(&["Notation", "dot"]),
                                        &[
                                            if ty_params.is_empty() {
                                                vec![]
                                            } else {
                                                vec![coq::ArgDecl::of_ty_params(
                                                    ty_params,
                                                    coq::ArgSpecKind::Implicit,
                                                )]
                                            },
                                            where_predicates
                                                .iter()
                                                .enumerate()
                                                .map(|(i, predicate)| {
                                                    predicate.to_coq().add_var(
                                                        &["H'".to_string(), i.to_string()].concat(),
                                                    )
                                                })
                                                .collect(),
                                        ]
                                        .concat(),
                                        &coq::Expression::just_name(&item.item_name)
                                            .apply_many_args(
                                                &ty_params
                                                    .iter()
                                                    .map(|ty_param| {
                                                        (
                                                            Some(ty_param.to_owned()),
                                                            coq::Expression::just_name(ty_param),
                                                        )
                                                    })
                                                    .collect::<Vec<_>>(),
                                            )
                                            .apply_many_args(
                                                &where_predicates
                                                    .iter()
                                                    .enumerate()
                                                    .map(|(i, _)| {
                                                        let var_name =
                                                            ["H'".to_string(), i.to_string()]
                                                                .concat();
                                                        (
                                                            Some(var_name.clone()),
                                                            coq::Expression::just_name(&var_name),
                                                        )
                                                    })
                                                    .collect::<Vec<_>>(),
                                            ),
                                    )],
                                }),
                                vec![],
                            ),
                            TraitItemData::Type { .. } => coq::Instance::new(
                                false,
                                &["Method_", &item.item_name].concat(),
                                &[coq::ArgDecl::new(
                                    &coq::ArgDeclVar::Generalized {
                                        idents: vec![],
                                        ty: coq::Expression::just_name("Trait"),
                                    },
                                    coq::ArgSpecKind::Explicit,
                                )],
                                coq::Expression::Variable {
                                    ident: Path::new(&["Notation", "DoubleColonType"]),
                                    no_implicit: false,
                                }
                                .apply(&coq::Expression::just_name("Self"))
                                .apply(&coq::Expression::String(item.item_name.to_owned())),
                                &Some(coq::Expression::Record {
                                    fields: vec![coq::Field::new(
                                        &Path::new(&["Notation", "double_colon_type"]),
                                        &[],
                                        &coq::Expression::just_name(&item.item_name),
                                    )],
                                }),
                                vec![],
                            ),
                            TraitItemData::DefinitionWithDefault {
                                ty_params,
                                where_predicates,
                                signature_and_body,
                            } => coq::Instance::new(
                                false,
                                &["Method_", &item.item_name].concat(),
                                &[
                                    coq::ArgDecl::monadic_typeclass_parameter(),
                                    coq::ArgDecl::new(
                                        &coq::ArgDeclVar::Generalized {
                                            idents: vec![],
                                            ty: coq::Expression::just_name("Trait"),
                                        },
                                        coq::ArgSpecKind::Explicit,
                                    ),
                                ],
                                coq::Expression::Variable {
                                    ident: Path::new(&["Notation", "Dot"]),
                                    no_implicit: false,
                                }
                                .apply(&coq::Expression::String(item.item_name.to_owned())),
                                &Some(coq::Expression::Record {
                                    fields: vec![coq::Field::new(
                                        &Path::new(&["Notation", "dot"]),
                                        &[
                                            if ty_params.is_empty() {
                                                vec![]
                                            } else {
                                                vec![coq::ArgDecl::of_ty_params(
                                                    ty_params,
                                                    coq::ArgSpecKind::Implicit,
                                                )]
                                            },
                                            where_predicates
                                                .iter()
                                                .map(|predicate| predicate.to_coq())
                                                .collect(),
                                            signature_and_body
                                                .args
                                                .iter()
                                                .map(|(name, ty)| {
                                                    coq::ArgDecl::new(
                                                        &coq::ArgDeclVar::Simple {
                                                            idents: vec![name.to_owned()],
                                                            ty: Some(ty.to_coq()),
                                                        },
                                                        coq::ArgSpecKind::Explicit,
                                                    )
                                                })
                                                .collect::<Vec<_>>(),
                                        ]
                                        .concat(),
                                        &coq::Expression::Code(group([
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
                                        ])),
                                    )],
                                }),
                                vec![],
                            ),
                        })
                        .map(|i| coq::TopLevelItem::Instance(i.to_owned()))
                        .collect_vec(),
                ),
                // extraction of the trait instances
                coq::TopLevel::new(
                    &body
                        .iter()
                        .filter_map(|item| match &item.item_data {
                            TraitItemData::Definition { .. }
                            | TraitItemData::DefinitionWithDefault { .. } => None,
                            TraitItemData::Type(bounds) => {
                                if bounds.is_empty() {
                                    None
                                } else {
                                    let proj_name = [
                                        "__the_bounds_of_",
                                        &item.item_name,
                                        "0",
                                    ]
                                    .concat();
                                    Some(coq::TopLevelItem::Module(coq::Module::new(
                                        &[
                                            "The_Bounds_Of_",
                                            &item.item_name,
                                        ]
                                        .concat(),
                                        coq::TopLevel::new(
                                            &bounds
                                                .iter()
                                                .map(|bound| {
                                                    let local_trait_name = "_Tr";
                                                    let item_for_the_trait = coq::Expression::just_name(
                                                        &item.item_name
                                                    )
                                                    .apply_arg(
                                                        &Some("Trait".to_string()),
                                                        &coq::Expression::just_name(local_trait_name),
                                                    );
                                                    coq::TopLevelItem::Module(coq::Module::new(
                                                        &bound.name.to_name(),
                                                        coq::TopLevel::new(&[
                                                            coq::TopLevelItem::Instance(coq::Instance::new(
                                                                false,
                                                                "I",
                                                                &[coq::ArgDecl::new(
                                                                    &coq::ArgDeclVar::Generalized {
                                                                        idents: vec!["_Tr".to_string()],
                                                                        ty: coq::Expression::just_name("Trait"),
                                                                    },
                                                                    coq::ArgSpecKind::Explicit,
                                                                )],
                                                                coq::Expression::Code(nest([
                                                                    text("ltac:"),
                                                                    round_brackets(group([
                                                                        group([
                                                                            text("unshelve"),
                                                                            line(),
                                                                            text("eapply"),
                                                                            line(),
                                                                            coq::Expression::Variable {
                                                                                ident: Path::concat(&[
                                                                                    bound.name.to_owned(),
                                                                                    Path::new(&["Trait"]),
                                                                                ]),
                                                                                no_implicit: false,
                                                                            }
                                                                            .apply(
                                                                                &item_for_the_trait,
                                                                            )
                                                                            .apply_many_args(
                                                                                &bound.ty_params
                                                                                    .iter()
                                                                                    .map(|ty_param| {
                                                                                        ty_param.to_coq_arg_value(&bound.name)
                                                                                    })
                                                                                    .collect_vec(),
                                                                            )
                                                                            .to_doc(true),
                                                                            text(";"),
                                                                        ]),
                                                                        line(),
                                                                        text("compute;"),
                                                                        line(),
                                                                        group([
                                                                            text("destruct"),
                                                                            line(),
                                                                            text("_Tr"),
                                                                            text(";"),
                                                                        ]),
                                                                        line(),
                                                                        nest([
                                                                            text("repeat"),
                                                                            line(),
                                                                            group([
                                                                                group([
                                                                                    text("destruct"),
                                                                                    line(),
                                                                                    text(proj_name.clone()),
                                                                                    line(),
                                                                                    text("as"),
                                                                                    line(),
                                                                                    square_brackets(nest([
                                                                                        text("?"),
                                                                                        line(),
                                                                                        text(proj_name.clone()),
                                                                                    ])),
                                                                                    text(";"),
                                                                                ]),
                                                                                line(),
                                                                                group([
                                                                                    text("try"),
                                                                                    line(),
                                                                                    text("assumption"),
                                                                                ]),
                                                                            ]),
                                                                        ]),
                                                                    ])),
                                                                ])),
                                                                &None,
                                                                {
                                                                    vec![nest([
                                                                        text("all:"),
                                                                        line(),
                                                                        group([
                                                                            text("compute;"),
                                                                            line(),
                                                                            text("destruct _Tr;"),
                                                                            line(),
                                                                            nest([
                                                                                text("repeat"),
                                                                                line(),
                                                                                round_brackets(group([
                                                                                    text("destruct"),
                                                                                    line(),
                                                                                    text(proj_name.clone()),
                                                                                    line(),
                                                                                    text("as"),
                                                                                    line(),
                                                                                    square_brackets(nest([
                                                                                        text("?"),
                                                                                        line(),
                                                                                        text(proj_name.clone()),
                                                                                    ])),
                                                                                ])),
                                                                            ]),
                                                                            text(";"),
                                                                            line(),
                                                                            text("assumption"),
                                                                        ]),
                                                                        text("."),
                                                                    ])]
                                                                },
                                                            )),
                                                        ]),
                                                    ))
                                                })
                                                .collect_vec(),
                                        ),
                                    )))
                                }
                            },
                        })
                        .collect_vec(),
                ),
            ]),
        ))
        .to_doc()
    }
}

// @TODO
//fn collect_supertraits_in_order

impl TopLevel {
    // function returns TopLevelItem::TypeStructStruct (comparing name)
    fn find_tli_by_name(&self, self_ty: &CoqType) -> Option<&TopLevelItem> {
        //Option<TopLevelItem> {
        self.0.iter().find(|item_ins| match item_ins {
            TopLevelItem::TypeStructStruct(TypeStructStruct {
                name,
                fields: _,
                is_dead_code: _,
                .. // @TODO should generic parameters be used here?
            }) => {
                // check if it is the struct we are looking for
                *name == self_ty.to_item_name()
            }
            _ => false,
        })
    }

    fn to_doc(&self, supertraits_map: &HashMap<Path, HashSet<Path>>) -> Doc {
        // check if there is a Debug Trait implementation in the code (#[derive(Debug)])
        // for a TopLevelItem::TypeStructStruct (@TODO extend to cover more cases)
        // if "yes" - get both TopLevelItems (Struct itself and TraitImpl for it)
        // in order to have all required data for printing instance for DoubleColon Class

        // We go through whole tree and if we face TraitImpl, we need to save previous item too
        // (the one for which Impl is being printed), in order to have all the extra_data

        let mut previous_module_names: Vec<String> = vec![];

        intersperse(
            self.0.iter().map(|item| {
                let extra_data =
                    // if item is DeriveDebug, get struct's fields
                    match item {
                        TopLevelItem::TraitImpl {
                            generic_tys: _,
                            ty_params: _,
                            self_ty,
                            of_trait,
                            items: _,
                            trait_non_default_items: _,
                            has_predicates_on_assoc_ty: _,
                        } =>
                        // if item is DeriveDebug we are getting missing datatypes for Struct, and
                        // printing DoubleColon instance for fmt function
                        {
                            // @TODO. below is support for deriveDebug (add code to support more traits)
                            if of_trait.to_name() == "core_fmt_Debug" {
                                let strct = self.find_tli_by_name(self_ty); // self.get_struct_types(self_ty);
                                                                            // add structs types here (for printing)
                                strct
                            } else {
                                // @TODO add more cases (only Derive debug for Struct supported)");
                                // if no DeriveDebug - we just convert item to doc, no extra data required.
                                None
                            }
                        }
                        _ => {
                            // if item is not TopLevelItem::TraitImpl - we just convert item to doc, no extra data required.
                            None
                        }
                    };
                let to_doc_context = ToDocContext {
                    extra_data,
                    previous_module_names: previous_module_names.clone(),
                    supertraits_map,
                };
                let doc = item.to_doc(to_doc_context);
                if let TopLevelItem::Module { name, .. } = item {
                    previous_module_names.push(name.to_owned());
                };
                doc
            }),
            [hardline(), hardline()],
        )
    }

    pub fn to_pretty(
        &self,
        width: usize,
        supertraits_map: &HashMap<Path, HashSet<Path>>,
    ) -> String {
        let mut w = Vec::new();
        self.to_doc(supertraits_map).render(width, &mut w).unwrap();
        format!("{}{}\n", HEADER, String::from_utf8(w).unwrap())
    }
}
