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
use std::vec;

pub(crate) struct TopLevelOptions {
    pub(crate) configuration_file: String,
    pub(crate) filename: String,
    pub(crate) axiomatize: bool,
    pub(crate) axiomatize_public: bool,
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
    ty_params: Vec<String>,
    where_predicates: Vec<WherePredicate>,
    signature_and_body: FnSigAndBody,
    is_dead_code: bool,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum ImplItem {
    Const {
        ty: Box<CoqType>,
        body: Option<Box<Expr>>,
        is_dead_code: bool,
    },
    Definition {
        definition: FunDefinition,
    },
    Type {
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
    ty_params: Vec<(String, TraitTyParamValue)>,
}

type TraitTyParamValue = FieldWithDefault<Box<CoqType>>;

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum VariantItem {
    Struct { fields: Vec<(String, Box<CoqType>)> },
    Tuple { tys: Vec<Box<CoqType>> },
}

/// The value for a field that may have a default value
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(crate) enum FieldWithDefault<A> {
    /// the value of a field that has no defaults
    RequiredValue(A),
    /// the value that replaces the default value
    OptionalValue(A),
    /// means the default value of the type parameter is used
    Default,
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
    Definition {
        name: String,
        definition: FunDefinition,
    },
    TypeAlias {
        name: String,
        ty_params: Vec<String>,
        ty: Box<CoqType>,
    },
    TypeEnum {
        name: String,
        ty_params: Vec<(String, Option<Box<CoqType>>)>,
        predicates: Vec<WherePredicate>,
        variants: Vec<(String, VariantItem)>,
    },
    TypeStructStruct(TypeStructStruct),
    TypeStructTuple {
        name: String,
        ty_params: Vec<(String, Option<Box<CoqType>>)>,
        fields: Vec<Box<CoqType>>,
    },
    TypeStructUnit {
        name: String,
        ty_params: Vec<(String, Option<Box<CoqType>>)>,
    },
    Module {
        name: String,
        body: TopLevel,
        is_dead_code: bool,
    },
    Impl {
        generic_tys: Vec<String>,
        self_ty: Box<CoqType>,
        /// We use a counter to disambiguate several impls for the same type
        counter: u64,
        items: Vec<(String, ImplItem)>,
    },
    Trait {
        name: String,
        ty_params: Vec<(String, Option<Box<CoqType>>)>,
        predicates: Vec<WherePredicate>,
        body: Vec<(String, TraitItem)>,
    },
    TraitImpl {
        generic_tys: Vec<String>,
        predicates: Vec<WherePredicate>,
        self_ty: Box<CoqType>,
        of_trait: Path,
        trait_ty_params: Vec<(String, TraitTyParamValue)>,
        items: Vec<(String, FieldWithDefault<ImplItem>)>,
    },
    Error(String),
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct TypeStructStruct {
    name: String,
    ty_params: Vec<(String, Option<Box<CoqType>>)>,
    predicates: Vec<WherePredicate>,
    fields: Vec<(String, Box<CoqType>)>,
    is_dead_code: bool,
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

impl<A> FieldWithDefault<A> {
    fn map<B, F>(self, f: F) -> FieldWithDefault<B>
    where
        F: FnOnce(A) -> B,
    {
        match self {
            FieldWithDefault::RequiredValue(a) => FieldWithDefault::RequiredValue(f(a)),
            FieldWithDefault::OptionalValue(a) => FieldWithDefault::OptionalValue(f(a)),
            FieldWithDefault::Default => FieldWithDefault::Default,
        }
    }
}

impl<'a, A> From<&'a FieldWithDefault<A>> for Option<&'a A> {
    fn from(val: &'a FieldWithDefault<A>) -> Self {
        match val {
            FieldWithDefault::RequiredValue(a) => Some(a),
            FieldWithDefault::OptionalValue(a) => Some(a),
            FieldWithDefault::Default => None,
        }
    }
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

fn is_top_level_item_public(tcx: &TyCtxt, env: &Env, item: &Item) -> bool {
    let def_id = item.owner_id.to_def_id();
    let ignore_impls = env.configuration.impl_ignore_axioms.contains(&env.file);
    let id_to_check = match &item.kind {
        ItemKind::Impl(Impl {
            of_trait: Some(trait_ref),
            ..
        }) if !ignore_impls => trait_ref.trait_def_id().unwrap(),
        _ => def_id,
    };
    tcx.visibility(id_to_check).is_public()
}

// gy@NOTE: This function might be able to generalize to more empty traits in general
fn is_sized_trait(segments: Vec<String>) -> bool {
    let sized_trait = vec![
        "core".to_string(),
        "marker".to_string(),
        "Sized".to_string(),
    ];
    segments == sized_trait
}

fn is_not_empty_trait(predicate: &WherePredicate) -> bool {
    let WherePredicate {
        bound: TraitBound {
            name: Path { segments },
            ..
        },
        ..
    } = predicate;
    !is_sized_trait(segments.to_owned())
}

/// [compile_top_level_item] compiles hir [Item]s into coq-of-rust (optional)
/// items.
/// - See https://doc.rust-lang.org/stable/nightly-rustc/rustc_hir/struct.Item.html
///   and the doc for [TopLevelItem]
/// - [rustc_middle::hir::map::Map] is intuitively the type for hir environments
/// - Method [body] allows retrievient the body of an identifier [body_id] in an
///   hir environment [hir]
// @TODO: the argument `tcx` is included in `env` and should thus be removed
fn compile_top_level_item(tcx: &TyCtxt, env: &mut Env, item: &Item) -> Vec<TopLevelItem> {
    let name = to_valid_coq_name(item.ident.name.to_string());
    if env.axiomatize && !env.axiomatize_public {
        let is_public = is_top_level_item_public(tcx, env, item);
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
                // TODO: uncomment this line to have 100% translation with THIR
                // for expressions
                // let value = compile_hir_id(env, body_id.hir_id);
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
            vec![TopLevelItem::Definition {
                name,
                definition: FunDefinition::compile(
                    env,
                    generics,
                    &fn_sig_and_body,
                    "arg",
                    is_dead_code,
                ),
            }]
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
        ItemKind::Enum(enum_def, generics) => {
            let ty_params = get_ty_params(env, generics);
            let predicates = get_where_predicates(tcx, env, generics);
            vec![TopLevelItem::TypeEnum {
                name,
                ty_params,
                predicates,
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
                                        (field.ident.to_string(), compile_type(env, field.ty))
                                    })
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
            }]
        }
        ItemKind::Struct(body, generics) => {
            let is_dead_code = check_dead_code_lint_in_attributes(tcx, item);
            let ty_params = get_ty_params(env, generics);
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
            let predicates = vec![
                get_where_predicates(tcx, env, generics),
                compile_generic_bounds(tcx, env, generic_bounds)
                    .into_iter()
                    .map(|bound| WherePredicate {
                        bound,
                        ty: CoqType::var("Self".to_string()),
                    })
                    .filter(is_not_empty_trait)
                    .collect(),
            ]
            .concat();
            vec![TopLevelItem::Trait {
                name,
                ty_params: get_ty_params(env, generics),
                predicates,
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
            let predicates = get_where_predicates(tcx, env, generics);
            let self_ty = compile_type(env, self_ty);
            let mut items: Vec<ImplItemRef> = items.to_vec();
            let context = get_full_name(tcx, item.hir_id());
            reorder_definitions_inplace(tcx, env, &context, &mut items);
            let items = compile_impl_item_refs(tcx, env, &items, is_dead_code);

            match of_trait {
                Some(trait_ref) => {
                    let rustc_default_item_names: Vec<String> = tcx
                        .associated_items(trait_ref.trait_def_id().unwrap())
                        .in_definition_order()
                        .filter(|item| item.defaultness(*tcx).has_value())
                        .map(|item| to_valid_coq_name(item.name.to_string()))
                        .collect();
                    let items: Vec<(String, FieldWithDefault<ImplItem>)> = items
                        .iter()
                        .map(|(name, item)| {
                            let has_default = rustc_default_item_names
                                .iter()
                                .any(|default_item_name| name == default_item_name);
                            let item = if has_default {
                                FieldWithDefault::OptionalValue(item.clone())
                            } else {
                                FieldWithDefault::RequiredValue(item.clone())
                            };
                            (name.clone(), item)
                        })
                        // We now add the elements that have a default value and are not in the
                        // list of definitions
                        .chain(
                            rustc_default_item_names
                                .iter()
                                .filter(|default_item_name| {
                                    !items.iter().any(|(name, _)| name == *default_item_name)
                                })
                                .map(|default_item_name| {
                                    let item = FieldWithDefault::Default;
                                    (default_item_name.clone(), item)
                                }),
                        )
                        .collect();

                    // Get the generics for the trait
                    let trait_generics = tcx.generics_of(trait_ref.trait_def_id().unwrap());

                    vec![TopLevelItem::TraitImpl {
                        generic_tys,
                        predicates,
                        self_ty,
                        of_trait: compile_path(env, trait_ref.path),
                        trait_ty_params: get_ty_params_with_default_status(
                            env,
                            trait_generics,
                            trait_ref.path,
                        ),
                        items,
                    }]
                }
                None => {
                    let counter_entry = env.impl_counter.entry(*self_ty.clone());
                    let counter = *counter_entry
                        .and_modify(|counter| *counter += 1)
                        .or_insert(1);
                    vec![TopLevelItem::Impl {
                        generic_tys,
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
) -> Vec<(String, ImplItem)> {
    item_refs
        .iter()
        .map(|item_ref| compile_impl_item(tcx, env, tcx.hir().impl_item(item_ref.id), is_dead_code))
        .collect()
}

/// compiles an item
fn compile_impl_item(
    tcx: &TyCtxt,
    env: &mut Env,
    item: &rustc_hir::ImplItem,
    is_dead_code: bool,
) -> (String, ImplItem) {
    let name = to_valid_coq_name(item.ident.name.to_string());
    let item = match &item.kind {
        ImplItemKind::Const(ty, body_id) => {
            let ty = compile_type(env, ty);
            let body = if env.axiomatize {
                None
            } else {
                Some(Box::new(compile_hir_id(env, body_id.hir_id)))
            };
            ImplItem::Const {
                ty,
                body,
                is_dead_code,
            }
        }
        ImplItemKind::Fn(fn_sig, body_id) => ImplItem::Definition {
            definition: FunDefinition::compile(
                env,
                item.generics,
                &get_hir_fn_sig_and_body(tcx, fn_sig, body_id),
                "Pattern",
                is_dead_code,
            ),
        },
        ImplItemKind::Type(ty) => ImplItem::Type {
            ty: compile_type(env, ty),
        },
    };
    (name, item)
}

/// returns the body corresponding to the given body_id
fn get_body<'a>(tcx: &'a TyCtxt, body_id: &rustc_hir::BodyId) -> &'a rustc_hir::Body<'a> {
    tcx.hir().body(*body_id)
}

// compiles the body of a function
fn compile_function_body(env: &mut Env, body: &rustc_hir::Body) -> Option<Box<Expr>> {
    if env.axiomatize {
        return None;
    }
    Some(Box::new(Expr::MonadicOperator {
        name: "M.function_body".to_string(),
        arg: Box::new(compile_hir_id(env, body.value.hir_id)),
    }))
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
            GenericParamKind::Type { default, .. } => {
                Some(f(env, param.name.ident().to_string(), default))
            }
            GenericParamKind::Lifetime { .. } | GenericParamKind::Const { .. } => None,
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
        .filter(is_not_empty_trait)
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
) -> Vec<(String, TraitTyParamValue)> {
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
) -> Vec<(String, TraitTyParamValue)> {
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
) -> (String, TraitTyParamValue) {
    let name = name.to_string();
    let ty = match ty {
        Some(ty) => {
            if *has_default {
                FieldWithDefault::OptionalValue(Box::new(ty.clone()))
            } else {
                FieldWithDefault::RequiredValue(Box::new(ty.clone()))
            }
        }
        None => FieldWithDefault::Default,
    };
    (name, ty)
}

/// Get the list of type parameters names and default status (true if it has a default)
pub(crate) fn type_params_name_and_default_status(
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
            let generic_bounds: Vec<TraitBound> = compile_generic_bounds(tcx, env, generic_bounds);
            TraitItem::Type(generic_bounds)
        }
    }
}

fn compile_top_level(tcx: &TyCtxt, opts: TopLevelOptions) -> TopLevel {
    let mut env = Env {
        impl_counter: HashMap::new(),
        tcx: *tcx,
        axiomatize: opts.axiomatize,
        axiomatize_public: opts.axiomatize_public,
        file: opts.filename,
        reorder_map: HashMap::new(),
        configuration: get_configuration(&opts.configuration_file),
    };

    let mut results: Vec<ItemId> = tcx.hir().items().collect();
    reorder_definitions_inplace(tcx, &mut env, "top_level", &mut results);

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

fn mt_impl_item(item: ImplItem) -> ImplItem {
    match item {
        ImplItem::Const {
            ty,
            body,
            is_dead_code,
        } => {
            let body = match body {
                None => body,
                Some(body) => {
                    let stmt = mt_expression(FreshVars::new(), *body).0;
                    Some(Box::new(Expr::Block(Box::new(stmt))))
                }
            };
            ImplItem::Const {
                ty: mt_ty(ty),
                body,
                is_dead_code,
            }
        }
        ImplItem::Definition { definition } => ImplItem::Definition {
            definition: definition.mt(),
        },
        ImplItem::Type { .. } => item,
    }
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
            signature_and_body: signature_and_body.mt(),
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
        TopLevelItem::Definition { name, definition } => TopLevelItem::Definition {
            name,
            definition: definition.mt(),
        },
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
            generic_tys,
            self_ty,
            counter,
            items,
        } => TopLevelItem::Impl {
            generic_tys,
            self_ty,
            counter,
            items: items
                .into_iter()
                .map(|(name, item)| (name, mt_impl_item(item)))
                .collect(),
        },
        TopLevelItem::Trait {
            name,
            ty_params,
            predicates,
            body,
        } => TopLevelItem::Trait {
            name,
            ty_params,
            predicates,
            body: mt_trait_items(body),
        },
        TopLevelItem::TraitImpl {
            generic_tys,
            predicates,
            self_ty,
            of_trait,
            trait_ty_params,
            items,
        } => TopLevelItem::TraitImpl {
            generic_tys,
            predicates,
            self_ty,
            of_trait,
            trait_ty_params,
            items: items
                .into_iter()
                .map(|(name, item)| (name, item.map(mt_impl_item)))
                .collect(),
        },
        TopLevelItem::Error(_) => item,
    }
}

fn mt_top_level(top_level: TopLevel) -> TopLevel {
    TopLevel(top_level.0.into_iter().map(mt_top_level_item).collect())
}

#[derive(Debug)]
pub(crate) struct DynNameGen {
    name: String,
    // Resources to be translated into a list of `WherePredicates`.
    // Traits' paths along with their opaque type names
    predicates: Vec<(Path, String)>,
}

impl DynNameGen {
    pub(crate) fn new(name: String) -> Self {
        DynNameGen {
            name,
            predicates: vec![],
        }
    }

    fn next(&mut self, path: Path) -> String {
        // Get the next character
        let next_letter = self
            .name
            .chars()
            .map(|c| (c as u8 + 1u8) as char)
            .collect::<String>();
        let full_name = format!("Dyn{}", self.name);
        // Collect the current path to be associated
        let predicates = vec![self.predicates.clone(), vec![(path, full_name.clone())]].concat();
        self.predicates = predicates;
        self.name = next_letter;
        full_name
    }

    fn get_predicates(&self) -> Vec<WherePredicate> {
        self.predicates
            .iter()
            .map(|(path, dyn_name)| WherePredicate {
                bound: TraitBound {
                    name: path.clone(),
                    ty_params: vec![],
                },
                ty: Box::new(CoqType::Var(Box::new(Path::local(dyn_name.to_string())))),
            })
            .collect()
    }

    fn get_type_parm_list(&self) -> Vec<String> {
        self.predicates
            .iter()
            .map(|(_, dyn_name)| dyn_name.clone())
            .collect()
    }

    fn make_dyn_parm(&mut self, arg: Box<CoqType>) -> Box<CoqType> {
        if let CoqType::Ref(arg, mutability) = *arg {
            let ct = self.make_dyn_parm(arg);
            Box::new(CoqType::Ref(ct, mutability))
        } else if let CoqType::Dyn(path) = *arg {
            // We suppose `dyn` is only associated with one trait so we can directly extract the first element
            if let Some(path) = path.first() {
                let dy_name = self.next(path.clone());
                Box::new(CoqType::Var(Box::new(Path::local(dy_name))))
            } else {
                // NOTE: cannot use `arg` directly because it is partially borrowed. Can it be fixed?
                Box::new(CoqType::Dyn(path))
            }
        } else {
            arg
        }
    }
}

impl FunDefinition {
    /// compiles a given function
    fn compile(
        env: &mut Env,
        generics: &rustc_hir::Generics,
        fn_sig_and_body: &HirFnSigAndBody,
        default: &str,
        is_dead_code: bool,
    ) -> Self {
        let tcx = env.tcx;
        let mut dyn_name_gen = DynNameGen::new("T".to_string());
        let FnSigAndBody { args, ret_ty, body } =
            compile_fn_sig_and_body(env, fn_sig_and_body, default);
        let args = args.iter().fold(vec![], |result, (string, ty)| {
            let ty = dyn_name_gen.make_dyn_parm(ty.clone());
            vec![result, vec![(string.to_owned(), ty)]].concat()
        });
        let ty_params = vec![
            get_ty_params_names(env, generics),
            dyn_name_gen.get_type_parm_list(),
        ]
        .concat();

        let where_predicates = vec![
            get_where_predicates(&tcx, env, generics),
            dyn_name_gen.get_predicates(),
        ]
        .concat();
        let signature_and_body = FnSigAndBody { args, ret_ty, body };

        FunDefinition {
            ty_params,
            where_predicates,
            signature_and_body,
            is_dead_code,
        }
    }

    fn mt(self) -> Self {
        FunDefinition {
            ty_params: self.ty_params,
            where_predicates: self.where_predicates,
            signature_and_body: self.signature_and_body.mt(),
            is_dead_code: self.is_dead_code,
        }
    }

    fn to_coq(&self, name: &str, with_state_trait: bool) -> coq::TopLevel {
        coq::TopLevel::new(
            &[
                if self.is_dead_code {
                    vec![coq::TopLevelItem::Comment(coq::Comment::new(
                        "#[allow(dead_code)] - function was ignored by the compiler",
                    ))]
                } else {
                    vec![]
                },
                match &self.signature_and_body.body {
                    None => {
                        let ret_ty_name = [name, "_", "ret_ty"].concat();
                        let ret_opaque_ty = CoqType::Application {
                            func: CoqType::var("projT1".to_string()),
                            args: vec![CoqType::var(ret_ty_name.clone())],
                            is_alias: false,
                        };
                        let opaque_return_tys_bounds =
                            self.signature_and_body.ret_ty.opaque_types_bounds();
                        let bounds_to_definition = |bounds: &Vec<Path>| {
                            coq::TopLevelItem::Definition(coq::Definition::new(
                                &ret_ty_name,
                                &coq::DefinitionKind::Assumption {
                                    ty: coq::Expression::PiType {
                                        args: vec![coq::ArgDecl::monadic_typeclass_parameter()],
                                        image: Box::new(coq::Expression::SigmaType {
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
                                        }),
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
                                name,
                                &coq::DefinitionKind::Assumption {
                                    ty: coq::Expression::PiType {
                                        args: [
                                            if with_state_trait {
                                                vec![coq::ArgDecl::monadic_typeclass_parameter()]
                                            } else {
                                                vec![]
                                            },
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
                                            if self.where_predicates.is_empty() {
                                                vec![]
                                            } else {
                                                vec![WherePredicate::vec_to_coq(
                                                    &self.where_predicates,
                                                )]
                                            },
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
                        name,
                        &coq::DefinitionKind::Alias {
                            args: [
                                if with_state_trait {
                                    vec![coq::ArgDecl::monadic_typeclass_parameter()]
                                } else {
                                    vec![]
                                },
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
                                if self.where_predicates.is_empty() {
                                    vec![]
                                } else {
                                    vec![WherePredicate::vec_to_coq(&self.where_predicates)]
                                },
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

    fn to_doc(&self, name: &str, with_state_trait: bool) -> Doc {
        self.to_coq(name, with_state_trait).to_doc()
    }
}

impl ImplItem {
    fn class_instance_to_doc<'a>(
        instance_prefix: &'a str,
        name: &'a str,
        ty_params: Option<&'a [String]>,
        where_predicates: Option<&'a [WherePredicate]>,
        class_name: &'a str,
        method_name: &'a str,
    ) -> Doc<'a> {
        group([
            nest([
                nest([
                    text("Global Instance "),
                    text(format!("{instance_prefix}_{name}")),
                    // Type parameters a, b, c... compiles to {a b c ... : Set}
                    match ty_params {
                        None | Some([]) => nil(),
                        Some(ty_params) => concat([
                            line(),
                            coq::ArgDecl::of_ty_params(ty_params, coq::ArgSpecKind::Implicit)
                                .to_doc(),
                        ]),
                    },
                    // where predicates types
                    match where_predicates {
                        None | Some([]) => nil(),
                        Some(where_predicates) => concat([
                            line(),
                            WherePredicate::vec_to_coq(where_predicates).to_doc(),
                        ]),
                    },
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
                    {
                        let body = coq::Expression::just_name(name);
                        match ty_params {
                            None => body,
                            Some(ty_params) => body.apply_many_args(
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
                        }
                        .to_doc(false)
                    },
                    text(";"),
                ]),
            ]),
            hardline(),
            text("}."),
        ])
    }

    fn to_doc<'a>(&'a self, name: &'a str) -> Doc {
        match self {
            ImplItem::Const {
                ty,
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
                match body {
                    None => nest([
                        nest([text("Parameter"), line(), text(name), text(" :")]),
                        line(),
                        ty.to_doc(false),
                        text("."),
                    ]),
                    Some(body) => nest([
                        nest([
                            nest([text("Definition"), line(), text(name), text(" :")]),
                            line(),
                            ty.to_doc(false),
                            text(" :="),
                        ]),
                        line(),
                        nest([text("M.run"), line(), body.to_doc(true)]),
                        text("."),
                    ]),
                },
                hardline(),
                hardline(),
                Self::class_instance_to_doc(
                    "AssociatedFunction",
                    name,
                    None,
                    None,
                    "Notation.DoubleColon Self",
                    "Notation.double_colon",
                ),
            ]),
            ImplItem::Definition { definition, .. } => concat([
                definition.to_doc(name, false),
                hardline(),
                hardline(),
                Self::class_instance_to_doc(
                    "AssociatedFunction",
                    name,
                    Some(&definition.ty_params),
                    Some(&definition.where_predicates),
                    "Notation.DoubleColon Self",
                    "Notation.double_colon",
                ),
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

impl WherePredicate {
    fn vec_to_coq(predicates: &[Self]) -> coq::ArgDecl {
        coq::ArgDecl::new(
            &coq::ArgDeclVar::Traits {
                traits: predicates
                    .iter()
                    .map(|predicate| predicate.bound.to_coq(predicate.ty.to_coq()))
                    .collect(),
            },
            coq::ArgSpecKind::Implicit,
        )
    }
}

impl TraitBound {
    /// Get the generics for the trait
    fn compile(tcx: &TyCtxt, env: &Env, ptraitref: &rustc_hir::PolyTraitRef) -> TraitBound {
        TraitBound {
            name: compile_path(env, ptraitref.trait_ref.path),
            ty_params: get_ty_params_with_default_status(
                env,
                tcx.generics_of(ptraitref.trait_ref.trait_def_id().unwrap()),
                ptraitref.trait_ref.path,
            ),
        }
    }

    fn to_coq<'a>(&self, self_ty: coq::Expression<'a>) -> coq::Expression<'a> {
        coq::Expression::Application {
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
                .map(|(name, ty_param)| match ty_param.to_owned() {
                    FieldWithDefault::RequiredValue(ty) | FieldWithDefault::OptionalValue(ty) => {
                        (Some(name.clone()), ty.to_coq())
                    }
                    FieldWithDefault::Default => (
                        Some(name.clone()),
                        coq::Expression::Code(concat([
                            self.name.to_doc(),
                            text(".Default."),
                            text(name.clone()),
                        ]))
                        .apply(&self_ty),
                    ),
                })
                .collect(),
        }
    }
}

struct ToDocContext {
    previous_module_names: Vec<String>,
}

impl TopLevelItem {
    fn to_doc(&self, to_doc_context: ToDocContext) -> Doc {
        match self {
            TopLevelItem::Const { name, ty, value } => match value {
                None => coq::TopLevel::new(&[coq::TopLevelItem::Definition(coq::Definition::new(
                    name,
                    &coq::DefinitionKind::Assumption {
                        ty: coq::Expression::PiType {
                            args: vec![coq::ArgDecl::monadic_typeclass_parameter()],
                            image: Box::new(ty.to_coq()),
                        },
                    },
                ))])
                .to_doc(),
                Some(value) => {
                    coq::TopLevel::new(&[coq::TopLevelItem::Definition(coq::Definition::new(
                        name,
                        &coq::DefinitionKind::Alias {
                            args: vec![coq::ArgDecl::monadic_typeclass_parameter()],
                            ty: Some(ty.to_coq()),
                            body: coq::Expression::Code(nest([
                                text("M.run"),
                                line(),
                                value.to_doc(true),
                            ])),
                        },
                    ))])
                    .to_doc()
                }
            },
            TopLevelItem::Definition { name, definition } => definition.to_doc(name, true),
            TopLevelItem::Module {
                name,
                body,
                is_dead_code,
            } => {
                let nb_previous_occurrences_of_module_name = to_doc_context
                    .previous_module_names
                    .iter()
                    .filter(|&current_name| current_name == name)
                    .count();
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
                            false,
                            nb_previous_occurrences_of_module_name,
                            coq::TopLevel::new(&[coq::TopLevelItem::Code(body.to_doc())]),
                        ))],
                    ]
                    .concat(),
                )
                .to_doc()
            }
            TopLevelItem::TypeAlias {
                name,
                ty,
                ty_params,
            } => nest([
                nest([
                    nest([text("Ltac"), line(), text(name)]),
                    concat(
                        ty_params
                            .iter()
                            .map(|ty_param| concat([line(), text(ty_param)])),
                    ),
                    text(" :="),
                ]),
                line(),
                (CoqType::Application {
                    func: CoqType::var("refine".to_string()),
                    args: vec![ty.clone()],
                    is_alias: false,
                })
                .to_doc(false),
                text("."),
            ]),
            TopLevelItem::TypeEnum {
                name,
                ty_params,
                predicates,
                variants,
            } => group([
                coq::TopLevelItem::Module(coq::Module::new(
                    name,
                    false,
                    coq::TopLevel::concat(&[coq::TopLevel::new(&[coq::TopLevelItem::Code(
                        group([
                            concat(variants.iter().map(|(name, fields)| {
                                match fields {
                                    VariantItem::Tuple { .. } => nil(),
                                    VariantItem::Struct { fields } => concat([
                                        coq::Module::new(
                                            name,
                                            false,
                                            coq::TopLevel::locally_unset_primitive_projections(&[
                                                coq::TopLevelItem::Code(concat([
                                                    nest([
                                                        text("Record"),
                                                        line(),
                                                        text("t"),
                                                        line(),
                                                        text("`{ℋ : State.Trait}"),
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
                                                                    fields.iter().map(
                                                                        |(name, ty)| {
                                                                            nest([
                                                                                text(name),
                                                                                line(),
                                                                                text(":"),
                                                                                line(),
                                                                                ty.to_doc(false),
                                                                                text(";"),
                                                                            ])
                                                                        },
                                                                    ),
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
                                text("`{ℋ : State.Trait}"),
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
                                            VariantItem::Tuple { tys } => {
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
                                                }))
                                            }
                                        },
                                    ])
                                }),
                                [line()],
                            ),
                            text("."),
                        ]),
                    )])]),
                ))
                .to_doc(),
                hardline(),
                coq::TopLevelItem::Definition(coq::Definition::new(
                    name,
                    &coq::DefinitionKind::Alias {
                        args: vec![
                            if ty_params.is_empty() {
                                vec![]
                            } else {
                                vec![coq::ArgDecl::of_ty_params(
                                    &ty_params
                                        .iter()
                                        .map(|(name, _)| name.clone())
                                        .collect::<Vec<_>>(),
                                    coq::ArgSpecKind::Explicit,
                                )]
                            },
                            vec![coq::ArgDecl::monadic_typeclass_parameter()],
                            if predicates.is_empty() {
                                vec![]
                            } else {
                                vec![WherePredicate::vec_to_coq(predicates)]
                            },
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
                                .map(|(name, _)| {
                                    (Some(name.clone()), coq::Expression::just_name(name))
                                })
                                .collect::<Vec<_>>(),
                        ),
                    },
                ))
                .to_doc(),
            ]),
            TopLevelItem::TypeStructStruct(tss) => tss.to_doc(),
            TopLevelItem::TypeStructTuple {
                name,
                ty_params,
                fields,
            } => group([coq::TopLevel::new(&[
                coq::TopLevelItem::Module(coq::Module::new(
                    name,
                    true,
                    coq::TopLevel::add_context_in_section(
                        &ty_params
                            .iter()
                            .map(|(name, _)| name.clone())
                            .collect::<Vec<_>>(),
                        &coq::TopLevel::concat(&[
                            coq::TopLevel::locally_unset_primitive_projections(&[
                                coq::TopLevelItem::Record(coq::Record::new(
                                    "t",
                                    &coq::Expression::Set,
                                    &fields
                                        .iter()
                                        .enumerate()
                                        .map(|(i, ty)| {
                                            coq::FieldDef::new(&Some(format!("x{i}")), &ty.to_coq())
                                        })
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
                                            &format!("Get_{i}"),
                                            &[],
                                            coq::Expression::Variable {
                                                ident: Path::new(&["Notation", "Dot"]),
                                                no_implicit: false,
                                            }
                                            .apply(
                                                &coq::Expression::just_name(&format!("\"{i}\"")),
                                            ),
                                            &coq::Expression::Record {
                                                fields: vec![coq::Field::new(
                                                    &Path::new(&["Notation", "dot"]),
                                                    &[struct_projection_pattern(name.to_owned())],
                                                    &struct_field_value(format!("x{i}")),
                                                )],
                                            },
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
                        args: vec![
                            vec![coq::ArgDecl::monadic_typeclass_parameter()],
                            if ty_params.is_empty() {
                                vec![]
                            } else {
                                vec![coq::ArgDecl::new(
                                    &coq::ArgDeclVar::Simple {
                                        idents: ty_params
                                            .iter()
                                            .map(|(name, _)| name.to_owned())
                                            .collect(),
                                        ty: Some(coq::Expression::Set),
                                    },
                                    coq::ArgSpecKind::Explicit,
                                )]
                            },
                        ]
                        .concat(),
                        ty: Some(coq::Expression::Set),
                        body: coq::Expression::just_name("M.Val").apply(
                            &coq::Expression::Variable {
                                ident: Path::new(&[name, &"t".to_string()]),
                                no_implicit: false,
                            }
                            .apply_many_args(
                                &ty_params
                                    .iter()
                                    .map(|(name, _)| {
                                        (Some(name.to_owned()), coq::Expression::just_name(name))
                                    })
                                    .collect::<Vec<_>>(),
                            ),
                        ),
                    },
                )),
            ])
            .to_doc()]),
            TopLevelItem::TypeStructUnit { name, ty_params } => coq::TopLevel::new(&[
                coq::TopLevelItem::Module(coq::Module::new(
                    name,
                    true,
                    coq::TopLevel::add_context_in_section(
                        &ty_params
                            .iter()
                            .map(|(name, _)| name.clone())
                            .collect::<Vec<_>>(),
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
                generic_tys,
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
                    true,
                    coq::TopLevel::add_context_in_section(
                        generic_tys,
                        &coq::TopLevel::concat(&[
                            coq::TopLevel::new(&[coq::TopLevelItem::Definition(
                                coq::Definition::new(
                                    "Self",
                                    &coq::DefinitionKind::Alias {
                                        args: vec![],
                                        ty: Some(coq::Expression::Set),
                                        body: self_ty.to_coq(),
                                    },
                                ),
                            )]),
                            coq::TopLevel::new(
                                &items
                                    .iter()
                                    .flat_map(|(name, item)| {
                                        [
                                            coq::TopLevelItem::Line,
                                            coq::TopLevelItem::Code(concat([item.to_doc(name)])),
                                        ]
                                    })
                                    .collect::<Vec<_>>(),
                            ),
                        ]),
                    ),
                ))])
                .to_doc()
            }
            TopLevelItem::Trait {
                name,
                ty_params,
                predicates,
                body,
            } => coq::TopLevelItem::trait_module(
                name,
                &ty_params
                    .iter()
                    .map(|(ty, default)| {
                        (
                            ty.to_owned(),
                            default.as_ref().map(|default| default.to_coq()),
                        )
                    })
                    .collect::<Vec<_>>(),
                &vec![
                    predicates
                        .iter()
                        .map(|predicate| {
                            coq::ClassFieldDef::new(
                                &None,
                                &[],
                                &predicate.bound.to_coq(predicate.ty.to_coq()),
                            )
                        })
                        .collect(),
                    body.iter()
                        .map(|(name, item)| match item {
                            TraitItem::Definition {
                                ty_params,
                                where_predicates,
                                ty,
                            } => vec![coq::ClassFieldDef::new(
                                &Some(name.to_owned()),
                                &[
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
                                    if where_predicates.is_empty() {
                                        vec![]
                                    } else {
                                        vec![WherePredicate::vec_to_coq(where_predicates)]
                                    },
                                ]
                                .concat(),
                                &ty.to_coq(),
                            )],
                            TraitItem::DefinitionWithDefault { .. } => vec![],
                            TraitItem::Type(bounds) => [
                                vec![coq::ClassFieldDef::new(
                                    &Some(name.to_owned()),
                                    &[],
                                    &coq::Expression::Set,
                                )],
                                bounds
                                    .iter()
                                    .map(|bound| {
                                        coq::ClassFieldDef::new(
                                            &None,
                                            &[],
                                            &bound.to_coq(coq::Expression::just_name(name)),
                                        )
                                    })
                                    .collect::<Vec<_>>(),
                            ]
                            .concat(),
                        })
                        .concat(),
                ]
                .concat(),
                &body
                    .iter()
                    .filter_map(|(name, item)| match item {
                        TraitItem::Definition { .. } => None,
                        TraitItem::Type { .. } => Some(coq::Instance::new(
                            &format!("Method_{name}"),
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
                            .apply(&coq::Expression::String(name.to_owned())),
                            &coq::Expression::Record {
                                fields: vec![coq::Field::new(
                                    &Path::new(&["Notation", "double_colon_type"]),
                                    &[],
                                    &coq::Expression::just_name(name),
                                )],
                            },
                            vec![],
                        )),
                        TraitItem::DefinitionWithDefault { .. } => None,
                    })
                    .collect::<Vec<_>>(),
            )
            .to_doc(),
            TopLevelItem::TraitImpl {
                generic_tys,
                predicates,
                self_ty,
                of_trait,
                trait_ty_params,
                items,
                ..
            } => {
                let module_name = format!(
                    "Impl_{}{}_for_{}",
                    of_trait.to_name(),
                    trait_ty_params
                        .iter()
                        .filter_map(|(_, trait_ty_param)| match trait_ty_param.to_owned() {
                            FieldWithDefault::RequiredValue(ty)
                            | FieldWithDefault::OptionalValue(ty) =>
                                Some(format!("_{}", ty.to_name())),
                            FieldWithDefault::Default => None,
                        })
                        .join(""),
                    self_ty.to_name()
                );
                let has_some_default_values = !items
                    .iter()
                    .all(|(_, item)| matches!(item, FieldWithDefault::RequiredValue(_)));

                coq::Module::new(
                    &module_name,
                    true,
                    coq::TopLevel::concat(&[
                        coq::TopLevel::add_context_in_section(
                            generic_tys,
                            &coq::TopLevel::new(&[
                                if predicates.is_empty() {
                                    vec![]
                                } else {
                                    vec![coq::TopLevelItem::Context(coq::Context::new(
                                            &[WherePredicate::vec_to_coq(predicates)]
                                    ))]
                                },
                                vec![
                                    coq::TopLevelItem::Definition(coq::Definition::new(
                                        "Self",
                                        &coq::DefinitionKind::Alias {
                                            args: vec![],
                                            ty: Some(coq::Expression::Set),
                                            body: self_ty.to_coq(),
                                        },
                                    )),
                                ],
                                vec![coq::TopLevelItem::Line],
                                items
                                    .iter()
                                    .filter_map(|(name, item)|
                                        Into::<Option<_>>::into(item).map(|item: &ImplItem| vec![
                                            coq::TopLevelItem::Code(item.to_doc(name)),
                                            coq::TopLevelItem::Line,
                                        ])
                                    )
                                    .concat(),
                                vec![coq::TopLevelItem::Instance(coq::Instance::new(
                                    "ℐ",
                                    &[],
                                    coq::Expression::Variable {
                                        ident: Path::concat(&[
                                            of_trait.to_owned(),
                                            Path::new(
                                                if has_some_default_values {
                                                    &["Required", "Trait"]
                                                } else {
                                                    &["Trait"]
                                                }),
                                        ]),
                                        no_implicit: false,
                                    }
                                    .apply(&coq::Expression::just_name("Self"))
                                    .apply_many_args(
                                        &trait_ty_params
                                            .iter()
                                            .map(|(name, ty_param)| {
                                                match ty_param {
                                                    FieldWithDefault::RequiredValue(ty) | FieldWithDefault::OptionalValue(ty) => {
                                                        (Some(name.clone()), ty.to_coq())
                                                    }
                                                    FieldWithDefault::Default => (
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
                                    &coq::Expression::Record {
                                        fields: items
                                            .iter()
                                            .map(|(name, item)| {
                                                let optional_item = Into::<Option<&_>>::into(item);

                                                coq::Field::new(
                                                    &Path::concat(&[of_trait.to_owned(), Path::new(&[name])]),
                                                    &match optional_item {
                                                        Some(ImplItem::Definition { definition : FunDefinition {ty_params, where_predicates, ..}, ..}) =>
                                                                    vec![
                                                                        if ty_params.is_empty() {
                                                                            vec![]
                                                                        } else {
                                                                            vec![coq::ArgDecl::of_ty_params(ty_params, coq::ArgSpecKind::Implicit)]
                                                                        },
                                                                        if where_predicates.is_empty() {
                                                                            vec![]
                                                                        } else {
                                                                            vec![WherePredicate::vec_to_coq(where_predicates)]
                                                                        },
                                                                    ].concat(),
                                                        _ => vec![],
                                                    },
                                                    {
                                                        let body = coq::Expression::just_name(name);
                                                        let body =
                                                            match optional_item {
                                                                Some(ImplItem::Definition { definition : FunDefinition {ty_params, ..}, ..}) =>
                                                                body.apply_many_args(&ty_params
                                                                    .iter()
                                                                    .map(|ty_param| {
                                                                        (
                                                                            Some(ty_param.to_owned()),
                                                                            coq::Expression::just_name(ty_param),
                                                                        )
                                                                    })
                                                                    .collect::<Vec<_>>(),),
                                                                _ => body
                                                            };
                                                        &match item {
                                                            FieldWithDefault::RequiredValue(_) => body,
                                                            FieldWithDefault::OptionalValue(_) =>
                                                                coq::Expression::just_name("Datatypes.Some")
                                                                .apply(&body),
                                                            FieldWithDefault::Default =>
                                                                coq::Expression::just_name("Datatypes.None"),
                                                        }
                                                    }
                                                )
                                            })
                                            .collect::<Vec<_>>(),
                                    },
                                    vec![],
                                ))],
                            ]
                            .concat()),
                        ),
                    ]),
                )
                .to_doc()
            }
            TopLevelItem::Error(message) => nest([text("Error"), line(), text(message), text(".")]),
        }
    }
}

fn struct_projection_pattern<'a>(name: String) -> coq::ArgDecl<'a> {
    coq::ArgDecl::new(
        &coq::ArgDeclVar::Simple {
            idents: vec![if name == "x" { "x'" } else { "x" }.to_string()],
            ty: None,
        },
        coq::ArgSpecKind::Explicit,
    )
}

fn struct_field_value<'a>(name: String) -> coq::Expression<'a> {
    let x = if name == "x" { "x'" } else { "x" };
    coq::Expression::Code(nest([
        group([
            nest([
                text(format!("let* {x} :=")),
                line(),
                text(format!("M.read {x} in")),
            ]),
            line(),
            nest([
                text("M.pure"),
                line(),
                text(format!("{x}.(")),
                text(name),
                text(") :"),
            ]),
        ]),
        line(),
        text("M _"),
    ]))
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

        // List of parameters with default values
        let params_with_default = ty_params
            .iter()
            .filter_map(|(ty, default)| {
                default.as_ref().map(|d| {
                    coq::TopLevelItem::Definition(coq::Definition::new(
                        ty,
                        &coq::DefinitionKind::Alias {
                            args: vec![],
                            ty: None,
                            body: coq::Expression::Code(nest([d.to_doc(false)])),
                        },
                    ))
                })
            })
            .collect::<Vec<_>>();
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
                        true,
                        coq::TopLevel::concat(&[
                          coq::TopLevel::add_context_in_section(
                              &ty_params.iter().map(|(name, _)| name.clone()).collect::<Vec<_>>(),
                              &coq::TopLevel::concat(&[
                                  coq::TopLevel::new(&if predicates.is_empty() {
                                      vec![]
                                  } else {
                                      vec![coq::TopLevelItem::Context(coq::Context::new(
                                            &[WherePredicate::vec_to_coq(predicates)]
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
                                                      false,
                                                      coq::TopLevel::new(&[
                                                          vec![coq::TopLevelItem::Definition(
                                                              coq::Definition::new(
                                                                  "t",
                                                                  &coq::DefinitionKind::Assumption {
                                                                      ty: coq::Expression::Set
                                                                  },
                                                              ),
                                                          )],
                                                          single_trait_object_traits
                                                              .iter()
                                                              .map(|single_trait_object_trait| {
                                                                  coq::TopLevelItem::Instance(
                                                                      coq::Instance::new(
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
                                                                          &coq::Expression::just_name("axiom"),
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
                                                                  }
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
                                          .flat_map(|(name, _)| {
                                              [
                                                  coq::TopLevelItem::Instance(coq::Instance::new(
                                                      &format!("Get_{name}"),
                                                      &[],
                                                      coq::Expression::Variable {
                                                          ident: Path::new(&["Notation", "Dot"]),
                                                          no_implicit: false,
                                                      }
                                                      .apply(&coq::Expression::String(
                                                          name.to_owned(),
                                                      )),
                                                      &coq::Expression::Record {
                                                          fields: vec![coq::Field::new(
                                                              &Path::new(&["Notation", "dot"]),
                                                              &[struct_projection_pattern(name.to_owned())],
                                                              &struct_field_value(name.to_owned()),
                                                          )],
                                                      },
                                                      vec![],
                                                  )),
                                                  coq::TopLevelItem::Instance(coq::Instance::new(
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
                                                      &coq::Expression::Record {
                                                          fields: vec![coq::Field::new(
                                                              &Path::new(&[
                                                                  "Notation",
                                                                  "double_colon",
                                                              ]),
                                                              &[struct_projection_pattern(name.to_owned())],
                                                              &struct_field_value(name.to_owned()),
                                                          )],
                                                      },
                                                      vec![],
                                                  )),
                                              ]
                                          })
                                          .collect::<Vec<_>>(),
                                  ),
                              ]),
                          ),
                          coq::TopLevel::new(&if params_with_default.is_empty() {
                              vec![]
                          } else {
                              vec![
                                coq::TopLevelItem::Module(coq::Module::new(
                                  "Default", false, coq::TopLevel::new(&params_with_default)
                                ))
                              ]
                          })
                        ])
                    )),
                    coq::TopLevelItem::Definition(coq::Definition::new(
                        name,
                        &coq::DefinitionKind::Alias {
                            args: [
                                if ty_params.is_empty() {
                                    vec![]
                                } else {
                                    vec![coq::ArgDecl::of_ty_params(
                                        &ty_params.iter().map(|(name, _)| name.clone()).collect::<Vec<_>>(),
                                        coq::ArgSpecKind::Explicit,
                                    )]
                                },
                                vec![coq::ArgDecl::monadic_typeclass_parameter()],
                                if predicates.is_empty() {
                                    vec![]
                                } else {
                                    vec![WherePredicate::vec_to_coq(predicates)]
                                },
                            ]
                            .concat(),
                            ty: Some(coq::Expression::Set),
                            body: coq::Expression::just_name("M.Val").apply(&coq::Expression::Variable {
                                ident: Path::new(&[name, &"t".to_string()]),
                                no_implicit: false,
                            }
                            .apply_many_args(
                                &ty_params
                                    .iter()
                                    .map(|(ty_param, _)| {
                                        (
                                            Some(ty_param.to_owned()),
                                            coq::Expression::just_name(ty_param),
                                        )
                                    })
                                    .collect::<Vec<_>>(),
                            )),
                        },
                    )),
                ],
            ]
            .concat(),
        )
        .to_doc()
    }
}

impl TopLevel {
    fn to_doc(&self) -> Doc {
        // check if there is a Debug Trait implementation in the code (#[derive(Debug)])
        // for a TopLevelItem::TypeStructStruct (@TODO extend to cover more cases)
        // if "yes" - get both TopLevelItems (Struct itself and TraitImpl for it)
        // in order to have all required data for printing instance for DoubleColon Class

        // We go through whole tree and if we face TraitImpl, we need to save previous item too
        // (the one for which Impl is being printed), in order to have all the extra_data

        let mut previous_module_names: Vec<String> = vec![];

        intersperse(
            self.0.iter().map(|item| {
                let to_doc_context = ToDocContext {
                    previous_module_names: previous_module_names.clone(),
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

    pub fn to_pretty(&self, width: usize) -> String {
        let mut w = Vec::new();
        self.to_doc().render(width, &mut w).unwrap();
        format!("{}{}\n", HEADER, String::from_utf8(w).unwrap())
    }
}
