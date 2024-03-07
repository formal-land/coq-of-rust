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
    GenericBound, GenericBounds, GenericParamKind, Impl, ImplItemRef, Item, ItemId, ItemKind,
    PatKind, QPath, TraitFn, TraitItemKind, Ty, TyKind, VariantData,
};
use rustc_middle::ty::TyCtxt;
use rustc_span::symbol::sym;
use std::collections::HashMap;
use std::iter::repeat;
use std::rc::Rc;
use std::string::ToString;
use std::vec;

pub(crate) struct TopLevelOptions {
    pub(crate) configuration_file: String,
    pub(crate) filename: String,
    pub(crate) axiomatize: bool,
    pub(crate) axiomatize_public: bool,
    pub(crate) generate_reorder: bool,
}

#[derive(Debug)]
struct HirFnSigAndBody<'a> {
    fn_sig: &'a rustc_hir::FnSig<'a>,
    body: &'a rustc_hir::Body<'a>,
}

#[derive(Debug, Eq, Hash, PartialEq)]
struct FnSigAndBody {
    args: Vec<(String, Rc<CoqType>)>,
    ret_ty: Rc<CoqType>,
    body: Option<Rc<Expr>>,
}

#[derive(Debug, Eq, Hash, PartialEq)]
enum TraitItem {
    Definition {
        ty_params: Vec<String>,
        ty: Rc<CoqType>,
    },
    DefinitionWithDefault(Rc<FunDefinition>),
    Type(Vec<Rc<TraitBound>>),
}

/// fields common for all function definitions
#[derive(Debug, Eq, Hash, PartialEq)]
struct FunDefinition {
    ty_params: Vec<String>,
    signature_and_body: Rc<FnSigAndBody>,
    is_dead_code: bool,
}

#[derive(Debug, Eq, Hash, PartialEq)]
enum ImplItemKind {
    Const {
        ty: Rc<CoqType>,
        body: Option<Rc<Expr>>,
        is_dead_code: bool,
    },
    Definition {
        definition: Rc<FunDefinition>,
    },
    Type {
        ty: Rc<CoqType>,
    },
}

#[derive(Debug, Eq, Hash, PartialEq)]
struct TraitBound {
    name: Path,
    ty_params: Vec<(String, Rc<TraitTyParamValue>)>,
}

type TraitTyParamValue = FieldWithDefault<Rc<CoqType>>;

#[derive(Debug, Eq, Hash, PartialEq)]
pub(crate) enum VariantItem {
    Struct { fields: Vec<(String, Rc<CoqType>)> },
    Tuple { tys: Vec<Rc<CoqType>> },
}

/// The value for a field that may have a default value
#[derive(Debug, Eq, Hash, PartialEq)]
pub(crate) enum FieldWithDefault<A> {
    /// the value of a field that has no defaults
    RequiredValue(A),
    /// the value that replaces the default value
    OptionalValue(A),
    /// means the default value of the type parameter is used
    Default,
}

#[derive(Debug, Eq, Hash, PartialEq)]
struct Snippet(Vec<String>);

#[derive(Debug, Eq, Hash, PartialEq)]
struct ImplItem {
    name: String,
    snippet: Option<Rc<Snippet>>,
    kind: Rc<ImplItemKind>,
}

#[derive(Debug, Eq, Hash, PartialEq)]
struct TraitImplItem {
    name: String,
    snippet: Option<Rc<Snippet>>,
    kind: Rc<FieldWithDefault<Rc<ImplItemKind>>>,
}

/// Representation of top-level hir [Item]s in coq-of-rust
/// See https://doc.rust-lang.org/reference/items.html
#[derive(Debug, Eq, Hash, PartialEq)]
enum TopLevelItem {
    Const {
        name: String,
        ty: Rc<CoqType>,
        value: Option<Rc<Expr>>,
    },
    Definition {
        name: String,
        snippet: Option<Rc<Snippet>>,
        definition: Rc<FunDefinition>,
    },
    TypeAlias {
        name: String,
        path: Path,
        ty_params: Vec<String>,
        ty: Rc<CoqType>,
    },
    TypeEnum {
        name: String,
        ty_params: Vec<(String, Option<Rc<CoqType>>)>,
        variants: Vec<(String, Rc<VariantItem>, Option<u128>)>,
    },
    TypeStructStruct(TypeStructStruct),
    TypeStructTuple {
        name: String,
        ty_params: Vec<(String, Option<Rc<CoqType>>)>,
        fields: Vec<Rc<CoqType>>,
    },
    TypeStructUnit {
        name: String,
        ty_params: Vec<(String, Option<Rc<CoqType>>)>,
    },
    Module {
        name: String,
        body: Rc<TopLevel>,
        is_dead_code: bool,
    },
    Impl {
        generic_tys: Vec<String>,
        self_ty: Rc<CoqType>,
        /// We use a counter to disambiguate several impls for the same type
        counter: u64,
        items: Vec<Rc<ImplItem>>,
    },
    Trait {
        name: String,
        path: Path,
        ty_params: Vec<(String, Option<Rc<CoqType>>)>,
        body: Vec<(String, Rc<TraitItem>)>,
    },
    TraitImpl {
        generic_tys: Vec<String>,
        self_ty: Rc<CoqType>,
        of_trait: Path,
        trait_ty_params: Vec<(String, Rc<TraitTyParamValue>)>,
        items: Vec<Rc<TraitImplItem>>,
    },
    Error(String),
}

#[derive(Debug, Eq, Hash, PartialEq)]
struct TypeStructStruct {
    name: String,
    ty_params: Vec<(String, Option<Rc<CoqType>>)>,
    fields: Vec<(String, Rc<CoqType>)>,
    is_dead_code: bool,
}

#[derive(Debug, Eq, Hash, PartialEq)]
pub struct TopLevel(Vec<Rc<TopLevelItem>>);

/// emits a warning with the given messages
fn emit_warning_with_note(env: &Env, span: &rustc_span::Span, warning_msg: &str, note_msg: &str) {
    env.tcx
        .sess
        .struct_span_warn(*span, warning_msg.to_string())
        .note(note_msg.to_string())
        .emit();
}

impl<A> FieldWithDefault<A> {
    fn map<B, F>(&self, f: F) -> FieldWithDefault<B>
    where
        F: FnOnce(&A) -> B,
    {
        match self {
            FieldWithDefault::RequiredValue(a) => FieldWithDefault::RequiredValue(f(a)),
            FieldWithDefault::OptionalValue(a) => FieldWithDefault::OptionalValue(f(a)),
            FieldWithDefault::Default => FieldWithDefault::Default,
        }
    }
}

impl<'a, A> From<&'a FieldWithDefault<Rc<A>>> for Option<&'a A> {
    fn from(val: &'a FieldWithDefault<Rc<A>>) -> Self {
        match val {
            FieldWithDefault::RequiredValue(a) => Some(a),
            FieldWithDefault::OptionalValue(a) => Some(a),
            FieldWithDefault::Default => None,
        }
    }
}

/// compiles a function with the given signature and body
fn compile_fn_sig_and_body<'a>(
    tcx: &TyCtxt<'a>,
    env: &mut Env<'a>,
    fn_sig_and_body: &HirFnSigAndBody,
    default: &str,
    is_axiom: bool,
) -> Rc<FnSigAndBody> {
    let decl = fn_sig_and_body.fn_sig.decl;
    let args = get_args(tcx, env, fn_sig_and_body.body, decl.inputs, default);
    let ret_ty = compile_fn_ret_ty(
        tcx,
        env,
        &fn_sig_and_body.body.value.hir_id.owner.def_id,
        &decl.output,
    );
    let body = compile_function_body(env, &args, fn_sig_and_body.body, ret_ty.clone(), is_axiom);

    Rc::new(FnSigAndBody { args, ret_ty, body })
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

fn check_lint_attribute<'a, Item: Into<rustc_hir::OwnerNode<'a>>>(
    tcx: &TyCtxt,
    item: Item,
    attribute: &str,
) -> bool {
    for attr in tcx.get_attrs(item.into().def_id().to_def_id(), sym::allow) {
        if let AttrKind::Normal(value) = &attr.kind {
            if let AttrArgs::Delimited(value2) = &value.item.args {
                let into_trees = &value2.tokens.trees();
                let in_the_tree = into_trees.look_ahead(0);
                match in_the_tree {
                    Some(res) => {
                        if let rustc_ast::tokenstream::TokenTree::Token(res2, _) = res {
                            if let rustc_ast::token::TokenKind::Ident(a, _) = res2.kind {
                                // since we can have many attributes on top of each piece of code,
                                // when we face the expected attribute, we return [true] right away,
                                // otherwise we keep looking
                                if a.to_string() == attribute {
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
    false
}

// Function checks if code block is having any `allow` attributes, and if it does,
// it returns [true] if one of attributes disables "dead_code" lint.
// Returns [false] if attribute is related to something else
fn check_dead_code_lint_in_attributes<'a, Item: Into<rustc_hir::OwnerNode<'a>>>(
    tcx: &TyCtxt,
    item: Item,
) -> bool {
    check_lint_attribute(tcx, item, "dead_code")
}

fn check_coq_axiom_lint_in_attributes<'a, Item: Into<rustc_hir::OwnerNode<'a>>>(
    tcx: &TyCtxt,
    item: Item,
) -> bool {
    check_lint_attribute(tcx, item, "coq_axiom")
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

fn get_item_ids_for_parent(tcx: &TyCtxt, expected_parent: rustc_hir::def_id::DefId) -> Vec<ItemId> {
    tcx.hir()
        .items()
        .filter(|item_id| {
            let def_id = item_id.owner_id.to_def_id();
            let parent = tcx.opt_parent(def_id).unwrap();

            parent == expected_parent
        })
        .collect()
}

fn compile_top_level_item_without_local_items<'a>(
    tcx: &TyCtxt<'a>,
    env: &mut Env<'a>,
    item: &Item,
) -> Vec<Rc<TopLevelItem>> {
    let name = to_valid_coq_name(item.ident.name.as_str());
    let path = compile_def_id(env, item.owner_id.to_def_id());

    match &item.kind {
        ItemKind::ExternCrate(_) => vec![],
        ItemKind::Use(..) => vec![],
        ItemKind::Static(ty, _, body_id) | ItemKind::Const(ty, _, body_id) => {
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
                let value = compile_hir_id(env, body_id.hir_id);
                Some(value)
            };
            let ty = compile_type(tcx, env, &item.owner_id.def_id, ty);

            let (value, ty) = if let ItemKind::Static(_, mutability, _) = &item.kind {
                (
                    value.map(|value| value.alloc()),
                    CoqType::make_ref(mutability, ty).val(),
                )
            } else {
                (value, ty.val())
            };

            vec![Rc::new(TopLevelItem::Const { name, ty, value })]
        }
        ItemKind::Fn(fn_sig, generics, body_id) => {
            if check_if_is_test_main_function(tcx, body_id) {
                return vec![];
            }

            let snippet = Snippet::of_span(env, &item.span);
            let is_dead_code = check_dead_code_lint_in_attributes(tcx, item);
            let is_axiom = check_coq_axiom_lint_in_attributes(tcx, item);
            let fn_sig_and_body = get_hir_fn_sig_and_body(tcx, fn_sig, body_id);

            vec![Rc::new(TopLevelItem::Definition {
                name,
                snippet,
                definition: FunDefinition::compile(
                    tcx,
                    env,
                    generics,
                    &fn_sig_and_body,
                    "arg",
                    is_dead_code,
                    is_axiom,
                ),
            })]
        }
        ItemKind::Macro(_, _) => vec![],
        ItemKind::Mod(module) => {
            let is_dead_code = check_dead_code_lint_in_attributes(tcx, item);
            let context = get_full_name(tcx, item.hir_id());
            let mut items: Vec<ItemId> = module.item_ids.to_vec();
            reorder_definitions_inplace(tcx, env, &context, &mut items);
            let items: Vec<_> = items
                .iter()
                .flat_map(|item_id| {
                    let item = tcx.hir().item(*item_id);
                    compile_top_level_item(tcx, env, item)
                })
                .collect();

            vec![Rc::new(TopLevelItem::Module {
                name,
                body: Rc::new(TopLevel(items)),
                is_dead_code,
            })]
        }
        ItemKind::ForeignMod { .. } => {
            vec![Rc::new(TopLevelItem::Error("ForeignMod".to_string()))]
        }
        ItemKind::GlobalAsm(_) => vec![Rc::new(TopLevelItem::Error("GlobalAsm".to_string()))],
        ItemKind::TyAlias(ty, generics) => vec![Rc::new(TopLevelItem::TypeAlias {
            name,
            path,
            ty: compile_type(tcx, env, &item.owner_id.def_id, ty),
            ty_params: get_ty_params_names(tcx, env, generics),
        })],
        ItemKind::OpaqueTy(_) => vec![Rc::new(TopLevelItem::Error("OpaqueTy".to_string()))],
        ItemKind::Enum(enum_def, generics) => {
            let ty_params = get_ty_params(tcx, env, &item.owner_id.def_id, generics);
            vec![Rc::new(TopLevelItem::TypeEnum {
                name,
                ty_params,
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
                                        (
                                            field.ident.to_string(),
                                            compile_type(tcx, env, &item.owner_id.def_id, field.ty),
                                        )
                                    })
                                    .collect();
                                VariantItem::Struct { fields }
                            }
                            VariantData::Tuple(fields, _, _) => {
                                let tys = fields
                                    .iter()
                                    .map(|field| {
                                        compile_type(tcx, env, &item.owner_id.def_id, field.ty)
                                    })
                                    .collect();
                                VariantItem::Tuple { tys }
                            }
                            VariantData::Unit(_, _) => VariantItem::Tuple { tys: vec![] },
                        };
                        let discriminant = match &variant.disr_expr {
                            None => None,
                            Some(annon_const) => {
                                let body = env.tcx.hir().body(annon_const.body);
                                let value = body.value;

                                match value.kind {
                                    rustc_hir::ExprKind::Lit(rustc_span::source_map::Spanned {
                                        node: rustc_ast::ast::LitKind::Int(discriminant, _),
                                        ..
                                    }) => Some(*discriminant),
                                    _ => None,
                                }
                            }
                        };

                        (name, Rc::new(fields), discriminant)
                    })
                    .collect(),
            })]
        }
        ItemKind::Struct(body, generics) => {
            let is_dead_code = check_dead_code_lint_in_attributes(tcx, item);
            let ty_params = get_ty_params(tcx, env, &item.owner_id.def_id, generics);

            match body {
                VariantData::Struct(fields, _) => {
                    if fields.is_empty() {
                        return vec![Rc::new(TopLevelItem::TypeStructUnit { name, ty_params })];
                    }
                    let fields = fields
                        .iter()
                        .map(|field| {
                            (
                                to_valid_coq_name(field.ident.name.as_str()),
                                compile_type(tcx, env, &item.owner_id.def_id, field.ty),
                            )
                        })
                        .collect();
                    vec![Rc::new(TopLevelItem::TypeStructStruct(TypeStructStruct {
                        name,
                        ty_params,
                        fields,
                        is_dead_code,
                    }))]
                }
                VariantData::Tuple(fields, _, _) => {
                    vec![Rc::new(TopLevelItem::TypeStructTuple {
                        name,
                        ty_params,
                        fields: fields
                            .iter()
                            .map(|field| compile_type(tcx, env, &item.owner_id.def_id, field.ty))
                            .collect(),
                    })]
                }
                VariantData::Unit(_, _) => {
                    vec![Rc::new(TopLevelItem::TypeStructUnit { name, ty_params })]
                }
            }
        }
        ItemKind::Union(_, _) => vec![Rc::new(TopLevelItem::Error("Union".to_string()))],
        ItemKind::Trait(_, _, generics, _, items) => {
            vec![Rc::new(TopLevelItem::Trait {
                name,
                path,
                ty_params: get_ty_params(tcx, env, &item.owner_id.def_id, generics),
                body: items
                    .iter()
                    .map(|item| {
                        let item = tcx.hir().trait_item(item.id);
                        let ty_params = get_ty_params_names(tcx, env, item.generics);
                        let body = compile_trait_item_body(tcx, env, ty_params, item);
                        (to_valid_coq_name(item.ident.name.as_str()), body)
                    })
                    .collect(),
            })]
        }
        ItemKind::TraitAlias(_, _) => {
            vec![Rc::new(TopLevelItem::Error("TraitAlias".to_string()))]
        }
        ItemKind::Impl(Impl {
            generics,
            of_trait,
            self_ty,
            items,
            ..
        }) => {
            let is_dead_code = check_dead_code_lint_in_attributes(tcx, item);
            let generic_tys = get_ty_params_names(tcx, env, generics);
            let self_ty = compile_type(tcx, env, &item.owner_id.def_id, self_ty);
            let mut items: Vec<ImplItemRef> = items.to_vec();
            let context = get_full_name(tcx, item.hir_id());
            reorder_definitions_inplace(tcx, env, &context, &mut items);

            // Add the current trait to the environment to be recognized latter
            // in the translation of expressions.
            if let Some(trait_ref) = of_trait {
                let trait_path = compile_path(env, trait_ref.path);
                env.current_trait_impl = Some((trait_path, self_ty.clone()));
            }

            let items = compile_impl_item_refs(tcx, env, &items, is_dead_code);
            env.current_trait_impl = None;

            match of_trait {
                Some(trait_ref) => {
                    let rustc_default_item_names: Vec<String> = tcx
                        .associated_items(trait_ref.trait_def_id().unwrap())
                        .in_definition_order()
                        .filter(|item| item.defaultness(*tcx).has_value())
                        .map(|item| to_valid_coq_name(item.name.as_str()))
                        .collect();
                    let items: Vec<Rc<TraitImplItem>> = items
                        .iter()
                        .map(|item| {
                            let has_default = rustc_default_item_names
                                .iter()
                                .any(|default_item_name| &item.name == default_item_name);
                            let kind = Rc::new(if has_default {
                                FieldWithDefault::OptionalValue(item.kind.clone())
                            } else {
                                FieldWithDefault::RequiredValue(item.kind.clone())
                            });
                            Rc::new(TraitImplItem {
                                name: item.name.clone(),
                                snippet: item.snippet.clone(),
                                kind,
                            })
                        })
                        // We now add the elements that have a default value and are not in the
                        // list of definitions
                        .chain(
                            rustc_default_item_names
                                .iter()
                                .filter(|default_item_name| {
                                    !items.iter().any(|item| &item.name == *default_item_name)
                                })
                                .map(|default_item_name| {
                                    let kind = Rc::new(FieldWithDefault::Default);
                                    Rc::new(TraitImplItem {
                                        name: default_item_name.clone(),
                                        snippet: None,
                                        kind,
                                    })
                                }),
                        )
                        .collect();

                    // Get the generics for the trait
                    let trait_generics = tcx.generics_of(trait_ref.trait_def_id().unwrap());

                    vec![Rc::new(TopLevelItem::TraitImpl {
                        generic_tys,
                        self_ty,
                        of_trait: compile_path(env, trait_ref.path),
                        trait_ty_params: get_ty_params_with_default_status(
                            tcx,
                            env,
                            &item.owner_id.def_id,
                            trait_generics,
                            trait_ref.path,
                        ),
                        items,
                    })]
                }
                None => {
                    let counter_entry = env.impl_counter.entry(self_ty.clone());
                    let counter = *counter_entry
                        .and_modify(|counter| *counter += 1)
                        .or_insert(1);
                    vec![Rc::new(TopLevelItem::Impl {
                        generic_tys,
                        self_ty,
                        counter,
                        items,
                    })]
                }
            }
        }
    }
}

/// [compile_top_level_item] compiles hir [Item]s into coq-of-rust (optional)
/// items.
/// - See https://doc.rust-lang.org/stable/nightly-rustc/rustc_hir/struct.Item.html
///   and the doc for [TopLevelItem]
/// - [rustc_middle::hir::map::Map] is intuitively the type for hir environments
/// - Method [body] allows retrievient the body of an identifier [body_id] in an
///   hir environment [hir]
// @TODO: the argument `tcx` is included in `env` and should thus be removed
fn compile_top_level_item<'a>(
    tcx: &TyCtxt<'a>,
    env: &mut Env<'a>,
    item: &Item,
) -> Vec<Rc<TopLevelItem>> {
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

    // Sometimes there can be local items, for example a struct defined in the
    // body of a function. For modules, we make an exception as modules are
    // expected to have items. We will concatenate the local items directly after
    // the item's translation.
    let local_item_ids = match &item.kind {
        ItemKind::Mod(_) => vec![],
        _ => get_item_ids_for_parent(tcx, item.item_id().owner_id.to_def_id()),
    };
    let local_items = local_item_ids
        .into_iter()
        .flat_map(|item_id| {
            let item = tcx.hir().item(item_id);
            compile_top_level_item(tcx, env, item)
        })
        .collect();

    let items = compile_top_level_item_without_local_items(tcx, env, item);

    [items, local_items].concat()
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
fn compile_impl_item_refs<'a>(
    tcx: &TyCtxt<'a>,
    env: &mut Env<'a>,
    item_refs: &[ImplItemRef],
    is_dead_code: bool,
) -> Vec<Rc<ImplItem>> {
    item_refs
        .iter()
        .map(|item_ref| compile_impl_item(tcx, env, tcx.hir().impl_item(item_ref.id), is_dead_code))
        .collect()
}

/// compiles an item
fn compile_impl_item<'a>(
    tcx: &TyCtxt<'a>,
    env: &mut Env<'a>,
    item: &rustc_hir::ImplItem,
    is_dead_code: bool,
) -> Rc<ImplItem> {
    let name = to_valid_coq_name(item.ident.name.as_str());
    let snippet = Snippet::of_span(env, &item.span);
    let is_axiom = check_coq_axiom_lint_in_attributes(tcx, item);
    let kind = match &item.kind {
        rustc_hir::ImplItemKind::Const(ty, body_id) => {
            let ty = compile_type(tcx, env, &item.owner_id.def_id, ty);
            let body = if env.axiomatize {
                None
            } else {
                Some(compile_hir_id(env, body_id.hir_id))
            };
            Rc::new(ImplItemKind::Const {
                ty,
                body,
                is_dead_code,
            })
        }
        rustc_hir::ImplItemKind::Fn(fn_sig, body_id) => Rc::new(ImplItemKind::Definition {
            definition: FunDefinition::compile(
                tcx,
                env,
                item.generics,
                &get_hir_fn_sig_and_body(tcx, fn_sig, body_id),
                "Pattern",
                is_dead_code,
                is_axiom,
            ),
        }),
        rustc_hir::ImplItemKind::Type(ty) => Rc::new(ImplItemKind::Type {
            ty: compile_type(tcx, env, &item.owner_id.def_id, ty),
        }),
    };
    Rc::new(ImplItem {
        name,
        snippet,
        kind,
    })
}

/// returns the body corresponding to the given body_id
fn get_body<'a>(tcx: &'a TyCtxt, body_id: &rustc_hir::BodyId) -> &'a rustc_hir::Body<'a> {
    tcx.hir().body(*body_id)
}

// compiles the body of a function
fn compile_function_body(
    env: &mut Env,
    args: &[(String, Rc<CoqType>)],
    body: &rustc_hir::Body,
    ret_ty: Rc<CoqType>,
    is_axiom: bool,
) -> Option<Rc<Expr>> {
    if env.axiomatize || is_axiom {
        return None;
    }
    let body = compile_hir_id(env, body.value.hir_id).read();
    let has_return = body.has_return();
    let body = if has_return {
        Rc::new(Expr {
            kind: Rc::new(ExprKind::Let {
                is_monadic: false,
                name: Some("return_".to_string()),
                init: Rc::new(Expr {
                    kind: Rc::new(ExprKind::VarWithTy {
                        path: Path::local("M.return_"),
                        ty_name: "R".to_string(),
                        ty: ret_ty,
                    }),
                    ty: None,
                }),
                body: Rc::new(Expr {
                    kind: Rc::new(ExprKind::MonadicOperator {
                        name: "M.catch_return".to_string(),
                        arg: body,
                    }),
                    ty: None,
                }),
            }),
            ty: None,
        })
    } else {
        body
    };
    let body = crate::thir_expression::allocate_bindings(
        &args
            .iter()
            .map(|(name, _)| name.clone())
            .collect::<Vec<_>>(),
        body,
    );

    Some(body)
}

/// returns a list of pairs of argument names and their types
fn get_args<'a>(
    tcx: &TyCtxt<'a>,
    env: &Env<'a>,
    body: &rustc_hir::Body,
    inputs: &[rustc_hir::Ty],
    default: &str,
) -> Vec<(String, Rc<CoqType>)> {
    let local_def_id = body.value.hir_id.owner.def_id;

    get_arg_names(body, default)
        .zip(
            inputs
                .iter()
                .map(|ty| compile_type(tcx, env, &local_def_id, ty)),
        )
        .collect()
}

/// returns names of the arguments
fn get_arg_names<'a>(
    body: &'a rustc_hir::Body,
    default: &'a str,
) -> impl Iterator<Item = String> + 'a {
    body.params.iter().map(|param| match param.pat.kind {
        PatKind::Binding(_, _, ident, _) => to_valid_coq_name(ident.name.as_str()),
        _ => default.to_string(),
    })
}

/// filters out type parameters and compiles them with the given function
fn compile_ty_params<'a, T>(
    tcx: &TyCtxt<'a>,
    env: &Env<'a>,
    generics: &rustc_hir::Generics,
    f: impl Fn(&TyCtxt<'a>, &Env<'a>, String, Option<&Ty>) -> T,
) -> Vec<T> {
    generics
        .params
        .iter()
        .filter_map(|param| match param.kind {
            // we ignore lifetimes
            GenericParamKind::Type { default, .. } => {
                Some(f(tcx, env, param.name.ident().to_string(), default))
            }
            GenericParamKind::Lifetime { .. } | GenericParamKind::Const { .. } => None,
        })
        .collect()
}

/// extracts type parameters with their optional default value from the generics
fn get_ty_params<'a>(
    tcx: &TyCtxt<'a>,
    env: &Env<'a>,
    local_def_id: &rustc_hir::def_id::LocalDefId,
    generics: &rustc_hir::Generics,
) -> Vec<(String, Option<Rc<CoqType>>)> {
    compile_ty_params(tcx, env, generics, |tcx, env, name, default| {
        let default = default.map(|default| compile_type(tcx, env, local_def_id, default));
        let name = to_valid_coq_name(&name);
        (name, default)
    })
}

/// extracts the names of type parameters from the generics
fn get_ty_params_names<'a>(
    tcx: &TyCtxt<'a>,
    env: &Env<'a>,
    generics: &rustc_hir::Generics,
) -> Vec<String> {
    compile_ty_params(tcx, env, generics, |_, _, name, _| to_valid_coq_name(&name))
}

/// [compile_generic_bounds] compiles generic bounds in [compile_trait_item_body]
fn compile_generic_bounds<'a>(
    tcx: &TyCtxt<'a>,
    env: &Env<'a>,
    generic_bounds: GenericBounds,
) -> Vec<Rc<TraitBound>> {
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
fn get_ty_params_with_default_status<'a>(
    tcx: &TyCtxt<'a>,
    env: &Env<'a>,
    local_def_id: &rustc_hir::def_id::LocalDefId,
    generics: &rustc_middle::ty::Generics,
    path: &rustc_hir::Path,
) -> Vec<(String, Rc<TraitTyParamValue>)> {
    let mut type_params_name_and_default_status = get_type_params_name_and_default_status(generics);
    // The first type parameter is always the Self type, that we do not consider as
    // part of the list of type parameters.
    type_params_name_and_default_status.remove(0);

    let ty_params = compile_path_ty_params(tcx, env, local_def_id, path);
    add_default_status_to_ty_params(&ty_params, &type_params_name_and_default_status)
}

/// takes a list of actual type parameters
/// and the information about required and default type parameters
/// and returns a list that combines them
pub(crate) fn add_default_status_to_ty_params(
    ty_params: &[Rc<CoqType>],
    names_and_default_status: &[(String, bool)],
) -> Vec<(String, Rc<TraitTyParamValue>)> {
    ty_params
        .iter()
        .map(Some)
        .chain(repeat(None))
        .zip(names_and_default_status)
        .map(|(ty, (name, has_default))| compile_ty_param_value(name, ty.cloned(), has_default))
        .collect()
}

/// compiles a type parameter
fn compile_ty_param_value(
    name: &str,
    ty: Option<Rc<CoqType>>,
    has_default: &bool,
) -> (String, Rc<TraitTyParamValue>) {
    let name = name.to_string();
    let ty = match ty {
        Some(ty) => {
            if *has_default {
                FieldWithDefault::OptionalValue(ty)
            } else {
                FieldWithDefault::RequiredValue(ty)
            }
        }
        None => FieldWithDefault::Default,
    };
    (name, Rc::new(ty))
}

/// Get the list of type parameters names and default status (true if it has a default)
pub(crate) fn get_type_params_name_and_default_status(
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
fn compile_trait_item_body<'a>(
    tcx: &TyCtxt<'a>,
    env: &mut Env<'a>,
    ty_params: Vec<String>,
    item: &rustc_hir::TraitItem,
) -> Rc<TraitItem> {
    match &item.kind {
        TraitItemKind::Const(ty, _) => Rc::new(TraitItem::Definition {
            ty_params,
            ty: compile_type(tcx, env, &item.owner_id.def_id, ty),
        }),
        TraitItemKind::Fn(fn_sig, trait_fn) => match trait_fn {
            TraitFn::Required(_) => Rc::new(TraitItem::Definition {
                ty_params,
                ty: compile_fn_decl(tcx, env, &item.owner_id.def_id, fn_sig.decl),
            }),
            TraitFn::Provided(body_id) => {
                let env_tcx = env.tcx;
                let fn_sig_and_body = get_hir_fn_sig_and_body(&env_tcx, fn_sig, body_id);
                let signature_and_body =
                    compile_fn_sig_and_body(tcx, env, &fn_sig_and_body, "arg", false);
                Rc::new(TraitItem::DefinitionWithDefault(Rc::new(FunDefinition {
                    ty_params,
                    signature_and_body,
                    is_dead_code: false,
                })))
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
            Rc::new(TraitItem::Type(generic_bounds))
        }
    }
}

fn compile_top_level(tcx: &TyCtxt, opts: TopLevelOptions) -> Rc<TopLevel> {
    let mut env = Env {
        impl_counter: HashMap::new(),
        tcx: *tcx,
        axiomatize: opts.axiomatize,
        axiomatize_public: opts.axiomatize_public,
        file: opts.filename,
        reorder_map: HashMap::new(),
        configuration: get_configuration(&opts.configuration_file),
        current_trait_impl: None,
    };

    let mut results = get_item_ids_for_parent(tcx, rustc_hir::def_id::CRATE_DEF_ID.into());
    reorder_definitions_inplace(tcx, &mut env, "top_level", &mut results);

    let results = results
        .iter()
        .flat_map(|item_id| {
            let item = tcx.hir().item(*item_id);
            compile_top_level_item(tcx, &mut env, item)
        })
        .collect();

    if opts.generate_reorder {
        let json = serde_json::json!({ "reorder": HashMap::from([(env.file.to_string(), env.reorder_map)])});
        println!("{}", serde_json::to_string_pretty(&json).expect("json"));
    }
    Rc::new(TopLevel(results))
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

fn mt_impl_item(item: Rc<ImplItemKind>) -> Rc<ImplItemKind> {
    match item.as_ref() {
        ImplItemKind::Const {
            ty,
            body,
            is_dead_code,
        } => {
            let body = match body {
                None => body.clone(),
                Some(body) => {
                    let body = mt_expression(FreshVars::new(), body.clone()).0;

                    Some(body)
                }
            };
            Rc::new(ImplItemKind::Const {
                ty: mt_ty(ty.clone()),
                body,
                is_dead_code: *is_dead_code,
            })
        }
        ImplItemKind::Definition { definition } => Rc::new(ImplItemKind::Definition {
            definition: definition.mt(),
        }),
        ImplItemKind::Type { .. } => item,
    }
}

impl FnSigAndBody {
    fn mt(&self) -> Rc<Self> {
        Rc::new(FnSigAndBody {
            args: self
                .args
                .iter()
                .map(|(name, ty)| (name.clone(), mt_ty(ty.clone())))
                .collect(),
            ret_ty: Rc::new(CoqType::Monad(mt_ty(self.ret_ty.clone()))),
            body: match &self.body {
                None => self.body.clone(),
                Some(body) => {
                    let (body, _fresh_vars) = mt_expression(FreshVars::new(), body.clone());
                    Some(body)
                }
            },
        })
    }
}

fn mt_trait_item(body: Rc<TraitItem>) -> Rc<TraitItem> {
    match body.as_ref() {
        TraitItem::Definition { ty_params, ty } => Rc::new(TraitItem::Definition {
            ty_params: ty_params.clone(),
            ty: mt_ty(ty.clone()),
        }),
        TraitItem::Type(x) => Rc::new(TraitItem::Type(x.clone())), // TODO: apply monadic transform
        TraitItem::DefinitionWithDefault(fun_definition) => {
            Rc::new(TraitItem::DefinitionWithDefault(fun_definition.mt()))
        }
    }
}

fn mt_trait_items(body: Vec<(String, Rc<TraitItem>)>) -> Vec<(String, Rc<TraitItem>)> {
    body.into_iter()
        .map(|(s, item)| (s, mt_trait_item(item)))
        .collect()
}

/// Monad transform for [TopLevelItem]
fn mt_top_level_item(item: Rc<TopLevelItem>) -> Rc<TopLevelItem> {
    match item.as_ref() {
        TopLevelItem::Const { name, ty, value } => Rc::new(TopLevelItem::Const {
            name: name.clone(),
            ty: ty.clone(),
            value: match value {
                None => value.clone(),
                Some(value) => {
                    let (value, _fresh_vars) = mt_expression(FreshVars::new(), value.clone());
                    Some(value)
                }
            },
        }),
        TopLevelItem::Definition {
            name,
            snippet,
            definition,
        } => Rc::new(TopLevelItem::Definition {
            name: name.clone(),
            snippet: snippet.clone(),
            definition: definition.mt(),
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
        } => Rc::new(TopLevelItem::Module {
            name: name.clone(),
            body: mt_top_level(body.clone()),
            is_dead_code: *is_dead_code,
        }),
        TopLevelItem::Impl {
            generic_tys,
            self_ty,
            counter,
            items,
        } => Rc::new(TopLevelItem::Impl {
            generic_tys: generic_tys.clone(),
            self_ty: self_ty.clone(),
            counter: *counter,
            items: items
                .iter()
                .map(|item| {
                    Rc::new(ImplItem {
                        name: item.name.clone(),
                        snippet: item.snippet.clone(),
                        kind: mt_impl_item(item.kind.clone()),
                    })
                })
                .collect(),
        }),
        TopLevelItem::Trait {
            name,
            path,
            ty_params,
            body,
        } => Rc::new(TopLevelItem::Trait {
            name: name.clone(),
            path: path.clone(),
            ty_params: ty_params.clone(),
            body: mt_trait_items(body.clone()),
        }),
        TopLevelItem::TraitImpl {
            generic_tys,
            self_ty,
            of_trait,
            trait_ty_params,
            items,
        } => Rc::new(TopLevelItem::TraitImpl {
            generic_tys: generic_tys.clone(),
            self_ty: self_ty.clone(),
            of_trait: of_trait.clone(),
            trait_ty_params: trait_ty_params.clone(),
            items: items
                .iter()
                .map(|item| {
                    Rc::new(TraitImplItem {
                        name: item.name.clone(),
                        snippet: item.snippet.clone(),
                        kind: Rc::new(item.kind.map(|item| mt_impl_item(item.clone()))),
                    })
                })
                .collect(),
        }),
        TopLevelItem::Error(_) => item,
    }
}

fn mt_top_level(top_level: Rc<TopLevel>) -> Rc<TopLevel> {
    Rc::new(TopLevel(
        top_level
            .0
            .clone()
            .into_iter()
            .map(mt_top_level_item)
            .collect(),
    ))
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
        let predicates = [self.predicates.clone(), vec![(path, full_name.clone())]].concat();
        self.predicates = predicates;
        self.name = next_letter;
        full_name
    }

    fn get_type_parm_list(&self) -> Vec<String> {
        self.predicates
            .iter()
            .map(|(_, dyn_name)| dyn_name.clone())
            .collect()
    }

    fn make_dyn_parm(&mut self, arg: Rc<CoqType>) -> Rc<CoqType> {
        if let Some((name, arg, is_alias)) = arg.clone().match_ref() {
            let ct = self.make_dyn_parm(arg);
            Rc::new(CoqType::Application {
                func: CoqType::path(&[&name]),
                args: vec![ct],
                is_alias,
            })
        } else if let CoqType::Dyn(path) = arg.as_ref() {
            // We suppose `dyn` is only associated with one trait so we can directly extract the first element
            if let Some(path) = path.first() {
                let dy_name = self.next(path.clone());
                Rc::new(CoqType::Var(dy_name))
            } else {
                // NOTE: cannot use `arg` directly because it is partially borrowed. Can it be fixed?
                Rc::new(CoqType::Dyn(path.clone()))
            }
        } else {
            arg
        }
    }
}

impl FunDefinition {
    /// compiles a given function
    fn compile<'a>(
        tcx: &TyCtxt<'a>,
        env: &mut Env<'a>,
        generics: &rustc_hir::Generics,
        fn_sig_and_body: &HirFnSigAndBody,
        default: &str,
        is_dead_code: bool,
        is_axiom: bool,
    ) -> Rc<Self> {
        let mut dyn_name_gen = DynNameGen::new("T".to_string());
        let FnSigAndBody { args, ret_ty, body } =
            &*compile_fn_sig_and_body(tcx, env, fn_sig_and_body, default, is_axiom);
        let args = args.iter().fold(vec![], |result, (string, ty)| {
            let ty = dyn_name_gen.make_dyn_parm(ty.clone());
            [result, vec![(string.to_owned(), ty)]].concat()
        });
        let ty_params = [
            get_ty_params_names(tcx, env, generics),
            dyn_name_gen.get_type_parm_list(),
        ]
        .concat();

        let signature_and_body = Rc::new(FnSigAndBody {
            args,
            ret_ty: ret_ty.clone(),
            body: body.clone(),
        });

        Rc::new(FunDefinition {
            ty_params,
            signature_and_body,
            is_dead_code,
        })
    }

    fn mt(&self) -> Rc<Self> {
        Rc::new(FunDefinition {
            ty_params: self.ty_params.clone(),
            signature_and_body: self.signature_and_body.mt(),
            is_dead_code: self.is_dead_code,
        })
    }

    /// The generics [generic_tys] are not part of the definition itself, but
    /// come from above, for example from the generics of the enclosing `impl`.
    fn to_coq<'a>(
        &'a self,
        name: &'a str,
        snippet: &'a Option<Rc<Snippet>>,
        generic_tys: Vec<String>,
    ) -> coq::TopLevel<'a> {
        coq::TopLevel::new(
            &[
                match snippet {
                    Some(snippet) => snippet.to_coq(),
                    None => vec![],
                },
                optional_insert_vec(
                    !self.is_dead_code,
                    vec![coq::TopLevelItem::Comment(coq::Comment::new(
                        "#[allow(dead_code)] - function was ignored by the compiler",
                    ))],
                ),
                match &self.signature_and_body.body {
                    None => vec![coq::TopLevelItem::Definition(coq::Definition::new(
                        name,
                        &coq::DefinitionKind::Assumption {
                            ty: coq::Expression::PiType {
                                args: vec![],
                                image: Rc::new(coq::Expression::FunctionType {
                                    domains: vec![
                                        coq::Expression::just_name("list")
                                            .apply(&coq::Expression::just_name("Ty.t")),
                                        coq::Expression::just_name("list")
                                            .apply(&coq::Expression::just_name("Value.t")),
                                    ],
                                    image: Rc::new(coq::Expression::just_name("M")),
                                }),
                            },
                        },
                    ))],
                    Some(body) => vec![coq::TopLevelItem::Definition(coq::Definition::new(
                        name,
                        &coq::DefinitionKind::Alias {
                            args: vec![
                                coq::ArgDecl::new(
                                    &coq::ArgDeclVar::Simple {
                                        idents: vec!["𝜏".to_string()],
                                        ty: Some(
                                            coq::Expression::just_name("list")
                                                .apply(&coq::Expression::just_name("Ty.t")),
                                        ),
                                    },
                                    coq::ArgSpecKind::Explicit,
                                ),
                                coq::ArgDecl::new(
                                    &coq::ArgDeclVar::Simple {
                                        idents: vec!["α".to_string()],
                                        ty: Some(
                                            coq::Expression::just_name("list")
                                                .apply(&coq::Expression::just_name("Value.t")),
                                        ),
                                    },
                                    coq::ArgSpecKind::Explicit,
                                ),
                            ],
                            ty: Some(coq::Expression::just_name("M")),
                            body: coq::Expression::Match {
                                scrutinees: vec![
                                    coq::Expression::just_name("𝜏"),
                                    coq::Expression::just_name("α"),
                                ],
                                arms: vec![
                                    (
                                        vec![
                                            coq::Expression::List {
                                                exprs: [generic_tys, self.ty_params.clone()]
                                                    .concat()
                                                    .iter()
                                                    .map(|ty_param| {
                                                        coq::Expression::just_name(ty_param)
                                                    })
                                                    .collect(),
                                            },
                                            coq::Expression::List {
                                                exprs: self
                                                    .signature_and_body
                                                    .args
                                                    .iter()
                                                    .map(|(name, _)| {
                                                        coq::Expression::just_name(name)
                                                    })
                                                    .collect(),
                                            },
                                        ],
                                        coq::Expression::Code(body.to_doc(false)),
                                    ),
                                    (
                                        vec![coq::Expression::Wild, coq::Expression::Wild],
                                        coq::Expression::just_name("M.impossible"),
                                    ),
                                ],
                            },
                        },
                    ))],
                },
            ]
            .concat(),
        )
    }

    fn to_doc<'a>(
        &'a self,
        name: &'a str,
        snippet: &'a Option<Rc<Snippet>>,
        generic_tys: Vec<String>,
    ) -> Doc<'a> {
        self.to_coq(name, snippet, generic_tys).to_doc()
    }
}

impl ImplItemKind {
    fn to_coq<'a>(&'a self, name: &'a str, generic_tys: Vec<String>) -> coq::TopLevel<'a> {
        match self {
            ImplItemKind::Const {
                ty,
                body,
                is_dead_code,
            } => coq::TopLevel::concat(&[coq::TopLevel::new(&[
                coq::TopLevelItem::Code(optional_insert(
                    !*is_dead_code,
                    concat([
                        text("(* #[allow(dead_code)] - function was ignored by the compiler *)"),
                        hardline(),
                    ]),
                )),
                match body {
                    None => coq::TopLevelItem::Definition(coq::Definition::new(
                        name,
                        &coq::DefinitionKind::Assumption { ty: ty.to_coq() },
                    )),
                    Some(body) => coq::TopLevelItem::Definition(coq::Definition::new(
                        name,
                        &coq::DefinitionKind::Alias {
                            args: vec![],
                            ty: Some(ty.to_coq()),
                            body: coq::Expression::Code(nest([
                                text("M.run"),
                                line(),
                                body.to_doc(true),
                            ])),
                        },
                    )),
                },
            ])]),
            ImplItemKind::Definition { definition, .. } => {
                coq::TopLevel::new(&[coq::TopLevelItem::Code(definition.to_doc(
                    name,
                    &None,
                    generic_tys,
                ))])
            }
            ImplItemKind::Type { ty } => {
                coq::TopLevel::new(&[coq::TopLevelItem::Definition(coq::Definition::new(
                    name,
                    &coq::DefinitionKind::Alias {
                        args: vec![],
                        ty: Some(coq::Expression::Set),
                        body: coq::Expression::Code(nest([ty.to_coq().to_doc(false)])),
                    },
                ))])
            }
        }
    }

    fn to_doc<'a>(&'a self, name: &'a str, generic_tys: Vec<String>) -> Doc {
        self.to_coq(name, generic_tys).to_doc()
    }
}

impl TraitBound {
    /// Get the generics for the trait
    fn compile<'a>(
        tcx: &TyCtxt<'a>,
        env: &Env<'a>,
        ptraitref: &rustc_hir::PolyTraitRef,
    ) -> Rc<TraitBound> {
        Rc::new(TraitBound {
            name: compile_path(env, ptraitref.trait_ref.path),
            ty_params: get_ty_params_with_default_status(
                tcx,
                env,
                &ptraitref.trait_ref.hir_ref_id.owner.def_id,
                tcx.generics_of(ptraitref.trait_ref.trait_def_id().unwrap()),
                ptraitref.trait_ref.path,
            ),
        })
    }

    fn to_coq<'a>(&self, self_ty: coq::Expression<'a>) -> coq::Expression<'a> {
        coq::Expression::Application {
            func: Rc::new(
                coq::Expression::Variable {
                    ident: Path::concat(&[self.name.to_owned(), Path::new(&["Trait"])]),
                    no_implicit: false,
                }
                .apply(&self_ty),
            ),
            args: self
                .ty_params
                .iter()
                .map(|(name, ty_param)| match ty_param.as_ref() {
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

impl Snippet {
    fn of_span(env: &Env, span: &rustc_span::Span) -> Option<Rc<Self>> {
        if env.axiomatize {
            return None;
        }

        let source_map = env.tcx.sess.source_map();
        let snippet = match (
            source_map.span_to_margin(*span),
            source_map.span_to_snippet(*span),
        ) {
            (Some(margin), Result::Ok(snippet)) => (" ".repeat(margin) + &snippet)
                .split('\n')
                .map(|line| line.to_string())
                .collect::<Vec<_>>(),
            _ => vec!["Rust source not found".to_string()],
        };

        Some(Rc::new(Snippet(snippet)))
    }

    fn to_coq(&self) -> Vec<coq::TopLevelItem> {
        let nb_quotes = self
            .0
            .iter()
            .map(|line| line.chars().filter(|c| *c == '"').count())
            .sum::<usize>();

        [
            vec![coq::TopLevelItem::Code(text("(*"))],
            self.0
                .iter()
                // We do this replace to avoid messing up with the Coq comments
                .map(|line| {
                    coq::TopLevelItem::Code(text(line.replace("(*", "( *").replace("*)", "* )")))
                })
                .collect(),
            if nb_quotes % 2 == 0 {
                vec![]
            } else {
                vec![coq::TopLevelItem::Code(text("\""))]
            },
            vec![coq::TopLevelItem::Code(text("*)"))],
        ]
        .concat()
    }
}

impl TopLevelItem {
    fn to_doc(&self, to_doc_context: ToDocContext) -> Doc {
        match self {
            TopLevelItem::Const { name, ty, value } => match value {
                None => coq::TopLevel::new(&[coq::TopLevelItem::Definition(coq::Definition::new(
                    name,
                    &coq::DefinitionKind::Assumption {
                        ty: coq::Expression::just_name("Value.t"),
                    },
                ))])
                .to_doc(),
                Some(value) => {
                    coq::TopLevel::new(&[coq::TopLevelItem::Definition(coq::Definition::new(
                        name,
                        &coq::DefinitionKind::Alias {
                            args: vec![],
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
            TopLevelItem::Definition {
                name,
                snippet,
                definition,
            } => definition.to_doc(name, snippet, vec![]),
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
                        optional_insert_vec(
                            !*is_dead_code,
                            vec![coq::TopLevelItem::Comment(coq::Comment::new(
                                "#[allow(dead_code)] - module was ignored by the compiler",
                            ))],
                        ),
                        vec![coq::TopLevelItem::Module(coq::Module::new_with_repeat(
                            name,
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
                path,
                ty,
                ty_params,
            } => coq::TopLevel::new(&[coq::TopLevelItem::Definition(coq::Definition::new(
                name,
                &coq::DefinitionKind::Axiom {
                    ty: coq::Expression::PiType {
                        args: vec![coq::ArgDecl::of_ty_params(
                            ty_params,
                            coq::ArgSpecKind::Explicit,
                        )],
                        image: Rc::new(coq::Expression::Equality {
                            lhs: Rc::new(
                                coq::Expression::just_name("Ty.path")
                                    .apply(&coq::Expression::String(path.to_string())),
                            ),
                            rhs: Rc::new(ty.to_coq()),
                        }),
                    },
                },
            ))])
            .to_doc(),
            TopLevelItem::TypeEnum {
                name,
                ty_params,
                variants,
            } => text(format!("(* Enum {name} *)")),
            TopLevelItem::TypeStructStruct(tss) => text(format!("(* Enum {} *)", tss.name)),
            TopLevelItem::TypeStructTuple {
                name,
                ty_params,
                fields,
            } => text(format!("(* Struct {name} *)")),
            TopLevelItem::TypeStructUnit { name, ty_params } => {
                text(format!("(* Struct {name} *)"))
            }
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
                let applied_self_coq = coq::Expression::just_name("Self").apply_many(
                    &generic_tys
                        .iter()
                        .map(|generic_ty| coq::Expression::just_name(generic_ty))
                        .collect_vec(),
                );
                let items_coq = items
                    .iter()
                    .flat_map(|item| {
                        let ImplItem {
                            name,
                            snippet,
                            kind,
                        } = item.as_ref();
                        [
                            vec![coq::TopLevelItem::Line],
                            match snippet {
                                None => vec![],
                                Some(snippet) => snippet.to_coq(),
                            },
                            vec![
                                coq::TopLevelItem::Code(concat([kind.to_doc(
                                    name,
                                    [vec!["Self".to_string()], generic_tys.clone()].concat(),
                                )])),
                                coq::TopLevelItem::Line,
                                coq::TopLevelItem::Definition(coq::Definition::new(
                                    &format!("AssociatedFunction_{name}"),
                                    &coq::DefinitionKind::Axiom {
                                        ty: coq::Expression::PiType {
                                            args: vec![coq::ArgDecl::of_ty_params(
                                                generic_tys,
                                                coq::ArgSpecKind::Explicit,
                                            )],
                                            image: Rc::new(
                                                coq::Expression::just_name(
                                                    "M.IsAssociatedFunction",
                                                )
                                                .apply_many(&[
                                                    applied_self_coq.clone(),
                                                    coq::Expression::String(name.to_string()),
                                                    coq::Expression::just_name(name),
                                                    coq::Expression::List {
                                                        exprs: generic_tys
                                                            .iter()
                                                            .map(|generic_ty| {
                                                                coq::Expression::just_name(
                                                                    generic_ty,
                                                                )
                                                            })
                                                            .collect(),
                                                    },
                                                ]),
                                            ),
                                        },
                                    },
                                )),
                            ],
                        ]
                        .concat()
                    })
                    .collect_vec();

                coq::TopLevel::new(&[coq::TopLevelItem::Module(coq::Module::new(
                    &module_name,
                    coq::TopLevel::concat(&[
                        coq::TopLevel::new(&[coq::TopLevelItem::Definition(coq::Definition::new(
                            "Self",
                            &coq::DefinitionKind::Alias {
                                args: vec![coq::ArgDecl::of_ty_params(
                                    generic_tys,
                                    coq::ArgSpecKind::Explicit,
                                )],
                                ty: Some(coq::Expression::just_name("Ty.t")),
                                body: self_ty.to_coq(),
                            },
                        ))]),
                        coq::TopLevel::new(&items_coq),
                    ]),
                ))])
                .to_doc()
            }
            TopLevelItem::Trait {
                name,
                path,
                ty_params,
                body,
            } => coq::TopLevel::new(&[
                coq::TopLevelItem::Comment(coq::Comment::new("Trait")),
                coq::TopLevelItem::Module(coq::Module::new(
                    name,
                    coq::TopLevel::new(
                        &body
                            .iter()
                            .flat_map(|(name, item)| match item.as_ref() {
                                TraitItem::DefinitionWithDefault(fun_definition) => [
                                    fun_definition
                                        .to_coq(
                                            name,
                                            &None,
                                            ty_params
                                                .iter()
                                                .map(|(ty_param, _)| ty_param.clone())
                                                .collect(),
                                        )
                                        .items,
                                    vec![
                                        coq::TopLevelItem::Line,
                                        coq::TopLevelItem::Definition(coq::Definition::new(
                                            &format!("ProvidedMethod_{name}"),
                                            &coq::DefinitionKind::Axiom {
                                                ty: coq::Expression::just_name(
                                                    "M.IsProvidedMethod",
                                                )
                                                .apply_many(&[
                                                    coq::Expression::String(path.to_string()),
                                                    coq::Expression::just_name(name),
                                                ]),
                                            },
                                        )),
                                    ],
                                ]
                                .concat(),
                                _ => vec![],
                            })
                            .collect_vec(),
                    ),
                )),
            ])
            .to_doc(),
            TopLevelItem::TraitImpl {
                generic_tys,
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
                        .filter_map(|(_, trait_ty_param)| match trait_ty_param.as_ref() {
                            FieldWithDefault::RequiredValue(ty)
                            | FieldWithDefault::OptionalValue(ty) =>
                                Some(format!("_{}", ty.to_name())),
                            FieldWithDefault::Default => None,
                        })
                        .join(""),
                    self_ty.to_name()
                );
                let items_coq = items
                    .iter()
                    .filter_map(|item| {
                        Into::<Option<&ImplItemKind>>::into(item.kind.as_ref()).map(|kind| {
                            coq::Expression::Tuple(vec![
                                coq::Expression::String(item.name.to_string()),
                                match kind {
                                    ImplItemKind::Const { .. } => {
                                        coq::Expression::just_name("TODO")
                                    }
                                    ImplItemKind::Definition { .. } => {
                                        coq::Expression::just_name("InstanceField.Method")
                                            .apply_many(&[
                                                coq::Expression::just_name(item.name.as_str()),
                                                coq::Expression::List {
                                                    exprs: generic_tys
                                                        .iter()
                                                        .map(|generic_ty| {
                                                            coq::Expression::just_name(generic_ty)
                                                        })
                                                        .collect(),
                                                },
                                            ])
                                    }
                                    ImplItemKind::Type { .. } => coq::Expression::just_name("TODO"),
                                },
                            ])
                        })
                    })
                    .collect_vec();

                coq::Module::new(
                    &module_name,
                    coq::TopLevel::new(
                        &[
                            items
                                .iter()
                                .filter_map(|item| {
                                    Into::<Option<&ImplItemKind>>::into(item.kind.as_ref()).map(
                                        |kind: &ImplItemKind| {
                                            [
                                                match &item.snippet {
                                                    None => vec![],
                                                    Some(snippet) => snippet.to_coq(),
                                                },
                                                vec![
                                                    coq::TopLevelItem::Code(
                                                        kind.to_doc(
                                                            item.name.as_str(),
                                                            [
                                                                vec!["Self".to_string()],
                                                                generic_tys.clone(),
                                                            ]
                                                            .concat(),
                                                        ),
                                                    ),
                                                    coq::TopLevelItem::Line,
                                                ],
                                            ]
                                            .concat()
                                        },
                                    )
                                })
                                .concat(),
                            vec![coq::TopLevelItem::Definition(coq::Definition::new(
                                "Implements",
                                &coq::DefinitionKind::Axiom {
                                    ty: coq::Expression::PiType {
                                        args: vec![coq::ArgDecl::of_ty_params(
                                            generic_tys,
                                            coq::ArgSpecKind::Explicit,
                                        )],
                                        image: Rc::new(
                                            coq::Expression::just_name("M.IsTraitInstance")
                                                .apply_many(&[
                                                    coq::Expression::String(of_trait.to_string()),
                                                    coq::Expression::Comment(
                                                        "Self".to_string(),
                                                        Rc::new(self_ty.to_coq()),
                                                    ),
                                                    coq::Expression::List {
                                                        exprs: trait_ty_params
                                                            .iter()
                                                            .filter_map(|(name, ty)| {
                                                                match ty.as_ref() {
                                                                FieldWithDefault::RequiredValue(
                                                                    ty,
                                                                )
                                                                | FieldWithDefault::OptionalValue(
                                                                    ty,
                                                                ) => {
                                                                    Some(coq::Expression::Comment(
                                                                        name.clone(),
                                                                        Rc::new(ty.to_coq()),
                                                                    ))
                                                                }
                                                                FieldWithDefault::Default => None,
                                                            }
                                                            })
                                                            .collect(),
                                                    },
                                                    coq::Expression::List { exprs: items_coq },
                                                ]),
                                        ),
                                    },
                                },
                            ))],
                        ]
                        .concat(),
                    ),
                )
                .to_doc()
            }
            TopLevelItem::Error(message) => nest([text("Error"), line(), text(message), text(".")]),
        }
    }
}

fn struct_field_value<'a>(name: String) -> coq::Expression<'a> {
    coq::Expression::just_name("Ref.map").apply_many(&[
        coq::Expression::Function {
            parameters: vec![coq::Expression::just_name("α")],
            body: Rc::new(coq::Expression::just_name("Some").apply(
                &coq::Expression::RecordField {
                    record: Rc::new(coq::Expression::just_name("α")),
                    field: name.to_owned(),
                },
            )),
        },
        coq::Expression::Function {
            parameters: vec![
                coq::Expression::just_name("β"),
                coq::Expression::just_name("α"),
            ],
            body: Rc::new(coq::Expression::just_name("Some").apply(
                &coq::Expression::RecordUpdate {
                    record: Rc::new(coq::Expression::just_name("α")),
                    field: name,
                    update: Rc::new(coq::Expression::just_name("β")),
                },
            )),
        },
    ])
}

fn enum_struct_field_value<'a>(
    constructor_name: &'a str,
    field_name: &'a str,
    has_more_than_one_case: bool,
) -> coq::Expression<'a> {
    let default_branch = if has_more_than_one_case {
        vec![(
            vec![coq::Expression::Wild],
            coq::Expression::just_name("None"),
        )]
    } else {
        vec![]
    };

    coq::Expression::just_name("Ref.map").apply_many(&[
        coq::Expression::Function {
            parameters: vec![coq::Expression::just_name("α")],
            body: Rc::new(coq::Expression::Match {
                scrutinees: vec![coq::Expression::just_name("α")],
                arms: [
                    vec![(
                        vec![coq::Expression::just_name(constructor_name)
                            .apply(&coq::Expression::just_name("α"))],
                        coq::Expression::just_name("Some").apply(&coq::Expression::RecordField {
                            record: Rc::new(coq::Expression::just_name("α")),
                            field: format!("{constructor_name}.{field_name}"),
                        }),
                    )],
                    default_branch.clone(),
                ]
                .concat(),
            }),
        },
        coq::Expression::Function {
            parameters: vec![
                coq::Expression::just_name("β"),
                coq::Expression::just_name("α"),
            ],
            body: Rc::new(coq::Expression::Match {
                scrutinees: vec![coq::Expression::just_name("α")],
                arms: [
                    vec![(
                        vec![coq::Expression::just_name(constructor_name)
                            .apply(&coq::Expression::just_name("α"))],
                        coq::Expression::just_name("Some").apply(
                            &coq::Expression::just_name(constructor_name).apply(
                                &coq::Expression::RecordUpdate {
                                    record: Rc::new(coq::Expression::just_name("α")),
                                    field: format!("{constructor_name}.{field_name}"),
                                    update: Rc::new(coq::Expression::just_name("β")),
                                },
                            ),
                        ),
                    )],
                    default_branch,
                ]
                .concat(),
            }),
        },
    ])
}

fn enum_tuple_field_value(
    constructor_name: &str,
    nb_fields: usize,
    field_index: usize,
    has_more_than_one_case: bool,
) -> coq::Expression {
    let default_branch = if has_more_than_one_case {
        vec![(
            vec![coq::Expression::Wild],
            coq::Expression::just_name("None"),
        )]
    } else {
        vec![]
    };

    coq::Expression::just_name("Ref.map").apply_many(&[
        coq::Expression::Function {
            parameters: vec![coq::Expression::just_name("α")],
            body: Rc::new(coq::Expression::Match {
                scrutinees: vec![coq::Expression::just_name("α")],
                arms: [
                    vec![(
                        vec![coq::Expression::just_name(constructor_name).apply_many(
                            &(0..nb_fields)
                                .map(|index| {
                                    if index == field_index {
                                        coq::Expression::just_name(&format!("α{index}"))
                                    } else {
                                        coq::Expression::Wild
                                    }
                                })
                                .collect::<Vec<_>>(),
                        )],
                        coq::Expression::just_name("Some")
                            .apply(&coq::Expression::just_name(&format!("α{field_index}"))),
                    )],
                    default_branch.clone(),
                ]
                .concat(),
            }),
        },
        coq::Expression::Function {
            parameters: vec![
                coq::Expression::just_name("β"),
                coq::Expression::just_name("α"),
            ],
            body: Rc::new(coq::Expression::Match {
                scrutinees: vec![coq::Expression::just_name("α")],
                arms: [
                    vec![(
                        vec![coq::Expression::just_name(constructor_name).apply_many(
                            &(0..nb_fields)
                                .map(|index| {
                                    if index != field_index {
                                        coq::Expression::just_name(&format!("α{index}"))
                                    } else {
                                        coq::Expression::Wild
                                    }
                                })
                                .collect::<Vec<_>>(),
                        )],
                        coq::Expression::just_name("Some").apply(
                            &coq::Expression::just_name(constructor_name).apply_many(
                                &(0..nb_fields)
                                    .map(|index| {
                                        if index == field_index {
                                            coq::Expression::just_name("β")
                                        } else {
                                            coq::Expression::just_name(&format!("α{index}"))
                                        }
                                    })
                                    .collect::<Vec<_>>(),
                            ),
                        ),
                    )],
                    default_branch,
                ]
                .concat(),
            }),
        },
    ])
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
                if let TopLevelItem::Module { name, .. } = item.as_ref() {
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
