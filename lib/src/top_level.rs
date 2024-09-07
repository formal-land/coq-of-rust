use crate::coq;
use crate::env::*;
use crate::expression::*;
use crate::header::*;
use crate::path::*;
use crate::pattern::*;
use crate::ty::*;
use itertools::Itertools;
use rustc_ast::ast::{AttrArgs, AttrKind};
use rustc_hir::def_id::LocalDefId;
use rustc_hir::{
    GenericBound, GenericBounds, GenericParamKind, Impl, ImplItemRef, Item, ItemId, ItemKind,
    PatKind, QPath, TraitFn, TraitItemKind, Ty, TyKind, VariantData,
};
use rustc_middle::ty::TyCtxt;
use rustc_span::symbol::sym;
use serde::Serialize;
use std::collections::HashMap;
use std::iter::repeat;
use std::rc::Rc;
use std::string::ToString;
use std::vec;

pub(crate) struct TopLevelOptions {
    pub(crate) axiomatize: bool,
}

#[derive(Debug)]
struct HirFnDeclAndBody<'a> {
    decl: &'a rustc_hir::FnDecl<'a>,
    body: Option<&'a rustc_hir::Body<'a>>,
}

type FnArgs = Vec<(String, Rc<CoqType>, Option<Rc<Pattern>>)>;

#[derive(Debug, Serialize)]
struct FnSigAndBody {
    args: Option<FnArgs>,
    ret_ty: Option<Rc<CoqType>>,
    body: Option<Rc<Expr>>,
}

#[derive(Debug, Serialize)]
enum TraitItem {
    Definition {
        #[allow(dead_code)]
        const_params: Vec<String>,
        #[allow(dead_code)]
        ty_params: Vec<String>,
        #[allow(dead_code)]
        ty: Rc<CoqType>,
    },
    DefinitionWithDefault(Rc<FunDefinition>),
    Type(),
}

/// fields common for all function definitions
#[derive(Debug, Serialize)]
struct FunDefinition {
    const_params: Vec<String>,
    ty_params: Vec<String>,
    signature_and_body: Rc<FnSigAndBody>,
}

#[derive(Debug, Serialize)]
enum ImplItemKind {
    Const {
        ty: Rc<CoqType>,
        body: Option<Rc<Expr>>,
    },
    Definition {
        definition: Rc<FunDefinition>,
    },
    Type {
        ty: Rc<CoqType>,
    },
}

#[derive(Debug, Serialize)]
struct WherePredicate {
    bound: Rc<TraitBound>,
    ty: Rc<CoqType>,
}

#[derive(Debug, Serialize)]
struct TraitBound {
    name: Rc<Path>,
    ty_params: Vec<(String, Rc<TraitTyParamValue>)>,
}

type TraitTyParamValue = FieldWithDefault<Rc<CoqType>>;

#[derive(Debug, Serialize)]
pub(crate) enum VariantItem {
    Struct { fields: Vec<(String, Rc<CoqType>)> },
    Tuple { tys: Vec<Rc<CoqType>> },
}

/// The value for a field that may have a default value
#[derive(Debug, Serialize)]
pub(crate) enum FieldWithDefault<A> {
    /// the value of a field that has no defaults
    RequiredValue(A),
    /// the value that replaces the default value
    OptionalValue(A),
    /// means the default value of the type parameter is used
    Default,
}

#[derive(Debug, Serialize)]
struct Snippet(Vec<String>);

#[derive(Debug, Serialize)]
struct ImplItem {
    name: String,
    snippet: Option<Rc<Snippet>>,
    kind: Rc<ImplItemKind>,
}

#[derive(Debug, Serialize)]
struct TraitImplItem {
    name: String,
    snippet: Option<Rc<Snippet>>,
    kind: Rc<FieldWithDefault<Rc<ImplItemKind>>>,
}

#[derive(Debug, Serialize)]
struct TypeEnumVariant {
    name: String,
    item: Rc<VariantItem>,
    discriminant: Option<u128>,
}

/// Representation of top-level hir [Item]s in coq-of-rust
/// See https://doc.rust-lang.org/reference/items.html
#[derive(Debug, Serialize)]
#[serde(tag = "type")]
enum TopLevelItem {
    Const {
        name: String,
        value: Option<Rc<Expr>>,
    },
    Definition {
        name: String,
        path: Rc<Path>,
        snippet: Option<Rc<Snippet>>,
        definition: Rc<FunDefinition>,
    },
    TypeAlias {
        name: String,
        path: Rc<Path>,
        const_params: Vec<String>,
        ty_params: Vec<String>,
        ty: Rc<CoqType>,
    },
    TypeEnum {
        name: String,
        const_params: Vec<String>,
        ty_params: Vec<String>,
        variants: Vec<Rc<TypeEnumVariant>>,
    },
    TypeStructStruct(TypeStructStruct),
    TypeStructTuple {
        name: String,
        const_params: Vec<String>,
        ty_params: Vec<String>,
        fields: Vec<Rc<CoqType>>,
    },
    TypeForeign {
        name: String,
    },
    Module {
        name: String,
        body: Rc<TopLevel>,
    },
    Impl {
        generic_consts: Vec<String>,
        generic_tys: Vec<String>,
        self_ty: Rc<CoqType>,
        items: Vec<Rc<ImplItem>>,
    },
    Trait {
        name: String,
        path: Rc<Path>,
        const_params: Vec<String>,
        ty_params: Vec<String>,
        body: Vec<(String, Rc<TraitItem>)>,
    },
    TraitImpl {
        generic_consts: Vec<String>,
        generic_tys: Vec<String>,
        predicates: Vec<Rc<WherePredicate>>,
        self_ty: Rc<CoqType>,
        of_trait: Rc<Path>,
        trait_ty_params: Vec<(String, Rc<TraitTyParamValue>)>,
        items: Vec<Rc<TraitImplItem>>,
    },
    Error {
        message: String,
    },
}

#[derive(Debug, Serialize)]
struct TypeStructStruct {
    name: String,
    const_params: Vec<String>,
    ty_params: Vec<String>,
    fields: Vec<(String, Rc<CoqType>)>,
}

#[derive(Debug, Serialize)]
struct TopLevelEntry {
    file_name: String,
    item: Rc<TopLevelItem>,
}

#[derive(Debug, Serialize)]
struct TopLevel(Vec<Rc<TopLevelEntry>>);

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
    env: &Env<'a>,
    fn_decl_and_body: HirFnDeclAndBody<'a>,
    is_axiom: bool,
) -> Rc<FnSigAndBody> {
    let HirFnDeclAndBody { decl, body } = fn_decl_and_body;
    let args = body.map(|body| get_args(env, body, decl.inputs));
    let ret_ty =
        body.map(|body| compile_fn_ret_ty(env, &body.value.hir_id.owner.def_id, &decl.output));
    let body = body.and_then(|body| compile_function_body(env, args.as_ref(), body, is_axiom));

    Rc::new(FnSigAndBody { args, ret_ty, body })
}

/// Check if the function body is actually the main test function calling to all
/// tests in the file. If so, we do not want to compile it.
fn check_if_is_test_main_function(env: &Env, body_id: &rustc_hir::BodyId) -> bool {
    let body = env.tcx.hir().body(*body_id);
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
    env: &Env,
    item: Item,
    attribute: &str,
) -> bool {
    for attr in env
        .tcx
        .get_attrs(item.into().def_id().to_def_id(), sym::allow)
    {
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

fn check_lint_attribute_axiom<'a, Item: Into<rustc_hir::OwnerNode<'a>>>(
    env: &Env,
    item: Item,
) -> bool {
    check_lint_attribute(env, item, "coq_axiom")
}

fn get_item_ids_for_parent(env: &Env, expected_parent: rustc_hir::def_id::DefId) -> Vec<ItemId> {
    env.tcx
        .hir()
        .items()
        .filter(|item_id| {
            let def_id = item_id.owner_id.to_def_id();
            let parent = env.tcx.opt_parent(def_id).unwrap();

            parent == expected_parent
        })
        .collect()
}

fn compile_top_level_item_without_local_items<'a>(
    env: &Env<'a>,
    item: &'a Item,
) -> Vec<Rc<TopLevelItem>> {
    let is_value = match &item.kind {
        ItemKind::Static(..) | ItemKind::Const(..) | ItemKind::Fn(..) => IsValue::Yes,
        _ => IsValue::No,
    };
    let name = to_valid_coq_name(is_value, item.ident.name.as_str());
    let path = compile_def_id(env, item.owner_id.to_def_id());

    match &item.kind {
        ItemKind::ExternCrate(_) => vec![],
        ItemKind::Use(..) => vec![],
        ItemKind::Static(ty, _, body_id) | ItemKind::Const(ty, _, body_id) => {
            if check_if_test_declaration(ty) {
                return vec![];
            }
            // skip const _ : ... = ...
            if item.ident.name.as_str() == "_" {
                return vec![];
            }

            let value_without_alloc = if env.axiomatize {
                None
            } else {
                Some(compile_hir_id(env, body_id.hir_id))
            };
            let value = if let ItemKind::Static(_, _, _) = &item.kind {
                value_without_alloc.map(|value_without_alloc| value_without_alloc.alloc())
            } else {
                value_without_alloc
            };

            vec![Rc::new(TopLevelItem::Const { name, value })]
        }
        ItemKind::Fn(fn_sig, generics, body_id) => {
            if check_if_is_test_main_function(env, body_id) {
                return vec![];
            }

            let snippet = Snippet::of_span(env, &item.span);
            let is_axiom = check_lint_attribute_axiom(env, item);
            let fn_decl_and_body = get_hir_fn_decl_and_body(env, fn_sig.decl, body_id);

            vec![Rc::new(TopLevelItem::Definition {
                name,
                path,
                snippet,
                definition: FunDefinition::compile(env, generics, fn_decl_and_body, is_axiom),
            })]
        }
        ItemKind::Macro(_, _) => vec![],
        ItemKind::Mod(module) => {
            let items = module
                .item_ids
                .iter()
                .flat_map(|item_id| {
                    let item = env.tcx.hir().item(*item_id);

                    compile_top_level_item_with_file_name(env, item)
                })
                .collect_vec();

            vec![Rc::new(TopLevelItem::Module {
                name,
                body: Rc::new(TopLevel(items)),
            })]
        }
        ItemKind::ForeignMod { abi: _, items } => items
            .iter()
            .map(|item| {
                let foreign_item = env.tcx.hir().foreign_item(item.id);
                let is_value = match &foreign_item.kind {
                    rustc_hir::ForeignItemKind::Fn(..) | rustc_hir::ForeignItemKind::Static(..) => {
                        IsValue::Yes
                    }
                    rustc_hir::ForeignItemKind::Type => IsValue::No,
                };
                let name = to_valid_coq_name(is_value, item.ident.name.as_str());

                match &foreign_item.kind {
                    rustc_hir::ForeignItemKind::Fn(sign, _, generics) => {
                        let fn_decl_and_body = HirFnDeclAndBody {
                            decl: sign.decl,
                            body: None,
                        };

                        Rc::new(TopLevelItem::Definition {
                            name: name.clone(),
                            path: Path::concat(&[path.clone(), Path::new(&[name])]),
                            snippet: None,
                            definition: FunDefinition::compile(
                                env,
                                generics,
                                fn_decl_and_body,
                                false,
                            ),
                        })
                    }
                    rustc_hir::ForeignItemKind::Static(..) => {
                        Rc::new(TopLevelItem::Const { name, value: None })
                    }
                    rustc_hir::ForeignItemKind::Type => Rc::new(TopLevelItem::TypeForeign { name }),
                }
            })
            .collect_vec(),
        ItemKind::GlobalAsm(_) => vec![Rc::new(TopLevelItem::Error {
            message: "GlobalAsm".to_string(),
        })],
        ItemKind::TyAlias(ty, generics) => vec![Rc::new(TopLevelItem::TypeAlias {
            name,
            path,
            ty: compile_type(env, &item.owner_id.def_id, ty),
            const_params: get_const_params(env, generics),
            ty_params: get_ty_params(env, generics),
        })],
        ItemKind::OpaqueTy(_) => vec![Rc::new(TopLevelItem::Error {
            message: "OpaqueTy".to_string(),
        })],
        ItemKind::Enum(enum_def, generics) => {
            let const_params = get_const_params(env, generics);
            let ty_params = get_ty_params(env, generics);

            vec![Rc::new(TopLevelItem::TypeEnum {
                name,
                const_params,
                ty_params,
                variants: enum_def
                    .variants
                    .iter()
                    .map(|variant| {
                        let name = variant.ident.name.to_string();
                        let fields = match &variant.data {
                            VariantData::Struct {
                                fields,
                                recovered: _,
                            } => {
                                let fields = fields
                                    .iter()
                                    .map(|field| {
                                        (
                                            field.ident.to_string(),
                                            compile_type(env, &item.owner_id.def_id, field.ty),
                                        )
                                    })
                                    .collect();
                                VariantItem::Struct { fields }
                            }
                            VariantData::Tuple(fields, _, _) => {
                                let tys = fields
                                    .iter()
                                    .map(|field| compile_type(env, &item.owner_id.def_id, field.ty))
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
                                    }) => Some(discriminant.get()),
                                    _ => None,
                                }
                            }
                        };

                        Rc::new(TypeEnumVariant {
                            name,
                            item: Rc::new(fields),
                            discriminant,
                        })
                    })
                    .collect(),
            })]
        }
        ItemKind::Struct(body, generics) => {
            let const_params = get_const_params(env, generics);
            let ty_params = get_ty_params(env, generics);

            match body {
                VariantData::Struct {
                    fields,
                    recovered: _,
                } => {
                    if fields.is_empty() {
                        return vec![Rc::new(TopLevelItem::TypeStructTuple {
                            name,
                            const_params,
                            ty_params,
                            fields: vec![],
                        })];
                    }
                    let fields = fields
                        .iter()
                        .map(|field| {
                            (
                                to_valid_coq_name(IsValue::No, field.ident.name.as_str()),
                                compile_type(env, &item.owner_id.def_id, field.ty),
                            )
                        })
                        .collect();
                    vec![Rc::new(TopLevelItem::TypeStructStruct(TypeStructStruct {
                        name,
                        const_params,
                        ty_params,
                        fields,
                    }))]
                }
                VariantData::Tuple(fields, _, _) => {
                    vec![Rc::new(TopLevelItem::TypeStructTuple {
                        name,
                        const_params,
                        ty_params,
                        fields: fields
                            .iter()
                            .map(|field| compile_type(env, &item.owner_id.def_id, field.ty))
                            .collect(),
                    })]
                }
                VariantData::Unit(_, _) => {
                    vec![Rc::new(TopLevelItem::TypeStructTuple {
                        name,
                        const_params,
                        ty_params,
                        fields: vec![],
                    })]
                }
            }
        }
        ItemKind::Union(_, _) => vec![Rc::new(TopLevelItem::Error {
            message: "Union".to_string(),
        })],
        ItemKind::Trait(_, _, generics, _, items) => {
            vec![Rc::new(TopLevelItem::Trait {
                name,
                path,
                const_params: get_const_params(env, generics),
                ty_params: get_ty_params(env, generics),
                body: items
                    .iter()
                    .map(|item| {
                        let item = env.tcx.hir().trait_item(item.id);
                        let const_params = get_const_params(env, item.generics);
                        let ty_params = get_ty_params(env, item.generics);
                        let body = compile_trait_item_body(env, const_params, ty_params, item);
                        let is_value = match body.as_ref() {
                            TraitItem::Definition { .. } | TraitItem::DefinitionWithDefault(..) => {
                                IsValue::Yes
                            }
                            TraitItem::Type() => IsValue::No,
                        };

                        (to_valid_coq_name(is_value, item.ident.name.as_str()), body)
                    })
                    .collect(),
            })]
        }
        ItemKind::TraitAlias(_, _) => {
            vec![Rc::new(TopLevelItem::Error {
                message: "TraitAlias".to_string(),
            })]
        }
        ItemKind::Impl(Impl {
            generics,
            of_trait,
            self_ty,
            items,
            ..
        }) => {
            let generic_consts = get_const_params(env, generics);
            let generic_tys = get_ty_params(env, generics);
            let predicates = get_where_predicates(env, &item.owner_id.def_id, generics);
            let self_ty = compile_type(env, &item.owner_id.def_id, self_ty);
            let items = compile_impl_item_refs(env, items);

            match of_trait {
                Some(trait_ref) => {
                    let rustc_default_item_names: Vec<String> = env
                        .tcx
                        .associated_items(trait_ref.trait_def_id().unwrap())
                        .in_definition_order()
                        .filter(|item| item.defaultness(env.tcx).has_value())
                        .map(|item| to_valid_coq_name(IsValue::Yes, item.name.as_str()))
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
                    let trait_generics = env.tcx.generics_of(trait_ref.trait_def_id().unwrap());

                    vec![Rc::new(TopLevelItem::TraitImpl {
                        generic_consts,
                        generic_tys,
                        predicates,
                        self_ty,
                        of_trait: compile_path(env, trait_ref.path),
                        trait_ty_params: get_ty_params_with_default_status(
                            env,
                            &item.owner_id.def_id,
                            trait_generics,
                            trait_ref.path,
                        ),
                        items,
                    })]
                }
                None => vec![Rc::new(TopLevelItem::Impl {
                    generic_consts,
                    generic_tys,
                    self_ty,
                    items,
                })],
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
fn compile_top_level_item<'a>(env: &Env<'a>, item: &'a Item) -> Vec<Rc<TopLevelItem>> {
    // Sometimes there can be local items, for example a struct defined in the
    // body of a function. For modules, we make an exception as modules are
    // expected to have items. We will concatenate the local items directly after
    // the item's translation, in a module of the same name to avoid collisions.
    let local_item_ids = match &item.kind {
        ItemKind::Mod(_) => vec![],
        _ => get_item_ids_for_parent(env, item.item_id().owner_id.to_def_id()),
    };
    let local_items = local_item_ids
        .into_iter()
        .flat_map(|item_id| {
            let item = env.tcx.hir().item(item_id);

            compile_top_level_item_with_file_name(env, item)
        })
        .collect_vec();

    let items = compile_top_level_item_without_local_items(env, item);

    [
        items,
        if local_items.is_empty() {
            vec![]
        } else {
            vec![Rc::new(TopLevelItem::Module {
                name: to_valid_coq_name(IsValue::No, item.ident.as_str()),
                body: Rc::new(TopLevel(local_items)),
            })]
        },
    ]
    .concat()
}

fn entry_of_item(env: &Env, span: rustc_span::Span, item: Rc<TopLevelItem>) -> Rc<TopLevelEntry> {
    Rc::new(TopLevelEntry {
        file_name: env
            .tcx
            .sess
            .source_map()
            .lookup_source_file(span.lo())
            .name
            .prefer_remapped_unconditionaly()
            .to_string_lossy()
            .to_string(),
        item,
    })
}

fn compile_top_level_item_with_file_name<'a>(
    env: &Env<'a>,
    item: &'a Item,
) -> Vec<Rc<TopLevelEntry>> {
    compile_top_level_item(env, item)
        .into_iter()
        .map(|translated_item| entry_of_item(env, item.span, translated_item))
        .collect()
}

fn group_top_level_items_by_file_name(
    items: &[Rc<TopLevelEntry>],
) -> HashMap<String, Vec<Rc<TopLevelEntry>>> {
    let mut groups: HashMap<String, Vec<Rc<TopLevelEntry>>> = HashMap::new();

    for item in items {
        match item.item.as_ref() {
            TopLevelItem::Module { name, body } => {
                let sub_groups = group_top_level_items_by_file_name(&body.0);

                for (file_name, sub_group) in sub_groups {
                    let group = groups.entry(file_name.clone()).or_default();

                    group.push(Rc::new(TopLevelEntry {
                        file_name,
                        item: Rc::new(TopLevelItem::Module {
                            name: name.clone(),
                            body: Rc::new(TopLevel(sub_group)),
                        }),
                    }))
                }
            }
            _ => {
                let file_name = item.file_name.clone();
                let group = groups.entry(file_name).or_default();

                group.push(item.clone());
            }
        }
    }

    groups
}

fn group_top_level_by_file_name(top_level: Rc<TopLevel>) -> HashMap<String, Rc<TopLevel>> {
    let groups = group_top_level_items_by_file_name(&top_level.0);

    groups
        .into_iter()
        .map(|(file_name, items)| (file_name, Rc::new(TopLevel(items))))
        .collect()
}

/// returns a pair of function signature and its body
fn get_hir_fn_decl_and_body<'a>(
    env: &Env<'a>,
    decl: &'a rustc_hir::FnDecl<'a>,
    body_id: &rustc_hir::BodyId,
) -> HirFnDeclAndBody<'a> {
    HirFnDeclAndBody {
        decl,
        body: Some(get_body(env, body_id)),
    }
}

/// compiles a list of references to items
fn compile_impl_item_refs(env: &Env, item_refs: &[ImplItemRef]) -> Vec<Rc<ImplItem>> {
    item_refs
        .iter()
        .map(|item_ref| compile_impl_item(env, env.tcx.hir().impl_item(item_ref.id)))
        .collect()
}

/// compiles an item
fn compile_impl_item<'a>(env: &Env<'a>, item: &'a rustc_hir::ImplItem) -> Rc<ImplItem> {
    let is_value = match &item.kind {
        rustc_hir::ImplItemKind::Const(..) | rustc_hir::ImplItemKind::Fn(..) => IsValue::Yes,
        rustc_hir::ImplItemKind::Type(..) => IsValue::No,
    };
    let name = to_valid_coq_name(is_value, item.ident.name.as_str());
    let snippet = Snippet::of_span(env, &item.span);
    let kind = match &item.kind {
        rustc_hir::ImplItemKind::Const(ty, body_id) => {
            let ty = compile_type(env, &item.owner_id.def_id, ty);
            let body = if env.axiomatize {
                None
            } else {
                Some(compile_hir_id(env, body_id.hir_id))
            };
            Rc::new(ImplItemKind::Const { ty, body })
        }
        rustc_hir::ImplItemKind::Fn(fn_sig, body_id) => {
            let is_axiom = check_lint_attribute_axiom(env, item);

            Rc::new(ImplItemKind::Definition {
                definition: FunDefinition::compile(
                    env,
                    item.generics,
                    get_hir_fn_decl_and_body(env, fn_sig.decl, body_id),
                    is_axiom,
                ),
            })
        }
        rustc_hir::ImplItemKind::Type(ty) => Rc::new(ImplItemKind::Type {
            ty: compile_type(env, &item.owner_id.def_id, ty),
        }),
    };
    Rc::new(ImplItem {
        name,
        snippet,
        kind,
    })
}

/// returns the body corresponding to the given body_id
fn get_body<'a>(env: &Env<'a>, body_id: &rustc_hir::BodyId) -> &'a rustc_hir::Body<'a> {
    env.tcx.hir().body(*body_id)
}

// compiles the body of a function
fn compile_function_body(
    env: &Env,
    args: Option<&FnArgs>,
    body: &rustc_hir::Body,
    is_axiom: bool,
) -> Option<Rc<Expr>> {
    if env.axiomatize || is_axiom {
        return None;
    }

    let body_without_bindings = compile_hir_id(env, body.value.hir_id).read();

    if body_without_bindings.is_unimplemented() {
        return None;
    }

    let body_without_bindings = if body_without_bindings.has_return() {
        Rc::new(Expr::Call {
            func: Expr::local_var("M.catch_return"),
            args: vec![Rc::new(Expr::Lambda {
                args: vec![],
                body: body_without_bindings,
                is_for_match: false,
                is_internal: true,
            })],
            kind: CallKind::Effectful,
        })
    } else {
        body_without_bindings
    };
    let body_with_patterns = match args {
        None => body_without_bindings,
        Some(args) => {
            args.iter().rfold(
                body_without_bindings,
                |body, (name, _, pattern)| match pattern {
                    None => body,
                    Some(pattern) => crate::thir_expression::build_match(
                        Expr::local_var(name),
                        vec![MatchArm {
                            pattern: pattern.clone(),
                            if_let_guard: vec![],
                            body,
                        }],
                    ),
                },
            )
        }
    };
    let body = match args {
        None => body_with_patterns,
        Some(args) => crate::thir_expression::allocate_bindings(
            &args
                .iter()
                .map(|(name, _, _)| name.clone())
                .collect::<Vec<_>>(),
            body_with_patterns,
        ),
    };

    Some(body)
}

/// Return a list of argument names with their type, and an optional pattern if
/// the name needs to go through a `match` later.
fn get_args<'a>(env: &Env<'a>, body: &'a rustc_hir::Body, inputs: &'a [rustc_hir::Ty]) -> FnArgs {
    let local_def_id = body.value.hir_id.owner.def_id;

    get_arg_names(env, body)
        .into_iter()
        .zip(inputs.iter().map(|ty| compile_type(env, &local_def_id, ty)))
        .map(|((name, pattern), ty)| (name, ty, pattern))
        .collect()
}

/// returns names of the arguments
fn get_arg_names<'a>(
    env: &Env<'a>,
    body: &'a rustc_hir::Body,
) -> Vec<(String, Option<Rc<Pattern>>)> {
    body.params
        .iter()
        .enumerate()
        .map(|(index, param)| match param.pat.kind {
            PatKind::Binding(rustc_hir::BindingMode(rustc_hir::ByRef::No, _), _, ident, None) => {
                (to_valid_coq_name(IsValue::Yes, ident.name.as_str()), None)
            }
            _ => (
                format!("β{}", index),
                Some(Pattern::compile(env, param.pat)),
            ),
        })
        .collect()
}

/// compiles the const parameters from the generics
fn get_const_params(env: &Env, generics: &rustc_hir::Generics) -> Vec<String> {
    generics
        .params
        .iter()
        .filter_map(|param| match param.kind {
            GenericParamKind::Const { .. } => Some(to_valid_coq_name(
                IsValue::No,
                &crate::thir_ty::compile_generic_param(env, param.def_id.to_def_id()),
            )),
            GenericParamKind::Lifetime { .. } | GenericParamKind::Type { .. } => None,
        })
        .collect()
}

/// extracts type parameters from the generics
fn get_ty_params(env: &Env, generics: &rustc_hir::Generics) -> Vec<String> {
    generics
        .params
        .iter()
        .filter_map(|param| match param.kind {
            // we ignore lifetimes
            GenericParamKind::Type { .. } => Some(to_valid_coq_name(
                IsValue::No,
                &crate::thir_ty::compile_generic_param(env, param.def_id.to_def_id()),
            )),
            GenericParamKind::Lifetime { .. } | GenericParamKind::Const { .. } => None,
        })
        .collect()
}

/// extracts where predicates from the generics
fn get_where_predicates<'a>(
    env: &Env<'a>,
    local_def_id: &LocalDefId,
    generics: &rustc_hir::Generics<'a>,
) -> Vec<Rc<WherePredicate>> {
    generics
        .predicates
        .iter()
        .flat_map(|predicate| match predicate {
            rustc_hir::WherePredicate::BoundPredicate(predicate) => {
                let names_and_ty_params =
                    compile_generic_bounds(env, local_def_id, predicate.bounds);

                names_and_ty_params
                    .into_iter()
                    .map(|bound| {
                        trait_bound_to_where_predicate(
                            bound,
                            compile_type(env, local_def_id, predicate.bounded_ty),
                        )
                    })
                    .collect()
            }
            _ => vec![],
        })
        .collect()
}

/// converts a trait bound to a where predicate
fn trait_bound_to_where_predicate(bound: Rc<TraitBound>, ty: Rc<CoqType>) -> Rc<WherePredicate> {
    Rc::new(WherePredicate { bound, ty })
}

/// [compile_generic_bounds] compiles generic bounds in [compile_trait_item_body]
fn compile_generic_bounds<'a>(
    env: &Env<'a>,
    local_def_id: &LocalDefId,
    generic_bounds: GenericBounds<'a>,
) -> Vec<Rc<TraitBound>> {
    generic_bounds
        .iter()
        .filter_map(|generic_bound| match generic_bound {
            GenericBound::Trait(ptraitref, _) => {
                Some(TraitBound::compile(env, local_def_id, ptraitref))
            }
            // we ignore lifetimes
            GenericBound::Outlives { .. } => None,
            // we ignore the use generics
            GenericBound::Use(_, _) => None,
        })
        .collect()
}

/// computes the list of actual type parameters with their default status
fn get_ty_params_with_default_status<'a>(
    env: &Env<'a>,
    local_def_id: &LocalDefId,
    generics: &rustc_middle::ty::Generics,
    path: &rustc_hir::Path<'a>,
) -> Vec<(String, Rc<TraitTyParamValue>)> {
    let mut type_params_name_and_default_status = get_type_params_name_and_default_status(generics);
    // The first type parameter is always the Self type, that we do not consider as
    // part of the list of type parameters.
    type_params_name_and_default_status.remove(0);

    let ty_params = compile_path_ty_params(env, local_def_id, path);
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
        .own_params
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
    env: &Env<'a>,
    const_params: Vec<String>,
    ty_params: Vec<String>,
    item: &'a rustc_hir::TraitItem,
) -> Rc<TraitItem> {
    match &item.kind {
        TraitItemKind::Const(ty, _) => Rc::new(TraitItem::Definition {
            const_params,
            ty_params,
            ty: compile_type(env, &item.owner_id.def_id, ty),
        }),
        TraitItemKind::Fn(fn_sig, trait_fn) => match trait_fn {
            TraitFn::Required(_) => Rc::new(TraitItem::Definition {
                const_params,
                ty_params,
                ty: compile_fn_decl(env, &item.owner_id.def_id, fn_sig.decl),
            }),
            TraitFn::Provided(body_id) => {
                let fn_decl_and_body = get_hir_fn_decl_and_body(env, fn_sig.decl, body_id);
                let signature_and_body = compile_fn_sig_and_body(env, fn_decl_and_body, false);
                Rc::new(TraitItem::DefinitionWithDefault(Rc::new(FunDefinition {
                    const_params,
                    ty_params,
                    signature_and_body,
                })))
            }
        },
        TraitItemKind::Type(_, concrete_type) => {
            if concrete_type.is_some() {
                let span = &item.span;
                let warning_msg = "Concrete value of associated types is not supported yet.";
                let note_msg = "It will change in future versions.";
                emit_warning_with_note(env, span, warning_msg, Some(note_msg));
            }

            Rc::new(TraitItem::Type())
        }
    }
}

fn compile_top_level(tcx: &TyCtxt, opts: TopLevelOptions) -> Rc<TopLevel> {
    let env = Env {
        tcx: *tcx,
        axiomatize: opts.axiomatize,
    };
    let results = get_item_ids_for_parent(&env, rustc_hir::def_id::CRATE_DEF_ID.into())
        .iter()
        .flat_map(|item_id| {
            let item = tcx.hir().item(*item_id);
            compile_top_level_item_with_file_name(&env, item)
        })
        .collect();

    Rc::new(TopLevel(results))
}

const LINE_WIDTH: usize = 100;

pub(crate) fn translate_top_level(
    tcx: &TyCtxt,
    opts: TopLevelOptions,
) -> HashMap<String, (String, String)> {
    let top_level = compile_top_level(tcx, opts);
    let top_level_groups = group_top_level_by_file_name(top_level);

    top_level_groups
        .into_iter()
        .map(|(file_name, top_level)| {
            (
                file_name,
                (top_level.to_pretty(LINE_WIDTH), top_level.to_json()),
            )
        })
        .collect()
}

#[derive(Debug, Serialize)]
pub(crate) struct DynNameGen {
    name: String,
    // Resources to be translated into a list of `WherePredicates`.
    // Traits' paths along with their opaque type names
    predicates: Vec<(Rc<Path>, String)>,
}

impl DynNameGen {
    pub(crate) fn new(name: String) -> Self {
        DynNameGen {
            name,
            predicates: vec![],
        }
    }

    fn next(&mut self, path: Rc<Path>) -> String {
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

    fn make_dyn_parm(&mut self, arg: Rc<CoqType>) -> Rc<CoqType> {
        if let Some((name, arg)) = arg.clone().match_ref() {
            let ct = self.make_dyn_parm(arg);
            Rc::new(CoqType::Application {
                func: CoqType::path(&[&name]),
                consts: vec![],
                tys: vec![ct],
            })
        } else if let CoqType::Dyn { traits } = arg.as_ref() {
            // We suppose `dyn` is only associated with one trait so we can directly extract the first element
            if let Some(trait_) = traits.first() {
                let dy_name = self.next(trait_.clone());
                CoqType::var(dy_name.as_ref())
            } else {
                Rc::new(CoqType::Dyn {
                    traits: traits.clone(),
                })
            }
        } else {
            arg
        }
    }
}

impl FunDefinition {
    /// compiles a given function
    fn compile<'a>(
        env: &Env<'a>,
        generics: &rustc_hir::Generics,
        fn_decl_and_body: HirFnDeclAndBody<'a>,
        is_axiom: bool,
    ) -> Rc<Self> {
        let mut dyn_name_gen = DynNameGen::new("T".to_string());
        let FnSigAndBody { args, ret_ty, body } =
            &*compile_fn_sig_and_body(env, fn_decl_and_body, is_axiom);
        let args = args.as_ref().map(|args| {
            args.iter().fold(vec![], |result, (string, ty, pattern)| {
                let ty = dyn_name_gen.make_dyn_parm(ty.clone());
                [result, vec![(string.to_owned(), ty, pattern.clone())]].concat()
            })
        });
        let const_params = get_const_params(env, generics);
        let ty_params = get_ty_params(env, generics);

        let signature_and_body = Rc::new(FnSigAndBody {
            args,
            ret_ty: ret_ty.clone(),
            body: body.clone(),
        });

        Rc::new(FunDefinition {
            const_params,
            ty_params,
            signature_and_body,
        })
    }

    /// The generics [generic_tys] are not part of the definition itself, but
    /// come from above, for example from the generics of the enclosing `impl`.
    /// The [with_extra_self_ty] is to add an extra `Self` parameter, for
    /// the default implementation of provided methods in traits.
    fn to_coq<'a>(
        &'a self,
        name: String,
        snippet: &'a Option<Rc<Snippet>>,
        generic_consts: Vec<String>,
        generic_tys: Vec<String>,
        with_extra_self_ty: bool,
    ) -> Vec<coq::TopLevelItem> {
        let generics = [generic_consts.clone(), generic_tys.clone()].concat();

        [
            match snippet {
                Some(snippet) => vec![snippet.to_coq()],
                None => vec![],
            },
            match &self.signature_and_body.body {
                None => vec![coq::TopLevelItem::Definition(coq::Definition::new(
                    &name,
                    &coq::DefinitionKind::Assumption {
                        ty: coq::Expression::PiType {
                            args: coq::ArgDecl::of_const_ty_params(
                                &generic_consts,
                                &generic_tys,
                                coq::ArgSpecKind::Explicit,
                            ),
                            image: Rc::new(coq::Expression::FunctionType {
                                domains: vec![
                                    coq::Expression::just_name("list")
                                        .apply(&coq::Expression::just_name("Value.t")),
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
                Some(body) => {
                    let body = coq::Expression::Match {
                        scrutinees: vec![
                            coq::Expression::just_name("ε"),
                            coq::Expression::just_name("τ"),
                            coq::Expression::just_name("α"),
                        ],
                        arms: vec![
                            (
                                vec![
                                    coq::Expression::List {
                                        exprs: self
                                            .const_params
                                            .iter()
                                            .map(|const_param| {
                                                coq::Expression::name_pattern(const_param)
                                            })
                                            .collect(),
                                    },
                                    coq::Expression::List {
                                        exprs: self
                                            .ty_params
                                            .iter()
                                            .map(|ty_param| coq::Expression::name_pattern(ty_param))
                                            .collect(),
                                    },
                                    coq::Expression::List {
                                        exprs: self
                                            .signature_and_body
                                            .args
                                            .as_ref()
                                            .unwrap_or(&vec![])
                                            .iter()
                                            .map(|(name, _, _)| coq::Expression::name_pattern(name))
                                            .collect(),
                                    },
                                ],
                                coq::Expression::monadic(&body.to_coq()),
                            ),
                            (
                                vec![
                                    coq::Expression::Wild,
                                    coq::Expression::Wild,
                                    coq::Expression::Wild,
                                ],
                                coq::Expression::just_name("M.impossible").apply(
                                    &coq::Expression::String(
                                        "wrong number of arguments".to_string(),
                                    ),
                                ),
                            ),
                        ],
                    };

                    vec![coq::TopLevelItem::Definition(coq::Definition::new(
                        &name,
                        &coq::DefinitionKind::Alias {
                            args: [
                                coq::ArgDecl::of_const_ty_params(
                                    &generic_consts,
                                    &[
                                        generic_tys.clone(),
                                        if with_extra_self_ty {
                                            vec!["Self".to_string()]
                                        } else {
                                            vec![]
                                        },
                                    ]
                                    .concat(),
                                    coq::ArgSpecKind::Explicit,
                                ),
                                vec![
                                    coq::ArgDecl::new(
                                        &coq::ArgDeclVar::Simple {
                                            idents: vec!["ε".to_string()],
                                            ty: Some(
                                                coq::Expression::just_name("list")
                                                    .apply(&coq::Expression::just_name("Value.t")),
                                            ),
                                        },
                                        coq::ArgSpecKind::Explicit,
                                    ),
                                    coq::ArgDecl::new(
                                        &coq::ArgDeclVar::Simple {
                                            idents: vec!["τ".to_string()],
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
                            ]
                            .concat(),
                            ty: Some(coq::Expression::just_name("M")),
                            body: if !generics.is_empty() && !with_extra_self_ty {
                                coq::Expression::Let {
                                    name: Some("Self".to_string()),
                                    is_user: false,
                                    ty: Some(Rc::new(coq::Expression::just_name("Ty.t"))),
                                    init: Rc::new(
                                        coq::Expression::just_name("Self").apply_many(
                                            &generics
                                                .iter()
                                                .map(|generic_ty| {
                                                    coq::Expression::just_name(generic_ty)
                                                })
                                                .collect_vec(),
                                        ),
                                    ),
                                    body: Rc::new(body),
                                }
                            } else {
                                body
                            },
                        },
                    ))]
                }
            },
        ]
        .concat()
    }
}

impl ImplItemKind {
    /// We prefix the type names by an underscore to avoid collisions with
    /// polymorphic type variables.
    fn to_definition_name(&self, name: String) -> String {
        match self {
            ImplItemKind::Type { .. } => format!("_{name}"),
            _ => name,
        }
    }

    fn to_coq<'a>(
        &'a self,
        name: &'a str,
        generic_consts: Vec<String>,
        generic_tys: Vec<String>,
    ) -> Vec<coq::TopLevelItem> {
        let definition_name = self.to_definition_name(name.to_string());
        let generics = [generic_consts.clone(), generic_tys.clone()].concat();

        match self {
            ImplItemKind::Const { ty, body } => vec![
                coq::TopLevelItem::Comment(vec![ty.to_coq()]),
                match body {
                    None => coq::TopLevelItem::Definition(coq::Definition::new(
                        &definition_name,
                        &coq::DefinitionKind::Assumption {
                            ty: coq::Expression::PiType {
                                args: coq::ArgDecl::of_const_ty_params(
                                    &generic_consts,
                                    &generic_tys,
                                    coq::ArgSpecKind::Explicit,
                                ),
                                image: Rc::new(coq::Expression::just_name("Value.t")),
                            },
                        },
                    )),
                    Some(body) => {
                        let body = coq::Expression::just_name("M.run")
                            .apply(&coq::Expression::monadic(&body.to_coq()));

                        coq::TopLevelItem::Definition(coq::Definition::new(
                            &definition_name,
                            &coq::DefinitionKind::Alias {
                                args: coq::ArgDecl::of_const_ty_params(
                                    &generic_consts,
                                    &generic_tys,
                                    coq::ArgSpecKind::Explicit,
                                ),
                                ty: Some(coq::Expression::just_name("Value.t")),
                                body: if !generics.is_empty() {
                                    coq::Expression::Let {
                                        name: Some("Self".to_string()),
                                        is_user: false,
                                        ty: Some(Rc::new(coq::Expression::just_name("Ty.t"))),
                                        init: Rc::new(
                                            coq::Expression::just_name("Self").apply_many(
                                                &generics
                                                    .iter()
                                                    .map(|generic_ty| {
                                                        coq::Expression::just_name(generic_ty)
                                                    })
                                                    .collect_vec(),
                                            ),
                                        ),
                                        body: Rc::new(body),
                                    }
                                } else {
                                    body
                                },
                            },
                        ))
                    }
                },
            ],
            ImplItemKind::Definition { definition, .. } => {
                definition.to_coq(definition_name, &None, generic_consts, generic_tys, false)
            }
            ImplItemKind::Type { ty } => {
                vec![coq::TopLevelItem::Definition(coq::Definition::new(
                    &definition_name,
                    &coq::DefinitionKind::Alias {
                        args: coq::ArgDecl::of_const_ty_params(
                            &generic_consts,
                            &generic_tys,
                            coq::ArgSpecKind::Explicit,
                        ),
                        ty: Some(coq::Expression::just_name("Ty.t")),
                        body: ty.to_coq(),
                    },
                ))]
            }
        }
    }
}

impl TraitBound {
    /// Get the generics for the trait
    fn compile<'a>(
        env: &Env<'a>,
        local_def_id: &LocalDefId,
        ptraitref: &rustc_hir::PolyTraitRef<'a>,
    ) -> Rc<TraitBound> {
        Rc::new(TraitBound {
            name: compile_path(env, ptraitref.trait_ref.path),
            ty_params: get_ty_params_with_default_status(
                env,
                local_def_id,
                env.tcx
                    .generics_of(ptraitref.trait_ref.trait_def_id().unwrap()),
                ptraitref.trait_ref.path,
            ),
        })
    }
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

    fn to_coq(&self) -> coq::TopLevelItem {
        let nb_quotes = self
            .0
            .iter()
            .map(|line| line.chars().filter(|c| *c == '"').count())
            .sum::<usize>();

        coq::TopLevelItem::Comment(
            [
                self.0
                    .iter()
                    // We do this replace to avoid messing up with the Coq comments
                    .map(|line| {
                        coq::Expression::Message(line.replace("(*", "( *").replace("*)", "* )"))
                    })
                    .collect(),
                if nb_quotes % 2 == 0 {
                    vec![]
                } else {
                    vec![coq::Expression::Message("\"".to_string())]
                },
            ]
            .concat(),
        )
    }
}

impl VariantItem {
    fn to_coq(&self) -> coq::Expression {
        match self {
            VariantItem::Struct { fields } => {
                coq::Expression::just_name("StructRecord").apply(&coq::Expression::List {
                    exprs: fields
                        .iter()
                        .map(|(name, ty)| {
                            coq::Expression::Tuple(vec![
                                coq::Expression::String(name.to_string()),
                                ty.to_coq(),
                            ])
                        })
                        .collect(),
                })
            }
            VariantItem::Tuple { tys } => {
                coq::Expression::just_name("StructTuple").apply(&coq::Expression::List {
                    exprs: tys.iter().map(|ty| ty.to_coq()).collect(),
                })
            }
        }
    }
}

impl TypeEnumVariant {
    fn to_coq(&self) -> coq::Expression {
        let Self {
            name,
            item,
            discriminant,
        } = self;

        coq::Expression::Record {
            fields: vec![
                coq::Field {
                    name: "name".to_string(),
                    args: vec![],
                    body: coq::Expression::String(name.to_string()),
                },
                coq::Field {
                    name: "item".to_string(),
                    args: vec![],
                    body: item.to_coq(),
                },
                coq::Field {
                    name: "discriminant".to_string(),
                    args: vec![],
                    body: coq::Expression::of_option(discriminant, |discriminant| {
                        coq::Expression::U128(*discriminant)
                    }),
                },
            ],
        }
    }
}

impl TypeStructStruct {
    fn to_coq(&self) -> coq::Expression {
        coq::Expression::just_name("StructRecord").apply(&coq::Expression::Record {
            fields: vec![
                coq::Field {
                    name: "name".to_string(),
                    args: vec![],
                    body: coq::Expression::String(self.name.to_string()),
                },
                coq::Field {
                    name: "const_params".to_string(),
                    args: vec![],
                    body: coq::Expression::List {
                        exprs: self
                            .const_params
                            .iter()
                            .map(|name| coq::Expression::String(name.to_string()))
                            .collect(),
                    },
                },
                coq::Field {
                    name: "ty_params".to_string(),
                    args: vec![],
                    body: coq::Expression::List {
                        exprs: self
                            .ty_params
                            .iter()
                            .map(|name| coq::Expression::String(name.to_string()))
                            .collect(),
                    },
                },
                coq::Field {
                    name: "fields".to_string(),
                    args: vec![],
                    body: coq::Expression::List {
                        exprs: self
                            .fields
                            .iter()
                            .map(|(name, ty)| {
                                coq::Expression::Tuple(vec![
                                    coq::Expression::String(name.to_string()),
                                    ty.to_coq(),
                                ])
                            })
                            .collect(),
                    },
                },
            ],
        })
    }
}

impl TopLevelItem {
    #[allow(clippy::format_collect)]
    fn to_coq(&self) -> Vec<coq::TopLevelItem> {
        match self {
            TopLevelItem::Const { name, value } => match value {
                None => vec![coq::TopLevelItem::Definition(coq::Definition::new(
                    name,
                    &coq::DefinitionKind::Assumption {
                        ty: coq::Expression::just_name("Value.t"),
                    },
                ))],
                Some(value) => {
                    vec![coq::TopLevelItem::Definition(coq::Definition::new(
                        name,
                        &coq::DefinitionKind::Alias {
                            args: vec![],
                            ty: Some(coq::Expression::just_name("Value.t")),
                            body: coq::Expression::just_name("M.run")
                                .apply(&coq::Expression::monadic(&value.to_coq())),
                        },
                    ))]
                }
            },
            TopLevelItem::Definition {
                name,
                path,
                snippet,
                definition,
            } => [
                definition.to_coq(name.to_string(), snippet, vec![], vec![], false),
                vec![
                    coq::TopLevelItem::Line,
                    coq::TopLevelItem::Definition(coq::Definition::new(
                        &format!("Function_{name}"),
                        &coq::DefinitionKind::Axiom {
                            ty: coq::Expression::just_name("M.IsFunction").apply_many(&[
                                coq::Expression::String(path.to_string()),
                                coq::Expression::just_name(name),
                            ]),
                        },
                    )),
                ],
            ]
            .concat(),
            TopLevelItem::Module { name, body } => {
                vec![coq::TopLevelItem::Module(coq::Module::new(
                    name,
                    body.to_coq(),
                ))]
            }
            TopLevelItem::TypeAlias {
                name,
                path,
                ty,
                const_params,
                ty_params,
            } => vec![coq::TopLevelItem::Definition(coq::Definition::new(
                name,
                &coq::DefinitionKind::Axiom {
                    ty: coq::Expression::PiType {
                        args: coq::ArgDecl::of_const_ty_params(
                            const_params,
                            ty_params,
                            coq::ArgSpecKind::Explicit,
                        ),
                        image: Rc::new(coq::Expression::Equality {
                            lhs: Rc::new(
                                CoqType::Application {
                                    func: Rc::new(CoqType::Path { path: path.clone() }),
                                    consts: const_params
                                        .iter()
                                        .map(|const_param| Expr::local_var(const_param))
                                        .collect(),
                                    tys: ty_params
                                        .iter()
                                        .map(|ty_param| CoqType::var(ty_param))
                                        .collect(),
                                }
                                .to_coq(),
                            ),
                            rhs: Rc::new(ty.to_coq()),
                        }),
                    },
                },
            ))],
            TopLevelItem::TypeEnum {
                name,
                const_params,
                ty_params,
                variants,
            } => vec![coq::TopLevelItem::Comment(vec![
                coq::Expression::Message(format!("Enum {name}")),
                coq::Expression::Record {
                    fields: vec![
                        coq::Field {
                            name: "const_params".to_string(),
                            args: vec![],
                            body: coq::Expression::List {
                                exprs: const_params
                                    .iter()
                                    .map(|name| coq::Expression::String(name.to_string()))
                                    .collect(),
                            },
                        },
                        coq::Field {
                            name: "ty_params".to_string(),
                            args: vec![],
                            body: coq::Expression::List {
                                exprs: ty_params
                                    .iter()
                                    .map(|name| coq::Expression::String(name.to_string()))
                                    .collect(),
                            },
                        },
                        coq::Field {
                            name: "variants".to_string(),
                            args: vec![],
                            body: coq::Expression::List {
                                exprs: variants.iter().map(|variant| variant.to_coq()).collect(),
                            },
                        },
                    ],
                },
            ])],
            TopLevelItem::TypeStructStruct(tss) => {
                vec![coq::TopLevelItem::Comment(vec![tss.to_coq()])]
            }
            TopLevelItem::TypeStructTuple {
                name,
                const_params,
                ty_params,
                fields,
            } => vec![coq::TopLevelItem::Comment(vec![
                coq::Expression::just_name("StructTuple").apply(&coq::Expression::Record {
                    fields: vec![
                        coq::Field {
                            name: "name".to_string(),
                            args: vec![],
                            body: coq::Expression::String(name.to_string()),
                        },
                        coq::Field {
                            name: "const_params".to_string(),
                            args: vec![],
                            body: coq::Expression::List {
                                exprs: const_params
                                    .iter()
                                    .map(|name| coq::Expression::String(name.to_string()))
                                    .collect(),
                            },
                        },
                        coq::Field {
                            name: "ty_params".to_string(),
                            args: vec![],
                            body: coq::Expression::List {
                                exprs: ty_params
                                    .iter()
                                    .map(|name| coq::Expression::String(name.to_string()))
                                    .collect(),
                            },
                        },
                        coq::Field {
                            name: "fields".to_string(),
                            args: vec![],
                            body: coq::Expression::List {
                                exprs: fields.iter().map(|ty| ty.to_coq()).collect(),
                            },
                        },
                    ],
                }),
            ])],
            TopLevelItem::TypeForeign { name } => {
                vec![coq::TopLevelItem::Comment(vec![coq::Expression::Message(
                    format!("Foreign type '{name}'"),
                )])]
            }
            TopLevelItem::Impl {
                generic_consts,
                generic_tys,
                self_ty,
                items,
            } => {
                let module_name = format!("Impl_{}", self_ty.to_name());
                let generics: Vec<String> = [generic_consts.clone(), generic_tys.clone()].concat();
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
                                Some(snippet) => vec![snippet.to_coq()],
                            },
                            kind.to_coq(name, generic_consts.clone(), generic_tys.clone()),
                            vec![
                                coq::TopLevelItem::Line,
                                coq::TopLevelItem::Definition(coq::Definition::new(
                                    &match kind.as_ref() {
                                        ImplItemKind::Const { .. } => {
                                            format!("AssociatedConstant_{name}")
                                        }
                                        ImplItemKind::Definition { .. } => {
                                            format!("AssociatedFunction_{name}")
                                        }
                                        ImplItemKind::Type { .. } => {
                                            format!("AssociatedType_{name}")
                                        }
                                    },
                                    &coq::DefinitionKind::Axiom {
                                        ty: coq::Expression::PiType {
                                            args: coq::ArgDecl::of_const_ty_params(
                                                generic_consts,
                                                generic_tys,
                                                coq::ArgSpecKind::Explicit,
                                            ),
                                            image: Rc::new(
                                                coq::Expression::just_name(match kind.as_ref() {
                                                    ImplItemKind::Const { .. } => {
                                                        "M.IsAssociatedConstant"
                                                    }
                                                    ImplItemKind::Definition { .. } => {
                                                        "M.IsAssociatedFunction"
                                                    }
                                                    ImplItemKind::Type { .. } => {
                                                        "M.IsAssociatedType"
                                                    }
                                                })
                                                .apply_many(&[
                                                    coq::Expression::just_name("Self").apply_many(
                                                        &generics
                                                            .iter()
                                                            .map(|generic| {
                                                                coq::Expression::just_name(generic)
                                                            })
                                                            .collect_vec(),
                                                    ),
                                                    coq::Expression::String(name.to_string()),
                                                    coq::Expression::just_name(name).apply_many(
                                                        &generics
                                                            .iter()
                                                            .map(|generic| {
                                                                coq::Expression::just_name(generic)
                                                            })
                                                            .collect_vec(),
                                                    ),
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

                vec![coq::TopLevelItem::Module(coq::Module::new(
                    &module_name,
                    coq::TopLevel::concat(&[
                        coq::TopLevel::new(&[coq::TopLevelItem::Definition(coq::Definition::new(
                            "Self",
                            &coq::DefinitionKind::Alias {
                                args: coq::ArgDecl::of_const_ty_params(
                                    generic_consts,
                                    generic_tys,
                                    coq::ArgSpecKind::Explicit,
                                ),
                                ty: Some(coq::Expression::just_name("Ty.t")),
                                body: self_ty.to_coq(),
                            },
                        ))]),
                        coq::TopLevel::new(&items_coq),
                    ]),
                ))]
            }
            TopLevelItem::Trait {
                name,
                path,
                const_params,
                ty_params,
                body,
            } => {
                let params = [const_params.clone(), ty_params.clone()].concat();

                vec![
                    coq::TopLevelItem::Comment(vec![coq::Expression::Message("Trait".to_string())]),
                    coq::TopLevelItem::Module(coq::Module::new(
                        name,
                        coq::TopLevel::new(
                            &body
                                .iter()
                                .flat_map(|(name, item)| match item.as_ref() {
                                    TraitItem::DefinitionWithDefault(fun_definition) => [
                                        fun_definition.to_coq(
                                            name.to_string(),
                                            &None,
                                            const_params.clone(),
                                            ty_params.clone(),
                                            true,
                                        ),
                                        vec![
                                        coq::TopLevelItem::Line,
                                        coq::TopLevelItem::Definition(coq::Definition::new(
                                            &format!("ProvidedMethod_{name}"),
                                            &coq::DefinitionKind::Axiom {
                                                ty: coq::Expression::PiType {
                                                    args: coq::ArgDecl::of_const_ty_params(
                                                        const_params,
                                                        ty_params,
                                                        coq::ArgSpecKind::Explicit,
                                                    ),
                                                    image: Rc::new(coq::Expression::just_name(
                                                        "M.IsProvidedMethod",
                                                    )
                                                    .apply_many(&[
                                                        coq::Expression::String(path.to_string()),
                                                        coq::Expression::String(name.to_string()),
                                                        coq::Expression::just_name(name)
                                                            .apply_many(
                                                                &params
                                                                    .iter()
                                                                    .map(|param| {
                                                                        coq::Expression::just_name(
                                                                            param,
                                                                        )
                                                                    })
                                                                    .collect_vec(),
                                                            ),
                                                    ])),
                                                },
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
                ]
            }
            TopLevelItem::TraitImpl {
                generic_consts,
                generic_tys,
                predicates,
                self_ty,
                of_trait,
                trait_ty_params,
                items,
            } => {
                let generics = [generic_consts.clone(), generic_tys.clone()].concat();
                let module_name = format!(
                    "Impl_{}{}{}_for_{}",
                    of_trait.to_name(),
                    predicates
                        .iter()
                        .map(|where_predicate| {
                            let WherePredicate { bound, ty } = where_predicate.as_ref();
                            let TraitBound { name, ty_params } = bound.as_ref();

                            format!(
                                "_where_{}_{}{}",
                                name.to_name(),
                                ty.to_name(),
                                ty_params
                                    .iter()
                                    .filter_map(|(_, ty_param)| match ty_param.as_ref() {
                                        FieldWithDefault::RequiredValue(ty)
                                        | FieldWithDefault::OptionalValue(ty) =>
                                            Some(format!("_{}", ty.to_name())),
                                        FieldWithDefault::Default => None,
                                    })
                                    .join(""),
                            )
                        })
                        .collect::<String>(),
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
                                coq::Expression::just_name(match kind {
                                    ImplItemKind::Const { .. } => "InstanceField.Constant",
                                    ImplItemKind::Definition { .. } => "InstanceField.Method",
                                    ImplItemKind::Type { .. } => "InstanceField.Ty",
                                })
                                .apply(
                                    &coq::Expression::just_name(
                                        &kind.to_definition_name(item.name.to_string()),
                                    )
                                    .apply_many(
                                        &generics
                                            .iter()
                                            .map(|generic| coq::Expression::just_name(generic))
                                            .collect_vec(),
                                    ),
                                ),
                            ])
                        })
                    })
                    .collect_vec();

                vec![coq::TopLevelItem::Module(coq::Module::new(
                    &module_name,
                    coq::TopLevel::new(
                        &[
                            vec![
                                coq::TopLevelItem::Definition(coq::Definition::new(
                                    "Self",
                                    &coq::DefinitionKind::Alias {
                                        args: coq::ArgDecl::of_const_ty_params(
                                            generic_consts,
                                            generic_tys,
                                            coq::ArgSpecKind::Explicit,
                                        ),
                                        ty: Some(coq::Expression::just_name("Ty.t")),
                                        body: self_ty.to_coq(),
                                    },
                                )),
                                coq::TopLevelItem::Line,
                            ],
                            items
                                .iter()
                                .filter_map(|item| {
                                    Into::<Option<&ImplItemKind>>::into(item.kind.as_ref()).map(
                                        |kind: &ImplItemKind| {
                                            [
                                                match &item.snippet {
                                                    None => vec![],
                                                    Some(snippet) => vec![snippet.to_coq()],
                                                },
                                                kind.to_coq(
                                                    item.name.as_str(),
                                                    generic_consts.clone(),
                                                    generic_tys.clone(),
                                                ),
                                                vec![coq::TopLevelItem::Line],
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
                                        args: coq::ArgDecl::of_const_ty_params(
                                            generic_consts,
                                            generic_tys,
                                            coq::ArgSpecKind::Explicit,
                                        ),
                                        image: Rc::new(
                                            coq::Expression::just_name("M.IsTraitInstance")
                                                .apply_many(&[
                                                    coq::Expression::String(of_trait.to_string()),
                                                    coq::Expression::just_name("Self").apply_many(
                                                        &generics
                                                            .iter()
                                                            .map(|generic| {
                                                                coq::Expression::just_name(generic)
                                                            })
                                                            .collect_vec(),
                                                    ),
                                                    coq::Expression::Comment(
                                                        "Trait polymorphic types".to_string(),
                                                        Rc::new(coq::Expression::List {
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
                                                        }),
                                                    ),
                                                    coq::Expression::Comment(
                                                        "Instance".to_string(),
                                                        Rc::new(coq::Expression::List {
                                                            exprs: items_coq,
                                                        }),
                                                    ),
                                                ]),
                                        ),
                                    },
                                },
                            ))],
                        ]
                        .concat(),
                    ),
                ))]
            }
            TopLevelItem::Error { message } => vec![coq::TopLevelItem::Comment(vec![
                coq::Expression::just_name("Error")
                    .apply(&coq::Expression::Message(message.clone())),
            ])],
        }
    }
}

impl TopLevel {
    fn to_coq(&self) -> coq::TopLevel {
        coq::TopLevel::new(
            &itertools::Itertools::intersperse(
                self.0.iter().map(|item| item.item.to_coq()),
                vec![coq::TopLevelItem::Line],
            )
            .flatten()
            .collect_vec(),
        )
    }

    pub fn to_pretty(&self, width: usize) -> String {
        let mut w = Vec::new();
        self.to_coq().to_doc().render(width, &mut w).unwrap();
        format!("{}{}\n", HEADER, String::from_utf8(w).unwrap())
    }

    pub fn to_json(&self) -> String {
        serde_json::to_string_pretty(self).unwrap()
    }
}
