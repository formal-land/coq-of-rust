use crate::env::*;
use crate::expression::*;
use crate::header::*;
use crate::path::*;
use crate::pattern::*;
use crate::rocq;
use crate::ty::*;
use itertools::Itertools;
use rustc_hir::def_id::LocalDefId;
use rustc_hir::{
    ConstItemRhs, GenericBound, GenericBounds, GenericParamKind, Impl, ImplItemId, Item, ItemId,
    ItemKind, PatKind, QPath, TraitFn, TraitItemKind, Ty, TyKind, VariantData,
};
use rustc_middle::ty::TyCtxt;
use rustc_span::symbol::{sym, Symbol};
use serde::Serialize;
use std::collections::HashMap;
use std::iter::repeat;
use std::path::Path as FilePath;
use std::rc::Rc;
use std::string::ToString;
use std::vec;

#[derive(Clone, Copy)]
pub(crate) struct TopLevelOptions<'a> {
    pub(crate) axiomatize: bool,
    pub(crate) separate_runtime_file: bool,
    pub(crate) runtime_module_prefix: Option<&'a str>,
}

#[derive(Debug)]
struct HirFnDeclAndBody<'a> {
    decl: &'a rustc_hir::FnDecl<'a>,
    body: Option<&'a rustc_hir::Body<'a>>,
}

type FnArgs = Vec<(String, Rc<RocqType>, Option<Rc<Pattern>>)>;

#[derive(Debug, Serialize)]
struct FnSigAndBody {
    args: Option<FnArgs>,
    ret_ty: Option<Rc<RocqType>>,
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
        ty: Rc<RocqType>,
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
        ty: Rc<RocqType>,
        body: Option<Rc<Expr>>,
    },
    Definition {
        definition: Rc<FunDefinition>,
    },
    Type {
        ty: Rc<RocqType>,
    },
}

#[derive(Debug, Serialize)]
struct WherePredicate {
    bound: Rc<TraitBound>,
    ty: Rc<RocqType>,
}

#[derive(Debug, Serialize)]
struct TraitBound {
    name: Rc<Path>,
    ty_params: Vec<(String, Rc<TraitTyParamValue>)>,
}

type TraitTyParamValue = FieldWithDefault<Rc<RocqType>>;

#[derive(Debug, Serialize)]
pub(crate) enum VariantItem {
    Struct { fields: Vec<(String, Rc<RocqType>)> },
    Tuple { tys: Vec<Rc<RocqType>> },
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
    source_name: String,
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
    discriminant: u128,
}

/// Representation of top-level hir [Item]s in rocq-of-rust
/// See https://doc.rust-lang.org/reference/items.html
#[derive(Debug, Serialize)]
enum TopLevelItem {
    Const {
        name: String,
        path: Rc<Path>,
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
        ty: Rc<RocqType>,
    },
    TypeEnum {
        name: String,
        path: Rc<Path>,
        const_params: Vec<String>,
        ty_params: Vec<String>,
        variants: Vec<Rc<TypeEnumVariant>>,
    },
    TypeStructStruct(TypeStructStruct),
    TypeStructTuple {
        name: String,
        const_params: Vec<String>,
        ty_params: Vec<String>,
        fields: Vec<Rc<RocqType>>,
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
        self_ty: Rc<RocqType>,
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
        self_ty: Rc<RocqType>,
        of_trait: Rc<Path>,
        trait_const_params: Vec<Rc<Expr>>,
        trait_ty_params: Vec<Rc<RocqType>>,
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
    fields: Vec<(String, Rc<RocqType>)>,
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
            FieldWithDefault::RequiredValue(value) => Some(value),
            FieldWithDefault::OptionalValue(value) => Some(value),
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
    let body = body
        .and_then(|body| compile_function_body(env, args.as_ref(), body, is_axiom, ret_ty.clone()));

    Rc::new(FnSigAndBody { args, ret_ty, body })
}

/// Check if the function body is actually the main test function calling to all
/// tests in the file. If so, we do not want to compile it.
fn check_if_is_test_main_function(env: &Env, body_id: &rustc_hir::BodyId) -> bool {
    let body = env.tcx.hir_body(*body_id);
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

fn item_ident(item: &Item) -> Option<rustc_span::Ident> {
    item.kind.ident()
}

fn item_name(env: &Env, item: &Item, is_value: IsValue) -> String {
    let name = item_ident(item)
        .map(|ident| to_valid_rocq_name(is_value, ident.name.as_str()))
        .unwrap_or_else(|| "anonymous".to_string());
    let disambiguator = env
        .tcx
        .def_path(item.owner_id.to_def_id())
        .data
        .last()
        .map(|item| item.disambiguator)
        .unwrap_or(0);

    if disambiguator == 0 {
        name
    } else {
        format!("{name}_{disambiguator}")
    }
}

fn const_rhs_body_id(rhs: &ConstItemRhs) -> Option<rustc_hir::BodyId> {
    match rhs {
        ConstItemRhs::Body(body_id) => Some(*body_id),
        ConstItemRhs::TypeConst(_) => None,
    }
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
        let attribute = Symbol::intern(attribute);
        if attr
            .meta_item_list()
            .is_some_and(|items| items.iter().any(|item| item.has_name(attribute)))
        {
            return true;
        }
    }
    false
}

fn check_lint_attribute_axiom<'a, Item: Into<rustc_hir::OwnerNode<'a>>>(
    env: &Env,
    item: Item,
) -> bool {
    check_lint_attribute(env, item, "rocq_axiom")
}

fn get_item_ids_for_parent(env: &Env, expected_parent: rustc_hir::def_id::DefId) -> Vec<ItemId> {
    env.tcx
        .hir_free_items()
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
        ItemKind::Static(..) | ItemKind::Const(..) | ItemKind::Fn { .. } => IsValue::Yes,
        _ => IsValue::No,
    };
    let name = item_name(env, item, is_value);
    let path = compile_def_id(env, item.owner_id.to_def_id());

    match &item.kind {
        ItemKind::ExternCrate(..) => vec![],
        ItemKind::Use(..) => vec![],
        ItemKind::Static(_, ident, ty, body_id) => {
            if check_if_test_declaration(ty) {
                return vec![];
            }
            // skip const _ : ... = ...
            if ident.name.as_str() == "_" {
                return vec![];
            }

            let ty = compile_type(env, &item.owner_id.def_id, ty);
            let value_without_alloc = if env.axiomatize {
                None
            } else {
                Some(compile_hir_id(env, body_id.hir_id))
            };
            let value =
                value_without_alloc.map(|value_without_alloc| value_without_alloc.alloc(ty));

            vec![Rc::new(TopLevelItem::Const { name, path, value })]
        }
        ItemKind::Const(ident, _, ty, rhs) => {
            if check_if_test_declaration(ty) {
                return vec![];
            }
            // skip const _ : ... = ...
            if ident.name.as_str() == "_" {
                return vec![];
            }

            let value = if env.axiomatize {
                None
            } else {
                const_rhs_body_id(rhs).map(|body_id| compile_hir_id(env, body_id.hir_id))
            };

            vec![Rc::new(TopLevelItem::Const { name, path, value })]
        }
        ItemKind::Fn {
            sig: fn_sig,
            generics,
            body: body_id,
            ..
        } => {
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
        ItemKind::Macro(..) => vec![],
        ItemKind::Mod(_, module) => {
            let items = module
                .item_ids
                .iter()
                .flat_map(|item_id| {
                    let item = env.tcx.hir_item(*item_id);

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
                let foreign_item = env.tcx.hir_foreign_item(*item);
                let is_value = match &foreign_item.kind {
                    rustc_hir::ForeignItemKind::Fn(..) | rustc_hir::ForeignItemKind::Static(..) => {
                        IsValue::Yes
                    }
                    rustc_hir::ForeignItemKind::Type => IsValue::No,
                };
                let name = to_valid_rocq_name(is_value, foreign_item.ident.name.as_str());
                let path = Path::concat(&[path.clone(), Path::new(std::slice::from_ref(&name))]);

                match &foreign_item.kind {
                    rustc_hir::ForeignItemKind::Fn(sign, _, generics) => {
                        let fn_decl_and_body = HirFnDeclAndBody {
                            decl: sign.decl,
                            body: None,
                        };

                        Rc::new(TopLevelItem::Definition {
                            name,
                            path,
                            snippet: None,
                            definition: FunDefinition::compile(
                                env,
                                generics,
                                fn_decl_and_body,
                                false,
                            ),
                        })
                    }
                    rustc_hir::ForeignItemKind::Static(..) => Rc::new(TopLevelItem::Const {
                        name,
                        path,
                        value: None,
                    }),
                    rustc_hir::ForeignItemKind::Type => Rc::new(TopLevelItem::TypeForeign { name }),
                }
            })
            .collect_vec(),
        ItemKind::GlobalAsm { .. } => vec![Rc::new(TopLevelItem::Error {
            message: "GlobalAsm".to_string(),
        })],
        ItemKind::TyAlias(_, generics, ty) => vec![Rc::new(TopLevelItem::TypeAlias {
            name,
            path,
            ty: compile_type(env, &item.owner_id.def_id, ty),
            const_params: get_const_params(env, generics),
            ty_params: get_ty_params(env, generics),
        })],
        ItemKind::Enum(_, generics, enum_def) => {
            let const_params = get_const_params(env, generics);
            let ty_params = get_ty_params(env, generics);
            let mut discriminant: u128 = 0;

            vec![Rc::new(TopLevelItem::TypeEnum {
                name,
                path,
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
                        if let Some(annon_const) = &variant.disr_expr {
                            let body = env.tcx.hir_body(annon_const.body);
                            let value = body.value;
                            match value.kind {
                                rustc_hir::ExprKind::Lit(rustc_span::source_map::Spanned {
                                    node: rustc_ast::ast::LitKind::Int(explicit_discriminant, _),
                                    ..
                                }) => discriminant = explicit_discriminant.get(),
                                _ => {
                                    let span = &item.span;
                                    let warning_msg = "Only explicit discriminants are supported.";
                                    let note_msg = "Replace it by a computed value.";
                                    emit_warning_with_note(env, span, warning_msg, Some(note_msg));
                                }
                            }
                        }
                        let result = Rc::new(TypeEnumVariant {
                            name,
                            item: Rc::new(fields),
                            discriminant,
                        });

                        discriminant += 1;

                        result
                    })
                    .collect(),
            })]
        }
        ItemKind::Struct(_, generics, body) => {
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
                                to_valid_rocq_name(IsValue::No, field.ident.name.as_str()),
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
        ItemKind::Union(..) => vec![Rc::new(TopLevelItem::Error {
            message: "Union".to_string(),
        })],
        ItemKind::Trait(_, _, _, _, generics, _, items) => {
            vec![Rc::new(TopLevelItem::Trait {
                name,
                path,
                const_params: get_const_params(env, generics),
                ty_params: get_ty_params(env, generics),
                body: items
                    .iter()
                    .map(|item| {
                        let item = env.tcx.hir_trait_item(*item);
                        let const_params = get_const_params(env, item.generics);
                        let ty_params = get_ty_params(env, item.generics);
                        let body = compile_trait_item_body(env, const_params, ty_params, item);
                        let is_value = match body.as_ref() {
                            TraitItem::Definition { .. } | TraitItem::DefinitionWithDefault(..) => {
                                IsValue::Yes
                            }
                            TraitItem::Type() => IsValue::No,
                        };

                        (to_valid_rocq_name(is_value, item.ident.name.as_str()), body)
                    })
                    .collect(),
            })]
        }
        ItemKind::TraitAlias(..) => {
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
                        .associated_items(trait_ref.trait_ref.trait_def_id().unwrap())
                        .in_definition_order()
                        .filter(|item| item.defaultness(env.tcx).has_value())
                        .filter_map(|item| {
                            item.opt_name()
                                .map(|name| to_valid_rocq_name(IsValue::Yes, name.as_str()))
                        })
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
                    let impl_generics = env.tcx.generics_of(item.owner_id.def_id);
                    let impl_trait_header = env.tcx.impl_trait_header(item.owner_id.def_id);
                    let trait_params = impl_trait_header.trait_ref.instantiate_identity().args;
                    let trait_const_params = trait_params
                        .iter()
                        .skip(1)
                        .filter_map(|generic_arg| {
                            generic_arg.as_const().as_ref().map(|ct| {
                                crate::thir_expression::compile_const(env, &item.span, ct)
                            })
                        })
                        .collect();
                    let trait_ty_params = trait_params
                        .iter()
                        .skip(1)
                        .filter_map(|generic_arg| {
                            generic_arg.as_type().as_ref().map(|ty| {
                                crate::thir_ty::compile_type(env, &item.span, impl_generics, ty)
                            })
                        })
                        .collect();

                    vec![Rc::new(TopLevelItem::TraitImpl {
                        generic_consts,
                        generic_tys,
                        predicates,
                        self_ty,
                        of_trait: compile_path(env, trait_ref.trait_ref.path),
                        trait_const_params,
                        trait_ty_params,
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

/// [compile_top_level_item] compiles hir [Item]s into rocq-of-rust (optional)
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
        ItemKind::Mod(..) => vec![],
        _ => get_item_ids_for_parent(env, item.item_id().owner_id.to_def_id()),
    };
    let local_items = local_item_ids
        .into_iter()
        .flat_map(|item_id| {
            let item = env.tcx.hir_item(item_id);

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
                name: item_name(env, item, IsValue::No),
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
            .prefer_remapped_unconditionally()
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
fn compile_impl_item_refs(env: &Env, item_refs: &[ImplItemId]) -> Vec<Rc<ImplItem>> {
    item_refs
        .iter()
        .map(|item_ref| compile_impl_item(env, env.tcx.hir_impl_item(*item_ref)))
        .collect()
}

/// compiles an item
fn compile_impl_item<'a>(env: &Env<'a>, item: &'a rustc_hir::ImplItem) -> Rc<ImplItem> {
    let is_value = match &item.kind {
        rustc_hir::ImplItemKind::Const(..) | rustc_hir::ImplItemKind::Fn(..) => IsValue::Yes,
        rustc_hir::ImplItemKind::Type(..) => IsValue::No,
    };
    let source_name = item.ident.name.as_str().to_string();
    let name = to_valid_rocq_name(is_value, source_name.as_str());
    let snippet = Snippet::of_span(env, &item.span);
    let kind = match &item.kind {
        rustc_hir::ImplItemKind::Const(ty, body_id) => {
            let ty = compile_type(env, &item.owner_id.def_id, ty);
            let body = if env.axiomatize {
                None
            } else {
                Some(compile_hir_id(env, body_id.hir_id()))
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
        source_name,
        snippet,
        kind,
    })
}

/// returns the body corresponding to the given body_id
fn get_body<'a>(env: &Env<'a>, body_id: &rustc_hir::BodyId) -> &'a rustc_hir::Body<'a> {
    env.tcx.hir_body(*body_id)
}

// compiles the body of a function
fn compile_function_body(
    env: &Env,
    args: Option<&FnArgs>,
    body: &rustc_hir::Body,
    is_axiom: bool,
    ret_ty: Option<Rc<RocqType>>,
) -> Option<Rc<Expr>> {
    if env.axiomatize || is_axiom {
        return None;
    }

    let ret_ty = ret_ty.unwrap_or_else(|| RocqType::path(&["Expected ret_ty"]));

    let body_without_bindings = compile_hir_id(env, body.value.hir_id).read();

    if body_without_bindings.is_unimplemented() {
        return None;
    }

    let body_without_bindings = if body_without_bindings.has_return() {
        Rc::new(Expr::Call {
            func: Rc::new(Expr::CallTy {
                func: Expr::local_var("M.catch_return"),
                ty: ret_ty.clone(),
            }),
            args: vec![Rc::new(Expr::Lambda {
                args: vec![],
                body: body_without_bindings,
                is_for_match: false,
                form: LambdaForm::Function,
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
                        ret_ty.clone(),
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
                .map(|(name, ty, _)| (name.clone(), ty.clone()))
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
                (to_valid_rocq_name(IsValue::Yes, ident.name.as_str()), None)
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
            GenericParamKind::Const { .. } => Some(to_valid_rocq_name(
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
            GenericParamKind::Type { .. } => Some(to_valid_rocq_name(
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
        .flat_map(|predicate| match predicate.kind {
            rustc_hir::WherePredicateKind::BoundPredicate(predicate) => {
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
fn trait_bound_to_where_predicate(bound: Rc<TraitBound>, ty: Rc<RocqType>) -> Rc<WherePredicate> {
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
            GenericBound::Trait(ptraitref) => {
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
    ty_params: &[Rc<RocqType>],
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
    ty: Option<Rc<RocqType>>,
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

fn compile_top_level(tcx: &TyCtxt, opts: TopLevelOptions<'_>) -> Rc<TopLevel> {
    let env = Env {
        tcx: *tcx,
        axiomatize: opts.axiomatize,
    };
    let results = get_item_ids_for_parent(&env, rustc_hir::def_id::CRATE_DEF_ID.into())
        .iter()
        .flat_map(|item_id| {
            let item = tcx.hir_item(*item_id);
            compile_top_level_item_with_file_name(&env, item)
        })
        .collect();

    Rc::new(TopLevel(results))
}

const LINE_WIDTH: usize = 100;

fn runtime_file_path(file_names: &[String]) -> String {
    let root_file = file_names
        .iter()
        .find(|file_name| {
            matches!(
                FilePath::new(file_name)
                    .file_name()
                    .and_then(|name| name.to_str()),
                Some("lib.rs" | "main.rs")
            )
        })
        .or_else(|| file_names.first());

    root_file
        .and_then(|file_name| FilePath::new(file_name).parent())
        .unwrap_or_else(|| FilePath::new(""))
        .join("rocq_of_rust_runtime.v")
        .to_string_lossy()
        .to_string()
}

fn runtime_module_name(module_prefix: &str, file_name: &str) -> Option<String> {
    let components = FilePath::new(file_name)
        .components()
        .map(|component| component.as_os_str().to_string_lossy().to_string())
        .collect_vec();
    let src_index = components
        .iter()
        .rposition(|component| component == "src")?;
    let mut module_path = vec![module_prefix.to_string()];

    for component in &components[src_index + 1..] {
        module_path.push(
            FilePath::new(component)
                .with_extension("")
                .to_string_lossy()
                .to_string(),
        );
    }

    Some(module_path.join("."))
}

fn runtime_imports(module_prefix: &str, file_names: &[String]) -> String {
    let mut module_names = file_names
        .iter()
        .filter_map(|file_name| runtime_module_name(module_prefix, file_name))
        .collect_vec();
    module_names.sort();
    module_names.dedup();

    module_names
        .into_iter()
        .map(|module_name| format!("Require Import {module_name}.\n"))
        .collect()
}

pub(crate) fn translate_top_level(
    tcx: &TyCtxt,
    opts: TopLevelOptions<'_>,
) -> HashMap<String, (String, String)> {
    let top_level = compile_top_level(tcx, opts);
    let top_level_groups = group_top_level_by_file_name(top_level.clone());
    let include_runtime_in_file = !opts.axiomatize && !opts.separate_runtime_file;

    let mut translations = top_level_groups
        .into_iter()
        .map(|(file_name, top_level)| {
            (
                file_name,
                (
                    top_level.to_pretty(LINE_WIDTH, include_runtime_in_file),
                    top_level.to_json(),
                ),
            )
        })
        .collect::<HashMap<_, _>>();

    if !opts.axiomatize && opts.separate_runtime_file {
        let mut file_names = translations.keys().cloned().collect_vec();
        file_names.sort();
        let crate_name = tcx.crate_name(rustc_hir::def_id::LOCAL_CRATE).to_string();
        let module_prefix = opts.runtime_module_prefix.unwrap_or(&crate_name);
        let runtime = format!(
            "{}{}\n{}",
            HEADER,
            runtime_imports(module_prefix, &file_names),
            top_level.runtime_to_pretty(LINE_WIDTH),
        );

        translations.insert(runtime_file_path(&file_names), (runtime, String::new()));
    }

    translations
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

    fn make_dyn_parm(&mut self, arg: Rc<RocqType>) -> Rc<RocqType> {
        if let Some((name, arg)) = arg.clone().match_ref() {
            let ct = self.make_dyn_parm(arg);
            Rc::new(RocqType::Application {
                func: RocqType::path(&[&name]),
                consts: vec![],
                tys: vec![ct],
            })
        } else if let RocqType::Dyn { traits } = arg.as_ref() {
            // We suppose `dyn` is only associated with one trait so we can directly extract the first element
            if let Some(trait_) = traits.first() {
                let dy_name = self.next(trait_.clone());
                RocqType::var(dy_name.as_ref())
            } else {
                Rc::new(RocqType::Dyn {
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
    fn to_rocq<'a>(
        &'a self,
        name: String,
        snippet: &'a Option<Rc<Snippet>>,
        generic_consts: Vec<String>,
        generic_tys: Vec<String>,
        with_extra_self_ty: bool,
    ) -> Vec<Rc<rocq::TopLevelItem>> {
        let generics = [generic_consts.clone(), generic_tys.clone()].concat();

        [
            match snippet {
                Some(snippet) => vec![snippet.to_rocq()],
                None => vec![],
            },
            match &self.signature_and_body.body {
                None => vec![Rc::new(rocq::TopLevelItem::Definition(
                    rocq::Definition::new(
                        &name,
                        Rc::new(rocq::DefinitionKind::Assumption {
                            ty: Rc::new(rocq::Expression::PiType {
                                args: rocq::ArgDecl::of_const_ty_params(
                                    &generic_consts,
                                    &generic_tys,
                                    rocq::ArgSpecKind::Explicit,
                                ),
                                image: Rc::new(rocq::Expression::FunctionType {
                                    domains: vec![
                                        rocq::Expression::just_name("list")
                                            .apply(rocq::Expression::just_name("Value.t")),
                                        rocq::Expression::just_name("list")
                                            .apply(rocq::Expression::just_name("Ty.t")),
                                        rocq::Expression::just_name("list")
                                            .apply(rocq::Expression::just_name("Value.t")),
                                    ],
                                    image: rocq::Expression::just_name("M"),
                                }),
                            }),
                        }),
                    ),
                ))],
                Some(body) => {
                    let body = Rc::new(rocq::Expression::Match {
                        scrutinees: vec![
                            rocq::Expression::just_name("ε"),
                            rocq::Expression::just_name("τ"),
                            rocq::Expression::just_name("α"),
                        ],
                        arms: vec![
                            (
                                vec![
                                    Rc::new(rocq::Expression::List {
                                        exprs: self
                                            .const_params
                                            .iter()
                                            .map(|const_param| {
                                                rocq::Expression::name_pattern(const_param)
                                            })
                                            .collect(),
                                    }),
                                    Rc::new(rocq::Expression::List {
                                        exprs: self
                                            .ty_params
                                            .iter()
                                            .map(|ty_param| {
                                                rocq::Expression::name_pattern(ty_param)
                                            })
                                            .collect(),
                                    }),
                                    Rc::new(rocq::Expression::List {
                                        exprs: self
                                            .signature_and_body
                                            .args
                                            .as_ref()
                                            .unwrap_or(&vec![])
                                            .iter()
                                            .map(|(name, _, _)| {
                                                rocq::Expression::name_pattern(name)
                                            })
                                            .collect(),
                                    }),
                                ],
                                rocq::Expression::monadic(body.to_rocq()),
                            ),
                            (
                                vec![
                                    Rc::new(rocq::Expression::Wild),
                                    Rc::new(rocq::Expression::Wild),
                                    Rc::new(rocq::Expression::Wild),
                                ],
                                rocq::Expression::just_name("M.impossible").apply(Rc::new(
                                    rocq::Expression::String(
                                        "wrong number of arguments".to_string(),
                                    ),
                                )),
                            ),
                        ],
                    });

                    vec![Rc::new(rocq::TopLevelItem::Definition(
                        rocq::Definition::new(
                            &name,
                            Rc::new(rocq::DefinitionKind::Alias {
                                args: [
                                    rocq::ArgDecl::of_const_ty_params(
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
                                        rocq::ArgSpecKind::Explicit,
                                    ),
                                    rocq::ArgDecl::polymorphic_function_params(),
                                ]
                                .concat(),
                                ty: Some(rocq::Expression::just_name("M")),
                                body: if !generics.is_empty() && !with_extra_self_ty {
                                    Rc::new(rocq::Expression::Let {
                                        suffix: "".to_string(),
                                        name: Some("Self".to_string()),
                                        ty: Some(rocq::Expression::just_name("Ty.t")),
                                        init: rocq::Expression::just_name("Self").apply_many(
                                            &generics
                                                .iter()
                                                .map(|generic_ty| {
                                                    rocq::Expression::just_name(generic_ty)
                                                })
                                                .collect_vec(),
                                        ),
                                        body,
                                    })
                                } else {
                                    body
                                },
                            }),
                        ),
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

    fn is_definition(&self) -> bool {
        match self {
            ImplItemKind::Const { body, .. } => body.is_some(),
            ImplItemKind::Definition { definition } => definition.signature_and_body.body.is_some(),
            ImplItemKind::Type { .. } => true,
        }
    }

    fn to_rocq<'a>(
        &'a self,
        name: &'a str,
        generic_consts: Vec<String>,
        generic_tys: Vec<String>,
    ) -> Vec<Rc<rocq::TopLevelItem>> {
        let definition_name = self.to_definition_name(name.to_string());
        let generics = [generic_consts.clone(), generic_tys.clone()].concat();

        match self {
            ImplItemKind::Const { ty, body } => vec![
                Rc::new(rocq::TopLevelItem::Comment(vec![ty.to_rocq()])),
                match body {
                    None => Rc::new(rocq::TopLevelItem::Definition(rocq::Definition::new(
                        &definition_name,
                        Rc::new(rocq::DefinitionKind::Assumption {
                            ty: Rc::new(rocq::Expression::PiType {
                                args: rocq::ArgDecl::of_const_ty_params(
                                    &generic_consts,
                                    &generic_tys,
                                    rocq::ArgSpecKind::Explicit,
                                ),
                                image: rocq::Expression::just_name("Value.t"),
                            }),
                        }),
                    ))),
                    Some(body) => {
                        let body = rocq::Expression::monadic(body.to_rocq());

                        Rc::new(rocq::TopLevelItem::Definition(rocq::Definition::new(
                            &definition_name,
                            Rc::new(rocq::DefinitionKind::Alias {
                                args: [
                                    rocq::ArgDecl::of_const_ty_params(
                                        &generic_consts,
                                        &generic_tys,
                                        rocq::ArgSpecKind::Explicit,
                                    ),
                                    rocq::ArgDecl::polymorphic_function_params(),
                                ]
                                .concat(),
                                ty: Some(rocq::Expression::just_name("M")),
                                body: if !generics.is_empty() {
                                    Rc::new(rocq::Expression::Let {
                                        suffix: "".to_string(),
                                        name: Some("Self".to_string()),
                                        ty: Some(rocq::Expression::just_name("Ty.t")),
                                        init: rocq::Expression::just_name("Self").apply_many(
                                            &generics
                                                .iter()
                                                .map(|generic_ty| {
                                                    rocq::Expression::just_name(generic_ty)
                                                })
                                                .collect_vec(),
                                        ),
                                        body,
                                    })
                                } else {
                                    body
                                },
                            }),
                        )))
                    }
                },
            ],
            ImplItemKind::Definition { definition, .. } => {
                definition.to_rocq(definition_name, &None, generic_consts, generic_tys, false)
            }
            ImplItemKind::Type { ty } => {
                vec![Rc::new(rocq::TopLevelItem::Definition(
                    rocq::Definition::new(
                        &definition_name,
                        Rc::new(rocq::DefinitionKind::Alias {
                            args: rocq::ArgDecl::of_const_ty_params(
                                &generic_consts,
                                &generic_tys,
                                rocq::ArgSpecKind::Explicit,
                            ),
                            ty: Some(rocq::Expression::just_name("Ty.t")),
                            body: ty.to_rocq(),
                        }),
                    ),
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

    fn to_rocq(&self) -> Rc<rocq::TopLevelItem> {
        let nb_quotes = self
            .0
            .iter()
            .map(|line| line.chars().filter(|c| *c == '"').count())
            .sum::<usize>();

        Rc::new(rocq::TopLevelItem::Comment(
            [
                self.0
                    .iter()
                    // We do this replace to avoid messing up with the Rocq comments
                    .map(|line| {
                        Rc::new(rocq::Expression::Message(
                            line.replace("(*", "( *").replace("*)", "* )"),
                        ))
                    })
                    .collect(),
                if nb_quotes % 2 == 0 {
                    vec![]
                } else {
                    vec![Rc::new(rocq::Expression::Message("\"".to_string()))]
                },
            ]
            .concat(),
        ))
    }
}

impl VariantItem {
    fn to_rocq(&self) -> Rc<rocq::Expression> {
        match self {
            VariantItem::Struct { fields } => {
                rocq::Expression::just_name("StructRecord").apply(Rc::new(rocq::Expression::List {
                    exprs: fields
                        .iter()
                        .map(|(name, ty)| {
                            Rc::new(rocq::Expression::Tuple(vec![
                                Rc::new(rocq::Expression::String(name.to_string())),
                                ty.to_rocq(),
                            ]))
                        })
                        .collect(),
                }))
            }
            VariantItem::Tuple { tys } => {
                rocq::Expression::just_name("StructTuple").apply(Rc::new(rocq::Expression::List {
                    exprs: tys.iter().map(|ty| ty.to_rocq()).collect(),
                }))
            }
        }
    }
}

impl TypeEnumVariant {
    fn to_rocq(&self) -> Rc<rocq::Expression> {
        let Self {
            name,
            item,
            discriminant: _,
        } = self;

        Rc::new(rocq::Expression::Record {
            fields: vec![
                Rc::new(rocq::Field {
                    name: "name".to_string(),
                    args: vec![],
                    body: Rc::new(rocq::Expression::String(name.to_string())),
                }),
                Rc::new(rocq::Field {
                    name: "item".to_string(),
                    args: vec![],
                    body: item.to_rocq(),
                }),
            ],
        })
    }
}

impl TypeStructStruct {
    fn to_rocq(&self) -> Rc<rocq::Expression> {
        rocq::Expression::just_name("StructRecord").apply(Rc::new(rocq::Expression::Record {
            fields: vec![
                Rc::new(rocq::Field {
                    name: "name".to_string(),
                    args: vec![],
                    body: Rc::new(rocq::Expression::String(self.name.to_string())),
                }),
                Rc::new(rocq::Field {
                    name: "const_params".to_string(),
                    args: vec![],
                    body: Rc::new(rocq::Expression::List {
                        exprs: self
                            .const_params
                            .iter()
                            .map(|name| Rc::new(rocq::Expression::String(name.to_string())))
                            .collect(),
                    }),
                }),
                Rc::new(rocq::Field {
                    name: "ty_params".to_string(),
                    args: vec![],
                    body: Rc::new(rocq::Expression::List {
                        exprs: self
                            .ty_params
                            .iter()
                            .map(|name| Rc::new(rocq::Expression::String(name.to_string())))
                            .collect(),
                    }),
                }),
                Rc::new(rocq::Field {
                    name: "fields".to_string(),
                    args: vec![],
                    body: Rc::new(rocq::Expression::List {
                        exprs: self
                            .fields
                            .iter()
                            .map(|(name, ty)| {
                                Rc::new(rocq::Expression::Tuple(vec![
                                    Rc::new(rocq::Expression::String(name.to_string())),
                                    ty.to_rocq(),
                                ]))
                            })
                            .collect(),
                    }),
                }),
            ],
        }))
    }
}

fn trait_impl_module_name(
    predicates: &[Rc<WherePredicate>],
    self_ty: &RocqType,
    of_trait: &Path,
    trait_const_params: &[Rc<Expr>],
    trait_ty_params: &[Rc<RocqType>],
) -> String {
    format!(
        "Impl_{}{}{}{}_for_{}",
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
                            | FieldWithDefault::OptionalValue(ty) => {
                                Some(format!("_{}", ty.to_name()))
                            }
                            FieldWithDefault::Default => None,
                        })
                        .join(""),
                )
            })
            .collect::<String>(),
        trait_const_params
            .iter()
            .map(|const_| format!("_{}", const_.to_name()))
            .join(""),
        trait_ty_params
            .iter()
            .map(|ty| format!("_{}", ty.to_name()))
            .join(""),
        self_ty.to_name()
    )
}

impl TopLevelItem {
    #[allow(clippy::format_collect)]
    fn to_rocq(&self) -> Vec<Rc<rocq::TopLevelItem>> {
        match self {
            TopLevelItem::Const { name, path, value } => vec![
                match value {
                    None => Rc::new(rocq::TopLevelItem::Definition(rocq::Definition::new(
                        name,
                        Rc::new(rocq::DefinitionKind::Assumption {
                            ty: rocq::Expression::just_name("PolymorphicFunction.t"),
                        }),
                    ))),
                    Some(value) => Rc::new(rocq::TopLevelItem::Definition(rocq::Definition::new(
                        name,
                        Rc::new(rocq::DefinitionKind::Alias {
                            args: rocq::ArgDecl::polymorphic_function_params(),
                            ty: Some(rocq::Expression::just_name("M")),
                            body: rocq::Expression::monadic(value.to_rocq()),
                        }),
                    ))),
                },
                Rc::new(rocq::TopLevelItem::Line),
                Rc::new(rocq::TopLevelItem::Definition(rocq::Definition::new(
                    &format!("Instance_IsConstant_{name}"),
                    Rc::new(rocq::DefinitionKind::AdmittedInstance {
                        locality: "Global".to_string(),
                        ty: rocq::Expression::just_name("M.IsFunction.C").apply_many(&[
                            Rc::new(rocq::Expression::String(path.to_string())),
                            rocq::Expression::just_name(name),
                        ]),
                    }),
                ))),
                if value.is_some() {
                    Rc::new(rocq::TopLevelItem::Hint {
                        kind: "Global Typeclasses Opaque".to_string(),
                        name: name.to_string(),
                        database: None,
                    })
                } else {
                    Rc::new(rocq::TopLevelItem::Empty)
                },
            ],
            TopLevelItem::Definition {
                name,
                path,
                snippet,
                definition,
            } => [
                definition.to_rocq(name.to_string(), snippet, vec![], vec![], false),
                vec![
                    Rc::new(rocq::TopLevelItem::Line),
                    Rc::new(rocq::TopLevelItem::Definition(rocq::Definition::new(
                        &format!("Instance_IsFunction_{name}"),
                        Rc::new(rocq::DefinitionKind::AdmittedInstance {
                            locality: "Global".to_string(),
                            ty: rocq::Expression::just_name("M.IsFunction.C").apply_many(&[
                                Rc::new(rocq::Expression::String(path.to_string())),
                                rocq::Expression::just_name(name),
                            ]),
                        }),
                    ))),
                    if definition.signature_and_body.body.is_some() {
                        Rc::new(rocq::TopLevelItem::Hint {
                            kind: "Global Typeclasses Opaque".to_string(),
                            name: name.to_string(),
                            database: None,
                        })
                    } else {
                        Rc::new(rocq::TopLevelItem::Empty)
                    },
                ],
            ]
            .concat(),
            TopLevelItem::Module { name, body } => {
                vec![Rc::new(rocq::TopLevelItem::Module(rocq::Module::new(
                    name,
                    body.to_rocq(false),
                )))]
            }
            TopLevelItem::TypeAlias {
                name,
                path,
                ty,
                const_params,
                ty_params,
            } => vec![Rc::new(rocq::TopLevelItem::Definition(
                rocq::Definition::new(
                    name,
                    Rc::new(rocq::DefinitionKind::Axiom {
                        ty: Rc::new(rocq::Expression::PiType {
                            args: rocq::ArgDecl::of_const_ty_params(
                                const_params,
                                ty_params,
                                rocq::ArgSpecKind::Explicit,
                            ),
                            image: Rc::new(rocq::Expression::Equality {
                                lhs: RocqType::Application {
                                    func: Rc::new(RocqType::Path { path: path.clone() }),
                                    consts: const_params
                                        .iter()
                                        .map(|const_param| Expr::local_var(const_param))
                                        .collect(),
                                    tys: ty_params
                                        .iter()
                                        .map(|ty_param| RocqType::var(ty_param))
                                        .collect(),
                                }
                                .to_rocq(),
                                rhs: ty.to_rocq(),
                            }),
                        }),
                    }),
                ),
            ))],
            TopLevelItem::TypeEnum {
                name,
                path,
                const_params,
                ty_params,
                variants,
            } => [
                vec![
                    Rc::new(rocq::TopLevelItem::Comment(vec![
                        Rc::new(rocq::Expression::Message(format!("Enum {name}"))),
                        Rc::new(rocq::Expression::Record {
                            fields: vec![
                                Rc::new(rocq::Field {
                                    name: "const_params".to_string(),
                                    args: vec![],
                                    body: Rc::new(rocq::Expression::List {
                                        exprs: const_params
                                            .iter()
                                            .map(|name| {
                                                Rc::new(rocq::Expression::String(name.to_string()))
                                            })
                                            .collect(),
                                    }),
                                }),
                                Rc::new(rocq::Field {
                                    name: "ty_params".to_string(),
                                    args: vec![],
                                    body: Rc::new(rocq::Expression::List {
                                        exprs: ty_params
                                            .iter()
                                            .map(|name| {
                                                Rc::new(rocq::Expression::String(name.to_string()))
                                            })
                                            .collect(),
                                    }),
                                }),
                                Rc::new(rocq::Field {
                                    name: "variants".to_string(),
                                    args: vec![],
                                    body: Rc::new(rocq::Expression::List {
                                        exprs: variants
                                            .iter()
                                            .map(|variant| variant.to_rocq())
                                            .collect(),
                                    }),
                                }),
                            ],
                        }),
                    ])),
                    Rc::new(rocq::TopLevelItem::Line),
                ],
                variants
                    .iter()
                    .map(|variant| {
                        Rc::new(rocq::TopLevelItem::Definition(rocq::Definition::new(
                            &format!("IsDiscriminant_{name}_{}", variant.name),
                            Rc::new(rocq::DefinitionKind::Axiom {
                                ty: rocq::Expression::just_name("M.IsDiscriminant").apply_many(&[
                                    Rc::new(rocq::Expression::String(format!(
                                        "{path}::{}",
                                        variant.name
                                    ))),
                                    Rc::new(rocq::Expression::U128(variant.discriminant)),
                                ]),
                            }),
                        )))
                    })
                    .collect(),
            ]
            .concat(),
            TopLevelItem::TypeStructStruct(tss) => {
                vec![Rc::new(rocq::TopLevelItem::Comment(vec![tss.to_rocq()]))]
            }
            TopLevelItem::TypeStructTuple {
                name,
                const_params,
                ty_params,
                fields,
            } => vec![Rc::new(rocq::TopLevelItem::Comment(vec![
                rocq::Expression::just_name("StructTuple").apply(Rc::new(
                    rocq::Expression::Record {
                        fields: vec![
                            Rc::new(rocq::Field {
                                name: "name".to_string(),
                                args: vec![],
                                body: Rc::new(rocq::Expression::String(name.to_string())),
                            }),
                            Rc::new(rocq::Field {
                                name: "const_params".to_string(),
                                args: vec![],
                                body: Rc::new(rocq::Expression::List {
                                    exprs: const_params
                                        .iter()
                                        .map(|name| {
                                            Rc::new(rocq::Expression::String(name.to_string()))
                                        })
                                        .collect(),
                                }),
                            }),
                            Rc::new(rocq::Field {
                                name: "ty_params".to_string(),
                                args: vec![],
                                body: Rc::new(rocq::Expression::List {
                                    exprs: ty_params
                                        .iter()
                                        .map(|name| {
                                            Rc::new(rocq::Expression::String(name.to_string()))
                                        })
                                        .collect(),
                                }),
                            }),
                            Rc::new(rocq::Field {
                                name: "fields".to_string(),
                                args: vec![],
                                body: Rc::new(rocq::Expression::List {
                                    exprs: fields.iter().map(|ty| ty.to_rocq()).collect(),
                                }),
                            }),
                        ],
                    },
                )),
            ]))],
            TopLevelItem::TypeForeign { name } => {
                vec![Rc::new(rocq::TopLevelItem::Comment(vec![Rc::new(
                    rocq::Expression::Message(format!("Foreign type '{name}'")),
                )]))]
            }
            TopLevelItem::Impl {
                generic_consts,
                generic_tys,
                self_ty,
                items,
            } => {
                let module_name = format!("Impl_{}", self_ty.to_name());
                let generics: Vec<String> = [generic_consts.clone(), generic_tys.clone()].concat();
                let items_rocq = items
                    .iter()
                    .flat_map(|item| {
                        let ImplItem {
                            name,
                            source_name,
                            snippet,
                            kind,
                        } = item.as_ref();
                        let axiom_name = match kind.as_ref() {
                            ImplItemKind::Const { .. } => {
                                format!("AssociatedConstant_{name}")
                            }
                            ImplItemKind::Definition { .. } => {
                                format!("AssociatedFunction_{name}")
                            }
                            ImplItemKind::Type { .. } => {
                                format!("AssociatedType_{name}")
                            }
                        };
                        [
                            vec![Rc::new(rocq::TopLevelItem::Line)],
                            match snippet {
                                None => vec![],
                                Some(snippet) => vec![snippet.to_rocq()],
                            },
                            kind.to_rocq(name, generic_consts.clone(), generic_tys.clone()),
                            vec![
                                Rc::new(rocq::TopLevelItem::Line),
                                Rc::new(rocq::TopLevelItem::Definition(rocq::Definition::new(
                                    &axiom_name,
                                    Rc::new(rocq::DefinitionKind::AdmittedInstance {
                                        locality: "Global".to_string(),
                                        ty: Rc::new(rocq::Expression::PiType {
                                            args: rocq::ArgDecl::of_const_ty_params(
                                                generic_consts,
                                                generic_tys,
                                                rocq::ArgSpecKind::Explicit,
                                            ),
                                            image: rocq::Expression::just_name(
                                                match kind.as_ref() {
                                                    ImplItemKind::Const { .. } => {
                                                        "M.IsAssociatedFunction.C"
                                                    }
                                                    ImplItemKind::Definition { .. } => {
                                                        "M.IsAssociatedFunction.C"
                                                    }
                                                    ImplItemKind::Type { .. } => {
                                                        "M.IsAssociatedType.Trait"
                                                    }
                                                },
                                            )
                                            .apply_many(&[
                                                rocq::Expression::just_name("Self").apply_many(
                                                    &generics
                                                        .iter()
                                                        .map(|generic| {
                                                            rocq::Expression::just_name(generic)
                                                        })
                                                        .collect_vec(),
                                                ),
                                                Rc::new(rocq::Expression::String(
                                                    source_name.to_string(),
                                                )),
                                                rocq::Expression::just_name(name).apply_many(
                                                    &generics
                                                        .iter()
                                                        .map(|generic| {
                                                            rocq::Expression::just_name(generic)
                                                        })
                                                        .collect_vec(),
                                                ),
                                            ]),
                                        }),
                                    }),
                                ))),
                                if kind.is_definition() {
                                    Rc::new(rocq::TopLevelItem::Hint {
                                        kind: "Global Typeclasses Opaque".to_string(),
                                        name: name.clone(),
                                        database: None,
                                    })
                                } else {
                                    Rc::new(rocq::TopLevelItem::Empty)
                                },
                            ],
                        ]
                        .concat()
                    })
                    .collect_vec();

                vec![Rc::new(rocq::TopLevelItem::Module(rocq::Module::new(
                    &module_name,
                    rocq::TopLevel::concat(&[
                        rocq::TopLevel::new(&[Rc::new(rocq::TopLevelItem::Definition(
                            rocq::Definition::new(
                                "Self",
                                Rc::new(rocq::DefinitionKind::Alias {
                                    args: rocq::ArgDecl::of_const_ty_params(
                                        generic_consts,
                                        generic_tys,
                                        rocq::ArgSpecKind::Explicit,
                                    ),
                                    ty: Some(rocq::Expression::just_name("Ty.t")),
                                    body: self_ty.to_rocq(),
                                }),
                            ),
                        ))]),
                        rocq::TopLevel::new(&items_rocq),
                    ]),
                )))]
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
                    Rc::new(rocq::TopLevelItem::Comment(vec![Rc::new(rocq::Expression::Message("Trait".to_string()))])),
                    Rc::new(rocq::TopLevelItem::Module(rocq::Module::new(
                        name,
                        rocq::TopLevel::new(
                            &body
                                .iter()
                                .flat_map(|(name, item)| match item.as_ref() {
                                    TraitItem::DefinitionWithDefault(fun_definition) => [
                                        fun_definition.to_rocq(
                                            name.to_string(),
                                            &None,
                                            const_params.clone(),
                                            ty_params.clone(),
                                            true,
                                        ),
                                        vec![
                                            Rc::new(rocq::TopLevelItem::Line),
                                            Rc::new(rocq::TopLevelItem::Definition(rocq::Definition::new(
                                            &format!("ProvidedMethod_{name}"),
                                            Rc::new(rocq::DefinitionKind::Axiom {
                                                ty: Rc::new(rocq::Expression::PiType {
                                                    args: rocq::ArgDecl::of_const_ty_params(
                                                        const_params,
                                                        ty_params,
                                                        rocq::ArgSpecKind::Explicit,
                                                    ),
                                                    image: rocq::Expression::just_name(
                                                        "M.IsProvidedMethod",
                                                    )
                                                    .apply_many(&[
                                                        Rc::new(rocq::Expression::String(path.to_string())),
                                                        Rc::new(rocq::Expression::String(name.to_string())),
                                                        rocq::Expression::just_name(name)
                                                            .apply_many(
                                                                &params
                                                                    .iter()
                                                                    .map(|param| {
                                                                        rocq::Expression::just_name(
                                                                            param,
                                                                        )
                                                                    })
                                                                    .collect_vec(),
                                                            ),
                                                    ]),
                                                }),
                                            }),
                                        ))),
                                    ],
                                    ]
                                    .concat(),
                                    _ => vec![],
                                })
                                .collect_vec(),
                        ),
                    ))),
                ]
            }
            TopLevelItem::TraitImpl {
                generic_consts,
                generic_tys,
                predicates,
                self_ty,
                of_trait,
                trait_const_params,
                trait_ty_params,
                items,
            } => {
                let generics = [generic_consts.clone(), generic_tys.clone()].concat();
                let module_name = trait_impl_module_name(
                    predicates,
                    self_ty,
                    of_trait,
                    trait_const_params,
                    trait_ty_params,
                );
                let items_rocq = items
                    .iter()
                    .filter_map(|item| {
                        Into::<Option<&ImplItemKind>>::into(item.kind.as_ref()).map(|kind| {
                            Rc::new(rocq::Expression::Tuple(vec![
                                Rc::new(rocq::Expression::String(item.name.to_string())),
                                rocq::Expression::just_name(match kind {
                                    ImplItemKind::Const { .. } => "InstanceField.Method",
                                    ImplItemKind::Definition { .. } => "InstanceField.Method",
                                    ImplItemKind::Type { .. } => "InstanceField.Ty",
                                })
                                .apply(
                                    rocq::Expression::just_name(
                                        &kind.to_definition_name(item.name.to_string()),
                                    )
                                    .apply_many(
                                        &generics
                                            .iter()
                                            .map(|generic| rocq::Expression::just_name(generic))
                                            .collect_vec(),
                                    ),
                                ),
                            ]))
                        })
                    })
                    .collect_vec();

                vec![Rc::new(rocq::TopLevelItem::Module(rocq::Module::new(
                    &module_name,
                    rocq::TopLevel::new(
                        &[
                            vec![
                                Rc::new(rocq::TopLevelItem::Definition(rocq::Definition::new(
                                    "Self",
                                    Rc::new(rocq::DefinitionKind::Alias {
                                        args: rocq::ArgDecl::of_const_ty_params(
                                            generic_consts,
                                            generic_tys,
                                            rocq::ArgSpecKind::Explicit,
                                        ),
                                        ty: Some(rocq::Expression::just_name("Ty.t")),
                                        body: self_ty.to_rocq(),
                                    }),
                                ))),
                                Rc::new(rocq::TopLevelItem::Line),
                            ],
                            items
                                .iter()
                                .filter_map(|item| {
                                    Into::<Option<&ImplItemKind>>::into(item.kind.as_ref()).map(
                                        |kind: &ImplItemKind| {
                                            [
                                                match &item.snippet {
                                                    None => vec![],
                                                    Some(snippet) => vec![snippet.to_rocq()],
                                                },
                                                kind.to_rocq(
                                                    item.name.as_str(),
                                                    generic_consts.clone(),
                                                    generic_tys.clone(),
                                                ),
                                                vec![Rc::new(rocq::TopLevelItem::Line)],
                                            ]
                                            .concat()
                                        },
                                    )
                                })
                                .concat(),
                            vec![Rc::new(rocq::TopLevelItem::Definition(
                                rocq::Definition::new(
                                    "Implements",
                                    Rc::new(rocq::DefinitionKind::Axiom {
                                        ty: Rc::new(rocq::Expression::PiType {
                                            args: rocq::ArgDecl::of_const_ty_params(
                                                generic_consts,
                                                generic_tys,
                                                rocq::ArgSpecKind::Explicit,
                                            ),
                                            image: rocq::Expression::just_name("M.IsTraitInstance")
                                                .apply_many(&[
                                                    Rc::new(rocq::Expression::String(
                                                        of_trait.to_string(),
                                                    )),
                                                    Rc::new(rocq::Expression::Comment(
                                                        "Trait polymorphic consts".to_string(),
                                                        Rc::new(rocq::Expression::List {
                                                            exprs: trait_const_params
                                                                .iter()
                                                                .map(|const_| const_.to_rocq())
                                                                .collect(),
                                                        }),
                                                    )),
                                                    Rc::new(rocq::Expression::Comment(
                                                        "Trait polymorphic types".to_string(),
                                                        Rc::new(rocq::Expression::List {
                                                            exprs: trait_ty_params
                                                                .iter()
                                                                .map(|ty| ty.to_rocq())
                                                                .collect(),
                                                        }),
                                                    )),
                                                    rocq::Expression::just_name("Self").apply_many(
                                                        &generics
                                                            .iter()
                                                            .map(|generic| {
                                                                rocq::Expression::just_name(generic)
                                                            })
                                                            .collect_vec(),
                                                    ),
                                                    Rc::new(rocq::Expression::Comment(
                                                        "Instance".to_string(),
                                                        Rc::new(rocq::Expression::List {
                                                            exprs: items_rocq,
                                                        }),
                                                    )),
                                                ]),
                                        }),
                                    }),
                                ),
                            ))],
                        ]
                        .concat(),
                    ),
                )))]
            }
            TopLevelItem::Error { message } => vec![Rc::new(rocq::TopLevelItem::Comment(vec![
                rocq::Expression::just_name("Error")
                    .apply(Rc::new(rocq::Expression::Message(message.clone()))),
            ]))],
        }
    }
}

impl TopLevel {
    fn function_table_entries(&self, module_path: &[String]) -> Vec<(String, Rc<Path>)> {
        self.0
            .iter()
            .flat_map(|entry| match entry.item.as_ref() {
                TopLevelItem::Const { name, path, .. }
                | TopLevelItem::Definition { name, path, .. } => {
                    let mut rocq_path = module_path.to_vec();
                    rocq_path.push(name.clone());

                    vec![(path.to_string(), Path::new(&rocq_path))]
                }
                TopLevelItem::Module { name, body } => {
                    let mut nested_module_path = module_path.to_vec();
                    nested_module_path.push(name.clone());
                    body.function_table_entries(&nested_module_path)
                }
                _ => vec![],
            })
            .collect()
    }

    fn function_table_to_rocq(&self) -> Rc<rocq::TopLevelItem> {
        let entries = self
            .function_table_entries(&[])
            .into_iter()
            .map(|(rust_path, rocq_path)| {
                Rc::new(rocq::Expression::Tuple(vec![
                    Rc::new(rocq::Expression::String(rust_path)),
                    Rc::new(rocq::Expression::Variable {
                        ident: rocq_path,
                        no_implicit: false,
                    }),
                ]))
            })
            .collect();
        let entry_type = rocq::Expression::multiply(
            rocq::Expression::just_name("string"),
            rocq::Expression::just_name("PolymorphicFunction.t"),
        );

        Rc::new(rocq::TopLevelItem::Definition(rocq::Definition::new(
            "function_table",
            Rc::new(rocq::DefinitionKind::Alias {
                args: vec![],
                ty: Some(rocq::Expression::just_name("list").apply(entry_type)),
                body: Rc::new(rocq::Expression::List { exprs: entries }),
            }),
        )))
    }

    fn trait_method_table_entries(&self, module_path: &[String]) -> Vec<Rc<rocq::Expression>> {
        self.0
            .iter()
            .flat_map(|entry| match entry.item.as_ref() {
                TopLevelItem::TraitImpl {
                    generic_consts,
                    generic_tys,
                    predicates,
                    self_ty,
                    of_trait,
                    trait_const_params,
                    trait_ty_params,
                    items,
                } if generic_consts.is_empty()
                    && generic_tys.is_empty()
                    && predicates.is_empty()
                    && trait_const_params.is_empty() =>
                {
                    let module_name = trait_impl_module_name(
                        predicates,
                        self_ty,
                        of_trait,
                        trait_const_params,
                        trait_ty_params,
                    );

                    items
                        .iter()
                        .filter_map(|item| {
                            let kind: Option<&ImplItemKind> = item.kind.as_ref().into();
                            let kind = kind?;

                            match kind {
                                ImplItemKind::Const { .. } | ImplItemKind::Definition { .. } => {
                                    let mut rocq_path = module_path.to_vec();
                                    rocq_path.push(module_name.clone());
                                    rocq_path.push(kind.to_definition_name(item.name.to_string()));

                                    Some(Rc::new(rocq::Expression::Tuple(vec![
                                        Rc::new(rocq::Expression::String(of_trait.to_string())),
                                        Rc::new(rocq::Expression::List {
                                            exprs: trait_ty_params
                                                .iter()
                                                .map(|ty| ty.to_rocq())
                                                .collect(),
                                        }),
                                        self_ty.to_rocq(),
                                        Rc::new(rocq::Expression::String(item.name.to_string())),
                                        Rc::new(rocq::Expression::Variable {
                                            ident: Path::new(&rocq_path),
                                            no_implicit: false,
                                        }),
                                    ])))
                                }
                                ImplItemKind::Type { .. } => None,
                            }
                        })
                        .collect()
                }
                TopLevelItem::Module { name, body } => {
                    let mut nested_module_path = module_path.to_vec();
                    nested_module_path.push(name.clone());
                    body.trait_method_table_entries(&nested_module_path)
                }
                _ => vec![],
            })
            .collect()
    }

    fn trait_method_table_to_rocq(&self) -> Rc<rocq::TopLevelItem> {
        Rc::new(rocq::TopLevelItem::Definition(rocq::Definition::new(
            "trait_method_table",
            Rc::new(rocq::DefinitionKind::Alias {
                args: vec![],
                ty: Some(rocq::Expression::just_name(
                    "list (string * list Ty.t * Ty.t * string * PolymorphicFunction.t)",
                )),
                body: Rc::new(rocq::Expression::List {
                    exprs: self.trait_method_table_entries(&[]),
                }),
            }),
        )))
    }

    fn runtime_to_rocq(&self) -> Rc<rocq::TopLevel> {
        rocq::TopLevel::new(&[
            self.function_table_to_rocq(),
            Rc::new(rocq::TopLevelItem::Line),
            self.trait_method_table_to_rocq(),
        ])
    }

    fn to_rocq(&self, include_runtime: bool) -> Rc<rocq::TopLevel> {
        let mut items = itertools::Itertools::intersperse(
            self.0.iter().map(|item| item.item.to_rocq()),
            vec![Rc::new(rocq::TopLevelItem::Line)],
        )
        .flatten()
        .collect_vec();

        if include_runtime {
            items.push(Rc::new(rocq::TopLevelItem::Line));
            items.push(self.function_table_to_rocq());
            items.push(Rc::new(rocq::TopLevelItem::Line));
            items.push(self.trait_method_table_to_rocq());
        }

        rocq::TopLevel::new(&items)
    }

    pub fn to_pretty(&self, width: usize, include_runtime: bool) -> String {
        let mut w = Vec::new();
        self.to_rocq(include_runtime)
            .to_doc(&pretty::Arena::new())
            .render(width, &mut w)
            .unwrap();
        format!("{}{}\n", HEADER, String::from_utf8(w).unwrap())
    }

    pub fn runtime_to_pretty(&self, width: usize) -> String {
        let mut w = Vec::new();
        self.runtime_to_rocq()
            .to_doc(&pretty::Arena::new())
            .render(width, &mut w)
            .unwrap();
        format!("{}\n", String::from_utf8(w).unwrap())
    }

    pub fn to_json(&self) -> String {
        serde_json::to_string_pretty(self).unwrap()
    }
}
