use crate::configuration::*;
use crate::env::*;
use crate::expression::*;
use crate::header::*;
use crate::path::*;
use crate::render::*;
use crate::ty::*;
use rustc_ast::ast::{AttrArgs, AttrKind};
use rustc_hir::{
    GenericBound, GenericParamKind, Impl, ImplItemKind, Item, ItemKind, PatKind, QPath, TraitFn,
    TraitItemKind, Ty, TyKind, VariantData,
};
use rustc_middle::ty::TyCtxt;
use rustc_span::symbol::sym;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::iter::repeat;
use std::string::ToString;

pub(crate) struct TopLevelOptions {
    pub(crate) configuration_file: String,
    pub(crate) filename: String,
    pub(crate) axiomatize: bool,
    pub(crate) generate_reorder: bool,
}

/// Trait for getting a name of an AST node. Used
/// for ordering the nodes based on a list of names
trait ToName {
    /// We return [String] instead of [&String] because
    /// some AST nodes need their names to be constructed.
    fn to_name(&self) -> String;
}

#[derive(Debug)]
enum TraitItem {
    Definition {
        ty_params: Vec<String>,
        where_predicates: Vec<WherePredicate>,
        ty: Box<CoqType>,
    },
    DefinitionWithDefault {
        ty_params: Vec<String>,
        where_predicates: Vec<WherePredicate>,
        args: Vec<(String, Box<CoqType>)>,
        ret_ty: Box<CoqType>,
        body: Box<Expr>,
    },
    Type(Vec<Path>),
}

#[derive(Debug)]
enum ImplItem {
    Const {
        body: Box<Expr>,
        is_dead_code: bool,
    },
    Definition {
        ty_params: Vec<String>,
        where_predicates: Vec<WherePredicate>,
        args: Vec<(String, Box<CoqType>)>,
        ret_ty: Box<CoqType>,
        body: Box<Expr>,
        is_method: bool,
        is_dead_code: bool,
        is_axiomatized: bool,
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
        is_axiomatized: bool,
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
        items: Vec<(String, ImplItem)>,
    },
    Trait {
        name: String,
        ty_params: Vec<(String, Option<Box<CoqType>>)>,
        body: Vec<(String, TraitItem)>,
    },
    TraitImpl {
        generic_tys: Vec<String>,
        ty_params: Vec<Box<TraitImplTyParam>>,
        self_ty: Box<CoqType>,
        of_trait: Path,
        items: Vec<(String, ImplItem)>,
        trait_non_default_items: Vec<String>,
    },
    Error(String),
}

impl ToName for TopLevelItem {
    fn to_name(&self) -> String {
        match self {
            TopLevelItem::Definition { name, .. } => name.clone(),
            TopLevelItem::Const { name, .. } => name.clone(),
            TopLevelItem::TypeAlias { name, .. } => name.clone(),
            TopLevelItem::TypeEnum { name, .. } => name.clone(),
            TopLevelItem::TypeStructStruct { name, .. } => name.clone(),
            TopLevelItem::TypeStructTuple { name, .. } => name.clone(),
            TopLevelItem::TypeStructUnit { name, .. } => name.clone(),
            TopLevelItem::Module { name, .. } => name.clone(),
            TopLevelItem::Impl {
                self_ty, counter, ..
            } => format!(
                "Impl_{}{}",
                self_ty.to_name(),
                if *counter != 1 {
                    format!("_{counter}")
                } else {
                    "".to_string()
                }
            ),
            TopLevelItem::Trait { name, .. } => name.to_string(),
            TopLevelItem::TraitImpl {
                of_trait, self_ty, ..
            } => format!("Impl_{}_for_{}", of_trait.to_name(), self_ty.to_name()),
            TopLevelItem::Error(msg) => msg.clone(),
        }
    }
}

/// The actual value of the type parameter of the trait implementation
#[derive(Clone, Debug)]
enum TraitImplTyParam {
    /// the value of the parameter that has no default
    JustValue { name: String, ty: Box<CoqType> },
    /// the value that replaces the default value of the parameter
    ValWithDef { name: String, ty: Box<CoqType> },
    /// means the default value of the type parameter is used
    JustDefault { name: String },
}

impl ToName for (String, ImplItem) {
    fn to_name(&self) -> String {
        self.0.clone()
    }
}

#[derive(Debug)]
pub struct TopLevel(Vec<TopLevelItem>);

struct FnSigAndBody {
    args: Vec<(String, Box<CoqType>)>,
    ret_ty: Box<CoqType>,
    body: Box<Expr>,
}

fn compile_fn_sig_and_body_id(
    env: &mut Env,
    fn_sig: &rustc_hir::FnSig<'_>,
    body_id: &rustc_hir::BodyId,
) -> FnSigAndBody {
    let body = env.tcx.hir().body(*body_id);
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
                (name, compile_type(env, ty))
            })
            .collect(),
        ret_ty: match fn_sig.decl.output {
            rustc_hir::FnRetTy::DefaultReturn(_) => CoqType::unit(),
            rustc_hir::FnRetTy::Return(ty) => compile_type(env, ty),
        },
        body: Box::new(compile_expr(env, expr)),
    }
}

/// Check if the function body is actually the main test function calling to all
/// tests in the file. If so, we do not want to compile it.
fn check_if_is_test_main_function(tcx: &TyCtxt, body_id: &rustc_hir::BodyId) -> bool {
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

            let value = tcx.hir().body(*body_id).value;
            vec![TopLevelItem::Const {
                name,
                ty: compile_type(env, ty),
                value: Box::new(compile_expr(env, value)),
            }]
        }
        ItemKind::Fn(fn_sig, generics, body_id) => {
            if check_if_is_test_main_function(tcx, body_id) {
                return vec![];
            }
            let if_marked_as_dead_code = check_dead_code_lint_in_attributes(tcx, item);
            let FnSigAndBody { args, ret_ty, body } =
                compile_fn_sig_and_body_id(env, fn_sig, body_id);
            vec![TopLevelItem::Definition {
                name,
                ty_params: generics
                    .params
                    .iter()
                    .filter_map(|param| match param.kind {
                        rustc_hir::GenericParamKind::Type { .. } => {
                            Some(to_valid_coq_name(param.name.ident().to_string()))
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
                                            compile_path(env, path),
                                            compile_path_ty_params(env, path),
                                        ))
                                    }
                                    _ => None,
                                });
                            names_and_ty_params
                                .map(|(name, ty_params)| WherePredicate {
                                    name,
                                    ty_params,
                                    ty: compile_type(env, predicate.bounded_ty),
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
                is_axiomatized: env.axiomatize,
            }]
        }
        ItemKind::Macro(_, _) => vec![],
        ItemKind::Mod(module) => {
            let if_marked_as_dead_code = check_dead_code_lint_in_attributes(tcx, item);
            env.push_context(&name);
            let mut items = module
                .item_ids
                .iter()
                .flat_map(|item_id| {
                    let item = tcx.hir().item(*item_id);
                    compile_top_level_item(tcx, env, item)
                })
                .collect();
            reorder_definitions_inplace(env, &mut items);
            env.pop_context();
            // We remove empty modules in the translation
            if items.is_empty() {
                return vec![];
            }
            vec![TopLevelItem::Module {
                name,
                body: TopLevel(items),
                is_dead_code: if_marked_as_dead_code,
            }]
        }
        ItemKind::ForeignMod { .. } => {
            vec![TopLevelItem::Error("ForeignMod".to_string())]
        }
        ItemKind::GlobalAsm(_) => vec![TopLevelItem::Error("GlobalAsm".to_string())],
        ItemKind::TyAlias(ty, _) => vec![TopLevelItem::TypeAlias {
            name,
            ty: compile_type(env, ty),
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
            let if_marked_as_dead_code = check_dead_code_lint_in_attributes(tcx, item);
            let ty_params = generics
                .params
                .iter()
                .filter_map(|param| match param.kind {
                    rustc_hir::GenericParamKind::Type { .. } => {
                        Some(param.name.ident().to_string())
                    }
                    rustc_hir::GenericParamKind::Const { .. } => {
                        env.tcx
                            .sess
                            .struct_span_warn(param.span, "Constant parameters are not supported.")
                            .note("It should be supported in future versions.")
                            .emit();
                        None
                    }
                    rustc_hir::GenericParamKind::Lifetime { .. } => None,
                })
                .collect();

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
                        is_dead_code: if_marked_as_dead_code,
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
        ItemKind::Trait(_, _, generics, _, items) => {
            vec![TopLevelItem::Trait {
                name,
                ty_params: generics
                    .params
                    .iter()
                    .map(|param| {
                        let default = match param.kind {
                            GenericParamKind::Type { default, .. } => {
                                default.map(|default| compile_type(env, default))
                            }
                            _ => {
                                env.tcx
                                    .sess
                                    .struct_span_warn(
                                        param.span,
                                        "Only type parameters are currently supported.",
                                    )
                                    .note("It should be supported in future versions.")
                                    .emit();
                                None
                            }
                        };
                        let name = to_valid_coq_name(param.name.ident().to_string());
                        (name, default)
                    })
                    .collect(),
                body: items
                    .iter()
                    .map(|item| {
                        let item = tcx.hir().trait_item(item.id);
                        let ty_params = item
                            .generics
                            .params
                            .iter()
                            .filter_map(|param| match param.kind {
                                rustc_hir::GenericParamKind::Type { .. } => {
                                    Some(to_valid_coq_name(param.name.ident().to_string()))
                                }
                                _ => None,
                            })
                            .collect();
                        let where_predicates = item
                            .generics
                            .predicates
                            .iter()
                            .flat_map(|predicate| match predicate {
                                rustc_hir::WherePredicate::BoundPredicate(predicate) => {
                                    let names_and_ty_params =
                                        predicate.bounds.iter().filter_map(|bound| match bound {
                                            rustc_hir::GenericBound::Trait(ref trait_ref, _) => {
                                                let path = trait_ref.trait_ref.path;
                                                Some((
                                                    compile_path(env, path),
                                                    compile_path_ty_params(env, path),
                                                ))
                                            }
                                            GenericBound::LangItemTrait { .. } => {
                                                env.tcx
                                                    .sess
                                                    .struct_span_warn(
                                                        predicate.span,
                                                        "LangItem trait bounds are not supported yet.",
                                                    )
                                                    .note("It will change in the future.")
                                                    .emit();
                                                None
                                            },
                                            GenericBound::Outlives { .. } => None,
                                        });
                                    names_and_ty_params
                                        .map(|(name, ty_params)| WherePredicate {
                                            name,
                                            ty_params,
                                            ty: compile_type(env, predicate.bounded_ty),
                                        })
                                        .collect()
                                }
                                _ => vec![],
                            })
                            .collect();
                        let body = match &item.kind {
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
                                    let FnSigAndBody { args, ret_ty, body } =
                                        compile_fn_sig_and_body_id(env, fn_sig, body_id);
                                    TraitItem::DefinitionWithDefault { ty_params, where_predicates, args, ret_ty, body }
                                }
                            },
                            TraitItemKind::Type(generic_bounds, ..) => {
                                let generic_bounds = generic_bounds
                                    .iter()
                                    .filter_map(|generic_bound| match generic_bound {
                                        GenericBound::Trait(ptraitref, _) => {
                                            Some(compile_path(env, ptraitref.trait_ref.path))
                                        }
                                        GenericBound::LangItemTrait { .. } => {
                                            env.tcx
                                                .sess
                                                .struct_span_warn(
                                                    generic_bound.span(),
                                                    "LangItem trait bounds are not supported yet.",
                                                )
                                                .note("It will change in the future.")
                                                .emit();
                                            None
                                        },
                                        GenericBound::Outlives { .. } => None,
                                    })
                                    .collect();
                                TraitItem::Type(generic_bounds)
                            }
                        };
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
            let if_marked_as_dead_code = check_dead_code_lint_in_attributes(tcx, item);
            let generic_tys: Vec<String> = generics
                .params
                .iter()
                .filter(|param| matches!(param.kind, rustc_hir::GenericParamKind::Type { .. }))
                .map(|param| param.name.ident().to_string())
                .collect();
            let self_ty = compile_type(env, self_ty);
            let entry = env.impl_counter.entry(*self_ty.clone());
            let counter = *entry.and_modify(|counter| *counter += 1).or_insert(1);
            let impl_name = format!(
                "Impl_{}{}",
                self_ty.to_name(),
                if counter != 1 {
                    format!("_{counter}")
                } else {
                    "".to_string()
                }
            );
            env.push_context(&impl_name);
            let mut items = items
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
                                body: Box::new(compile_expr(env, expr)),
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
                            let ty_params = item
                                .generics
                                .params
                                .iter()
                                .filter_map(|param| match param.kind {
                                    rustc_hir::GenericParamKind::Type { .. } => {
                                        Some(param.name.ident().to_string())
                                    }
                                    _ => None,
                                })
                                .collect();
                            let where_predicates = item
                                .generics
                                .predicates
                                .iter()
                                .flat_map(|predicate| match predicate {
                                    rustc_hir::WherePredicate::BoundPredicate(predicate) => {
                                        let names_and_ty_params =
                                            predicate.bounds.iter().filter_map(|bound| match bound {
                                                rustc_hir::GenericBound::Trait(ref trait_ref, _) => {
                                                    let path = trait_ref.trait_ref.path;
                                                    Some((
                                                        compile_path(env, path),
                                                        compile_path_ty_params(env, path),
                                                    ))
                                                }
                                                _ => {
                                                    env.tcx
                                                        .sess
                                                        .struct_span_warn(
                                                            predicate.span,
                                                            "Only trait bounds are currently supported.",
                                                        )
                                                        .note("It may change in future versions.")
                                                        .emit();
                                                    None
                                                },
                                            });
                                        names_and_ty_params
                                            .map(|(name, ty_params)| WherePredicate {
                                                name,
                                                ty_params,
                                                ty: compile_type(env, predicate.bounded_ty),
                                            })
                                            .collect()
                                    }
                                    _ => vec![],
                                })
                                .collect();
                            let arg_tys = inputs.iter().map(|ty| compile_type(env, ty));
                            let ret_ty = compile_fn_ret_ty(env, output);
                            let expr = tcx.hir().body(*body_id).value;
                            ImplItem::Definition {
                                ty_params,
                                where_predicates,
                                args: arg_names.zip(arg_tys).collect(),
                                ret_ty,
                                body: Box::new(compile_expr(env, expr)),
                                is_method,
                                is_dead_code: if_marked_as_dead_code,
                                is_axiomatized: env.axiomatize,
                            }
                        }
                        ImplItemKind::Type(ty) => ImplItem::Type {
                            ty: compile_type(env, ty),
                        },
                    };
                    (item.ident.name.to_string(), value)
                })
                .collect();
            reorder_definitions_inplace(env, &mut items);
            env.pop_context();
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

                    // Get the list of type parameters default status (true if it has a default)
                    let mut type_params_name_and_default_status: Vec<(String, bool)> = generics
                        .params
                        .iter()
                        .filter_map(|param| match param.kind {
                            rustc_middle::ty::GenericParamDefKind::Type { has_default, .. } => {
                                Some((param.name.to_string(), has_default))
                            }
                            _ => None,
                        })
                        .collect();
                    // The first type parameter is always the Self type, that we do not consider as
                    // part of the list of type parameters.
                    type_params_name_and_default_status.remove(0);

                    let ty_params = compile_path_ty_params(env, trait_ref.path);

                    vec![TopLevelItem::TraitImpl {
                        generic_tys,
                        ty_params: ty_params
                            .into_iter()
                            .map(Some)
                            .chain(repeat(None))
                            .zip(type_params_name_and_default_status)
                            .map(|(ty, (name, has_default))| {
                                Box::new(match ty {
                                    Some(ty) => {
                                        if has_default {
                                            TraitImplTyParam::ValWithDef { name, ty }
                                        } else {
                                            TraitImplTyParam::JustValue { name, ty }
                                        }
                                    }
                                    None => TraitImplTyParam::JustDefault { name },
                                })
                            })
                            .collect(),
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

#[allow(clippy::ptr_arg)] // Disable warning over &mut Vec<...>, using &mut[...] wont compile
fn reorder_definitions_inplace(env: &mut Env, definitions: &mut Vec<impl ToName>) {
    let context = &env.context;

    // The context here is the path of the file name with / so we need
    // to escape it
    let order = config_get_reorder(env);
    definitions.sort_by(|a, b| {
        let a_name = a.to_name();
        let b_name = b.to_name();
        let a_position = order.iter().position(|elm| *elm == a_name);
        if a_position.is_none() {
            return Ordering::Equal;
        }

        let b_position = order.iter().position(|elm| *elm == b_name);
        if b_position.is_none() {
            return Ordering::Equal;
        };

        a_position.cmp(&b_position)
    });

    let identifiers: Vec<String> = definitions.iter().map(ToName::to_name).collect();
    env.reorder_map.insert(context.to_string(), identifiers);
}

fn compile_top_level(tcx: &TyCtxt, opts: TopLevelOptions) -> TopLevel {
    let mut env = Env {
        impl_counter: HashMap::new(),
        tcx: *tcx,
        axiomatize: opts.axiomatize,
        file: opts.filename,
        context: "top_level".to_string(),
        reorder_map: HashMap::new(),
        configuration: get_configuration(&opts.configuration_file),
    };

    let mut results: Vec<TopLevelItem> = tcx
        .hir()
        .items()
        .flat_map(|item_id| {
            let item = tcx.hir().item(item_id);
            compile_top_level_item(tcx, &mut env, item)
        })
        .collect();

    reorder_definitions_inplace(&mut env, &mut results);
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

/// provides the instance of the Struct.Trait typeclass
/// for definitions of functions and constants
/// which types utilize the M monad constructor
fn monadic_typeclass_parameter<'a>() -> Doc<'a> {
    // TODO: check whether the name of the parameter is necessary
    text("`{H : State.Trait}")
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

// We can not have more than 7 arguments for the function,
// so we put all the arguments into one struct
struct ArgumentsForFnToDoc<'a> {
    name: &'a String,
    ty_params: Option<&'a Vec<String>>,
    where_predicates: Option<&'a Vec<WherePredicate>>,
    args: &'a Vec<(String, Box<CoqType>)>,
    ret_ty: &'a CoqType,
    body: &'a Expr,
    is_dead_code: bool,
    is_axiomatized: bool,
    extra_data: Option<&'a TopLevelItem>,
}

fn fn_to_doc(strct_args: ArgumentsForFnToDoc) -> Doc {
    let types_for_f = types_for_f(strct_args.extra_data);

    group([
        if strct_args.is_dead_code {
            concat([
                text("(* #[allow(dead_code)] - function was ignored by the compiler *)"),
                hardline(),
            ])
        } else {
            nil()
        },
        // Printing instance of DoubleColon Class for [f]
        // (fmt;  #[derive(Debug)]; Struct std::fmt::Formatter)
        if (strct_args.name == "fmt") && is_extra(strct_args.extra_data) {
            group([
                nest([
                    text("Parameter "),
                    strct_args.body.parameter_name_for_fmt(),
                    text(" : "),
                    // get type of argument named f
                    // (see: https://doc.rust-lang.org/std/fmt/struct.Formatter.html)
                    concat(strct_args.args.iter().map(|(name, ty)| {
                        if name == "f" {
                            ty.to_doc_tuning(false)
                        } else {
                            nil()
                        }
                    })),
                    text(" -> "),
                    types_for_f,
                    strct_args.ret_ty.to_doc(false),
                    text("."),
                ]),
                hardline(),
                hardline(),
                nest([
                    text("Global Instance Deb_"),
                    strct_args.body.parameter_name_for_fmt(),
                    text(" : "),
                    text("Notation.DoubleColon"),
                    line(),
                    concat(strct_args.args.iter().map(|(name, ty)| {
                        if name == "f" {
                            ty.to_doc_tuning(false)
                        } else {
                            nil()
                        }
                    })),
                    text(" \""),
                    strct_args.body.parameter_name_for_fmt(),
                    text("\""),
                    text(" := "),
                    text("{"),
                    line(),
                    nest([
                        text("Notation.double_colon := "),
                        strct_args.body.parameter_name_for_fmt(),
                        text(";"),
                        line(),
                    ]),
                    text("}."),
                ]),
                hardline(),
                hardline(),
            ])
        } else {
            nil()
        },
        if strct_args.is_axiomatized {
            nest([nest([
                nest([
                    text("Parameter"),
                    line(),
                    text(strct_args.name),
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
                match strct_args.ty_params {
                    None => nil(),
                    Some(ty_params) => {
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
                    }
                },
                // where predicates types
                match strct_args.where_predicates {
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
                // argument types
                concat(
                    strct_args
                        .args
                        .iter()
                        .map(|(_, ty)| concat([ty.to_doc(false), text(" ->"), line()])),
                ),
                // return type
                strct_args.ret_ty.to_doc(false),
                text("."),
            ])])
        } else {
            nest([
                nest([
                    nest([text("Definition"), line(), text(strct_args.name)]),
                    line(),
                    monadic_typeclass_parameter(),
                    match strct_args.ty_params {
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
                    match strct_args.where_predicates {
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
                    concat(strct_args.args.iter().map(|(name, ty)| {
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
                        strct_args.ret_ty.to_doc(false),
                        text(" :="),
                    ]),
                ]),
                line(),
                strct_args.body.to_doc(false),
                text("."),
            ])
        },
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
            ty_params,
            where_predicates,
            args,
            ret_ty,
            body,
            is_method,
            is_dead_code,
            is_axiomatized,
        } => {
            let (body, _fresh_vars) = mt_expression(FreshVars::new(), *body);
            ImplItem::Definition {
                ty_params,
                where_predicates,
                args,
                ret_ty: CoqType::monad(mt_ty(ret_ty)),
                body: Box::new(Expr::Block(Box::new(body))),
                is_method,
                is_dead_code,
                is_axiomatized,
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
            args,
            ret_ty,
            body,
        } => {
            let (body, _fresh_vars) = mt_expression(FreshVars::new(), *body);
            TraitItem::DefinitionWithDefault {
                ty_params,
                where_predicates,
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
            is_axiomatized,
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
                is_axiomatized,
            }
        }
        TopLevelItem::TypeAlias { name, ty } => TopLevelItem::TypeAlias { name, ty },
        TopLevelItem::TypeEnum { name, variants } => TopLevelItem::TypeEnum { name, variants },
        TopLevelItem::TypeStructStruct {
            name,
            ty_params,
            fields,
            is_dead_code,
        } => TopLevelItem::TypeStructStruct {
            name,
            ty_params,
            fields,
            is_dead_code,
        },
        TopLevelItem::TypeStructTuple {
            name,
            ty_params,
            fields,
        } => TopLevelItem::TypeStructTuple {
            name,
            ty_params,
            fields,
        },
        TopLevelItem::TypeStructUnit { name, ty_params } => {
            TopLevelItem::TypeStructUnit { name, ty_params }
        }
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

    fn to_doc<'a>(&'a self, name: &'a String, extra_data: &Option<&'a TopLevelItem>) -> Doc<'a> {
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
                ty_params,
                where_predicates,
                args,
                ret_ty,
                body,
                is_method,
                is_dead_code,
                is_axiomatized,
            } => {
                let afftd = ArgumentsForFnToDoc {
                    name,
                    ty_params: Some(ty_params),
                    where_predicates: Some(where_predicates),
                    args,
                    ret_ty,
                    body,
                    is_dead_code: *is_dead_code,
                    is_axiomatized: *is_axiomatized,
                    extra_data: *extra_data,
                };

                concat([
                    fn_to_doc(afftd),
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
                ])
            }
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
    /// turns the predicate into its representation as constraint
    fn to_doc(&self) -> Doc {
        nest([
            text("`{"),
            self.name.to_doc(),
            text(".Trait"),
            line(),
            concat(
                self.ty_params
                    .iter()
                    .map(|param| concat([param.to_doc(true), line()])),
            ),
            self.ty.to_doc(true),
            text("}"),
        ])
    }
}

impl TopLevelItem {
    fn to_doc<'a>(&'a self, extra_data: &Option<&'a TopLevelItem>) -> Doc {
        match self {
            TopLevelItem::Const { name, ty, value } => nest([
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
            TopLevelItem::Definition {
                name,
                ty_params,
                where_predicates,
                args,
                ret_ty,
                body,
                is_dead_code,
                is_axiomatized,
            } => {
                let afftd = ArgumentsForFnToDoc {
                    name,
                    ty_params: Some(ty_params),
                    where_predicates: Some(where_predicates),
                    args,
                    ret_ty,
                    body,
                    is_dead_code: *is_dead_code,
                    is_axiomatized: *is_axiomatized,
                    extra_data: *extra_data,
                };

                fn_to_doc(afftd)
            }
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
                    add_section_if_necessary(
                        name,
                        &ty_params.iter().collect(),
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
                    ),
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
                    add_section_if_necessary(
                        name,
                        &ty_params.iter().collect(),
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
                    ),
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
                    add_section_if_necessary(
                        name,
                        &ty_params.iter().collect(),
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
                    ),
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
                        concat(items.iter().map(|(name, item)| {
                            concat([hardline(), hardline(), item.to_doc(name, extra_data)])
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
            } => module(
                name,
                group([
                    locally_unset_primitive_projections(
                        body.is_empty(),
                        group([
                            nest([
                                nest([
                                    text("Class Trait"),
                                    line(),
                                    nest([
                                        text("("),
                                        text("Self"),
                                        line(),
                                        text(":"),
                                        line(),
                                        text("Set"),
                                        text(")"),
                                        if ty_params.is_empty() {
                                            nil()
                                        } else {
                                            concat([
                                                line(),
                                                nest([
                                                    text("{"),
                                                    concat(ty_params.iter().map(
                                                        |(ty, default)| {
                                                            match default {
                                                                // @TODO: implement translation of type parameters with default
                                                                Some(_default) => concat([
                                                                    text("(* TODO *)"),
                                                                    line(),
                                                                    text(ty),
                                                                    line(),
                                                                ]),
                                                                None => concat([text(ty), line()]),
                                                            }
                                                        },
                                                    )),
                                                    text(":"),
                                                    line(),
                                                    text("Set"),
                                                    text("}"),
                                                ]),
                                            ])
                                        },
                                    ]),
                                    intersperse(
                                        body.iter().map(|(item_name, item)| match item {
                                            TraitItem::Definition { .. } => nil(),
                                            TraitItem::DefinitionWithDefault { .. } => nil(),
                                            TraitItem::Type(bounds) => concat([
                                                line(),
                                                nest([
                                                    text("{"),
                                                    text(item_name),
                                                    text(" : "),
                                                    text("Set"),
                                                    text("}"),
                                                ]),
                                                concat(bounds.iter().map(|x| {
                                                    concat([
                                                        line(),
                                                        nest([
                                                            text("`{"),
                                                            x.to_doc(),
                                                            text(".Trait"),
                                                            line(),
                                                            text(item_name),
                                                            text("}"),
                                                        ]),
                                                    ])
                                                })),
                                            ]),
                                        }),
                                        [nil()],
                                    ),
                                    text(" :"),
                                    line(),
                                    text("Set := {"),
                                ]),
                                intersperse(
                                    body.iter().map(|(name, item)| match item {
                                        TraitItem::Definition {
                                            ty_params,
                                            where_predicates,
                                            ty,
                                        } => group([
                                            hardline(),
                                            nest([
                                                text(name),
                                                line(),
                                                monadic_typeclass_parameter(),
                                                line(),
                                                if ty_params.is_empty() {
                                                    nil()
                                                } else {
                                                    concat([
                                                        group([
                                                            text("{"),
                                                            intersperse(ty_params, [line()]),
                                                            text(": Set}"),
                                                        ]),
                                                        line(),
                                                    ])
                                                },
                                                intersperse(
                                                    [
                                                        where_predicates
                                                            .iter()
                                                            .map(|predicate| predicate.to_doc())
                                                            .collect::<Vec<Doc>>(),
                                                        vec![nil()],
                                                    ]
                                                    .concat(),
                                                    [line()],
                                                ),
                                                text(":"),
                                                line(),
                                                ty.to_doc(false),
                                                text(";"),
                                            ]),
                                        ]),
                                        TraitItem::DefinitionWithDefault { .. } => nil(),
                                        TraitItem::Type { .. } => group([
                                            hardline(),
                                            nest([
                                                text(name),
                                                line(),
                                                text(":="),
                                                line(),
                                                text(name),
                                                text(";"),
                                            ]),
                                        ]),
                                    }),
                                    [nil()],
                                ),
                            ]),
                            hardline(),
                            text("}."),
                        ]),
                    ),
                    concat(body.iter().map(|(name, item)| {
                        concat([
                            hardline(),
                            nest([
                                nest([
                                    text("Global Instance"),
                                    line(),
                                    text(format!("Method_{name}")),
                                    line(),
                                    monadic_typeclass_parameter(),
                                    line(),
                                    text("`(Trait)"),
                                ]),
                                line(),
                                match item {
                                    TraitItem::Definition { .. }
                                    | TraitItem::DefinitionWithDefault { .. } => nest([
                                        text(": Notation.Dot"),
                                        line(),
                                        text(format!("\"{name}\"")),
                                        line(),
                                        text(":= {"),
                                    ]),
                                    TraitItem::Type { .. } => nest([
                                        text(": Notation.DoubleColonType"),
                                        line(),
                                        text("Self"),
                                        line(),
                                        text(format!("\"{name}\"")),
                                        line(),
                                        text(":= {"),
                                    ]),
                                },
                            ]),
                            nest([
                                hardline(),
                                match item {
                                    TraitItem::Definition { .. } => nest([
                                        text("Notation.dot"),
                                        line(),
                                        text(":="),
                                        line(),
                                        text("@"),
                                        text(name),
                                        text(";"),
                                    ]),
                                    TraitItem::Type { .. } => nest([
                                        text("Notation.double_colon_type"),
                                        line(),
                                        text(":="),
                                        line(),
                                        text(name),
                                        text(";"),
                                    ]),
                                    TraitItem::DefinitionWithDefault {
                                        ty_params,
                                        where_predicates,
                                        args,
                                        ret_ty,
                                        body,
                                    } => nest([
                                        nest([
                                            text("Notation.dot"),
                                            if ty_params.is_empty() {
                                                nil()
                                            } else {
                                                concat([
                                                    group([
                                                        // change here if it doesn't work with '{}' brackets
                                                        text("{"),
                                                        intersperse(ty_params, [line()]),
                                                        text(": Set}"),
                                                    ]),
                                                    line(),
                                                ])
                                            },
                                            intersperse(
                                                [
                                                    where_predicates
                                                        .iter()
                                                        .map(|predicate| predicate.to_doc())
                                                        .collect::<Vec<Doc>>(),
                                                    vec![nil()],
                                                ]
                                                .concat(),
                                                [line()],
                                            ),
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
                                            })),
                                            text(" :="),
                                        ]),
                                        line(),
                                        text("("),
                                        body.to_doc(false),
                                        line(),
                                        nest([text(":"), line(), ret_ty.to_doc(false), text(")")]),
                                        text(";"),
                                    ]),
                                },
                            ]),
                            hardline(),
                            text("}."),
                        ])
                    })),
                ]),
            ),
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
                        concat(items.iter().map(|(name, item)| {
                            concat([item.to_doc(name, extra_data), hardline(), hardline()])
                        })),
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
                                                TraitImplTyParam::ValWithDef { name, ty } => {
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
                                                TraitImplTyParam::JustValue { name, ty } => nest([
                                                    text("("),
                                                    text(name),
                                                    line(),
                                                    text(":="),
                                                    line(),
                                                    ty.to_doc(false),
                                                    text(")"),
                                                ]),
                                                TraitImplTyParam::JustDefault { name } => nest([
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
