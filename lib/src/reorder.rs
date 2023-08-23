/// This module implements the reordering of the definitions in the output
/// and also the `--generate-reorder` option. The order is read from
/// the configuration file and applied before the compilation  with
/// the compile_* functions, and happens at top_level.rs module
use crate::configuration::*;
use crate::env::*;
use itertools::Itertools;
use rustc_hir::{HirId, Impl, ImplItemRef, Item, ItemId, ItemKind, Node, QPath, Ty, TyKind};
use rustc_middle::ty::TyCtxt;
use std::string::ToString;

pub(crate) trait GetHirId {
    fn hir_id(&self) -> HirId;
}

impl GetHirId for ItemId {
    fn hir_id(&self) -> HirId {
        self.hir_id()
    }
}

impl GetHirId for ImplItemRef {
    fn hir_id(&self) -> HirId {
        self.id.hir_id()
    }
}

fn get_name(tcx: &TyCtxt, a_id: HirId) -> String {
    let a_name = tcx.hir().ident(a_id).as_str().to_string();
    if a_name.is_empty() {
        let a_node_opt = tcx.hir().find(a_id);
        match a_node_opt {
            Some(node) => get_impl_type_opt(node).unwrap_or(a_name),
            None => a_name,
        }
    } else {
        a_name
    }
}

/// Reorder a vector of definitions to match the contents of the
/// configuration file. The reordering happens before the compilation
/// i.e. before calling the `compile_...` functions, in the
/// HIR.
#[allow(clippy::ptr_arg)] // Disable warning over &mut Vec<...>, using &mut[...] wont compile
pub(crate) fn reorder_definitions_inplace(
    tcx: &TyCtxt,
    env: &mut Env,
    definitions: &mut Vec<impl GetHirId>,
) {
    // If we have only one element we still want it to show up
    // in the output of `--generate-reorder`, even if there
    // is no sorting going on
    if definitions.is_empty() {
        return;
    }

    if env.configuration.debug_reorder {
        eprintln!(
            "{}",
            definitions
                .iter()
		.enumerate()
                .map(|(i, def)| format!("\x1b[0;31mreorder before: {i:6} {}/{} {}\x1b[0m", env.file, get_context_name(tcx, &def.hir_id()), get_name(tcx, def.hir_id())))
                .collect::<Vec<String>>()
                .join("\n")
        );
    }

    let definitions_ids: Vec<HirId> = definitions.iter().map(|def| def.hir_id()).collect();

    // @TODO 
    // compute the origional position

    for def_id in &definitions_ids {
        let def_name = get_name(tcx, *def_id);
        let context = get_context_name(tcx, &def_id);
 	let pos = definitions_ids.iter().position(|elm| elm == def_id).unwrap();

        match config_get_reorder(env, &context, &def_name) {
	    Some(config_identifier) => {
		let config_id_pos = definitions_ids.iter()
		    .map(|hir_id| get_name(tcx, *hir_id))
		    .position(|elm| elm == config_identifier);
		if config_id_pos.is_none() {
		    continue;
		}
		let config_id_pos = config_id_pos.unwrap();
		let def = definitions.remove(pos);
		definitions.insert(config_id_pos, def);
	    },
	    None => continue,
	}
    };

    if env.configuration.debug_reorder {
        eprintln!(
            "{}",
            definitions
                .iter()
                .map(|def| {
		    let id = def.hir_id();
		    let pos = definitions_ids.iter().position(|x| *x == id).unwrap_or(0);
		    format!("\x1b[0;32mreorder after:  {pos:6} {}/{} {}\x1b[0m", env.file, get_context_name(tcx, &def.hir_id()), get_name(tcx, def.hir_id()))
		})
                .collect::<Vec<String>>()
                .join("\n")
        );
    }

    let identifiers = definitions
        .iter()
        .filter_map(|def| {
            let name = get_name(tcx, def.hir_id());
            if !name.is_empty() && name != "test" && name != "std" {
                Some(name)
            } else {
                None
            }
        })
        .unique()
        .collect::<Vec<String>>();

    let context = get_context_name(tcx, &definitions[0].hir_id());
    env.reorder_map.insert(context, identifiers);
}

/// Extract the type name for a node if is a trait
/// implementation, otherwise returns None
fn get_impl_type_opt(node: Node) -> Option<String> {
    match node {
        Node::Item(Item {
            kind:
                ItemKind::Impl(Impl {
                    self_ty:
                        Ty {
                            kind: TyKind::Path(QPath::Resolved(_, rustc_hir::Path { segments, .. })),
                            ..
                        },
                    of_trait,
                    ..
                }),
            ..
        }) => {
            let ty_name: String = segments.iter().map(|x| x.ident.as_str()).join("::");
            match of_trait {
                Some(rustc_hir::TraitRef { path, .. }) => {
                    let trait_name = path.segments.iter().map(|x| x.ident.as_str()).join("::");
                    Some(format!("Impl_{trait_name}_for_{ty_name}"))
                }
                None => Some(format!("Impl_{ty_name}")),
            }
        }
        _ => None,
    }
}

/// Given a HirId returns the name of the context/scope
/// where such item is. Example top_level::inner_mod::other_mod
pub(crate) fn get_context_name(tcx: &TyCtxt, id: &HirId) -> String {
    let name = tcx
        .hir()
        .parent_iter(*id)
        .filter_map(|(_, parent)| match get_impl_type_opt(parent) {
            Some(typ) => Some(typ),
            None => parent.ident().map(|ident| ident.as_str().to_string()),
        })
        .collect::<Vec<String>>()
        .into_iter()
        .rev()
        .collect::<Vec<String>>()
        .join("::");
    if name.is_empty() {
        "top_level".to_string()
    } else {
        format!("top_level::{}", name)
    }
}
