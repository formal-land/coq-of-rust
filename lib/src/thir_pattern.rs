use crate::env::*;
use crate::path::*;
use crate::pattern::*;
use rustc_middle::thir::{Pat, PatKind};
use rustc_type_ir::sty::TyKind;

pub(crate) fn compile_pattern(env: &Env, pat: &Pat) -> Pattern {
    match &pat.kind {
        PatKind::Wild => Pattern::Wild,
        PatKind::AscribeUserType { subpattern, .. } => compile_pattern(env, subpattern),
        PatKind::Binding {
            name, subpattern, ..
        } => {
            let name = name.to_string();
            match subpattern {
                None => Pattern::Variable(name),
                Some(subpattern) => {
                    Pattern::Binding(name, Box::new(compile_pattern(env, subpattern)))
                }
            }
        }
        PatKind::Variant {
            adt_def,
            variant_index,
            subpatterns,
            ..
        } => {
            let path = compile_def_id(env, adt_def.did());
            let variant = adt_def.variant(*variant_index);
            let struct_or_variant = StructOrVariant::Variant;
            let fields: Vec<_> = subpatterns
                .iter()
                .map(|field| {
                    (
                        variant.fields.get(field.field).unwrap().name.to_string(),
                        compile_pattern(env, &field.pattern),
                    )
                })
                .collect();
            let is_a_tuple = fields
                .iter()
                .all(|(name, _)| name.starts_with(|c: char| c.is_ascii_digit()));
            if is_a_tuple {
                let fields = fields.into_iter().map(|(_, pattern)| pattern).collect();
                Pattern::StructTuple(path, fields, struct_or_variant)
            } else {
                Pattern::StructStruct(path, fields, struct_or_variant)
            }
        }
        PatKind::Leaf { subpatterns } => {
            if let TyKind::Tuple(_) = pat.ty.kind() {
                return Pattern::Tuple(
                    subpatterns
                        .iter()
                        .map(|field| compile_pattern(env, &field.pattern))
                        .collect(),
                );
            }
            let adt_def = pat.ty.ty_adt_def().unwrap();
            let path = compile_def_id(env, adt_def.did());
            let variant = adt_def.non_enum_variant();
            let struct_or_variant = StructOrVariant::Struct;
            let fields: Vec<_> = subpatterns
                .iter()
                .map(|field| {
                    (
                        variant.fields.get(field.field).unwrap().name.to_string(),
                        compile_pattern(env, &field.pattern),
                    )
                })
                .collect();
            let is_a_tuple = fields
                .iter()
                .all(|(name, _)| name.starts_with(|c: char| c.is_ascii_digit()));
            if is_a_tuple {
                let fields = fields.into_iter().map(|(_, pattern)| pattern).collect();
                Pattern::StructTuple(path, fields, struct_or_variant)
            } else {
                Pattern::StructStruct(path, fields, struct_or_variant)
            }
        }
        PatKind::Deref { subpattern } => compile_pattern(env, subpattern),
        // /// One of the following:
        // /// * `&str`, which will be handled as a string pattern and thus exhaustiveness
        // ///   checking will detect if you use the same string twice in different patterns.
        // /// * integer, bool, char or float, which will be handled by exhaustiveness to cover exactly
        // ///   its own value, similar to `&str`, but these values are much simpler.
        // /// * Opaque constants, that must not be matched structurally. So anything that does not derive
        // ///   `PartialEq` and `Eq`.
        // Constant {
        //     value: mir::ConstantKind<'tcx>,
        // },

        // Range(Box<PatRange<'tcx>>),

        // /// Matches against a slice, checking the length and extracting elements.
        // /// irrefutable when there is a slice pattern and both `prefix` and `suffix` are empty.
        // /// e.g., `&[ref xs @ ..]`.
        // Slice {
        //     prefix: Box<[Box<Pat<'tcx>>]>,
        //     slice: Option<Box<Pat<'tcx>>>,
        //     suffix: Box<[Box<Pat<'tcx>>]>,
        // },

        // /// Fixed match against an array; irrefutable.
        // Array {
        //     prefix: Box<[Box<Pat<'tcx>>]>,
        //     slice: Option<Box<Pat<'tcx>>>,
        //     suffix: Box<[Box<Pat<'tcx>>]>,
        // },
        PatKind::Or { pats } => {
            Pattern::Or(pats.iter().map(|pat| compile_pattern(env, pat)).collect())
        }
        _ => panic!("pattern {pat:#?} not implemented"),
    }
}
