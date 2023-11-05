use crate::env::*;
use crate::path::*;
use crate::pattern::*;
use rustc_middle::thir::{Pat, PatKind};
use rustc_type_ir::sty::TyKind;

// fn const_to_lit_kind(constant: rustc_middle::mir::ConstantKind) -> rustc_ast::LitKind {
//     match constant {
//         rustc_middle::mir::ConstantKind::Val(value, _) => match value {
//             rustc_middle::mir::interpret::ConstValue::Scalar(scalar) => match scalar.to_u128() {
//                 Result::Ok(value) => {
//                     return rustc_ast::LitKind::Int(
//                         value as u128,
//                         rustc_ast::LitIntType::Unsuffixed,
//                     );
//                 }
//                 Result::Err(_) => (),
//             },
//             _ => (),
//         },
//         _ => (),
//     }
//     panic!("constant {:#?} not yet handled", constant);
// }

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
            let variant = adt_def.variant(*variant_index);
            let path = Path::concat(&[
                compile_def_id(env, adt_def.did()),
                Path::local(variant.name.to_string()),
            ]);
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
        // PatKind::Constant { value } => {
        //     let literal = const_to_lit_kind(*value);
        //     Pattern::Lit(literal)
        // }
        PatKind::Constant { .. } => {
            env.tcx
                .sess
                .struct_span_warn(pat.span, "Constants in patterns are not yet supported.")
                .emit();
            Pattern::Wild
        }
        PatKind::Range(_) => {
            env.tcx
                .sess
                .struct_span_warn(pat.span, "Ranges in patterns are not yet supported.")
                .emit();
            Pattern::Wild
        }
        PatKind::Slice {
            prefix,
            slice,
            suffix,
        }
        | PatKind::Array {
            prefix,
            slice,
            suffix,
        } => {
            let prefix: Vec<Pattern> = prefix.iter().map(|pat| compile_pattern(env, pat)).collect();
            let suffix: Vec<Pattern> = suffix.iter().map(|pat| compile_pattern(env, pat)).collect();
            match slice {
                Some(pat_middle) => {
                    if suffix.is_empty() {
                        let pat_middle = compile_pattern(env, pat_middle);
                        Pattern::Slice {
                            init_patterns: prefix,
                            slice_pattern: Some(Box::new(pat_middle)),
                        }
                    } else {
                        env.tcx
                            .sess
                            .struct_span_warn(
                                pat.span,
                                "Destructuring after slice patterns is not supported.",
                            )
                            .help("Reverse the slice instead.")
                            .emit();
                        Pattern::Wild
                    }
                }
                None => {
                    let all_patterns = [prefix, suffix].concat().to_vec();
                    Pattern::Slice {
                        init_patterns: all_patterns,
                        slice_pattern: None,
                    }
                }
            }
        }
        PatKind::Or { pats } => {
            Pattern::Or(pats.iter().map(|pat| compile_pattern(env, pat)).collect())
        }
    }
}
