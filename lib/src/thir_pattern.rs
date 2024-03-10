use crate::env::*;
use crate::expression::*;
use crate::path::*;
use crate::pattern::*;
use crate::render::*;
use rustc_middle::thir::{Pat, PatKind};
use rustc_type_ir::TyKind;
use std::rc::Rc;

pub(crate) fn compile_pattern(env: &Env, pat: &Pat) -> Rc<Pattern> {
    match &pat.kind {
        PatKind::Wild => Rc::new(Pattern::Wild),
        PatKind::AscribeUserType { subpattern, .. } => compile_pattern(env, subpattern),
        PatKind::Binding {
            name,
            mode,
            subpattern,
            ..
        } => {
            let name = to_valid_coq_name(name.as_str());
            let is_with_ref = match mode {
                rustc_middle::thir::BindingMode::ByValue => false,
                rustc_middle::thir::BindingMode::ByRef(_) => true,
            };
            let pattern = subpattern
                .as_ref()
                .map(|subpattern| compile_pattern(env, subpattern));
            Rc::new(Pattern::Binding {
                name,
                is_with_ref,
                pattern,
            })
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
                Path::local(variant.name.as_str()),
            ]);
            let struct_or_variant = StructOrVariant::Variant {
                nb_cases: adt_def.variants().len(),
            };
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
                Rc::new(Pattern::StructTuple(path, fields, struct_or_variant))
            } else {
                Rc::new(Pattern::StructStruct(path, fields, struct_or_variant))
            }
        }
        PatKind::Leaf { subpatterns } => {
            if let TyKind::Tuple(tys) = &pat.ty.kind() {
                // With the notation `..` some of the fields might be omitted. This is why we
                // first create a fields of wildcards and then replace the ones that are
                // present in the pattern.
                let mut fields: Vec<_> = tys.iter().map(|_| Rc::new(Pattern::Wild)).collect();

                for subpattern in subpatterns {
                    fields[subpattern.field.index()] = compile_pattern(env, &subpattern.pattern);
                }

                return Rc::new(Pattern::Tuple(fields));
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
                Rc::new(Pattern::StructTuple(path, fields, struct_or_variant))
            } else {
                Rc::new(Pattern::StructStruct(path, fields, struct_or_variant))
            }
        }
        PatKind::Deref { subpattern } => Rc::new(Pattern::Deref(compile_pattern(env, subpattern))),
        PatKind::Constant { value } => {
            if let rustc_middle::mir::Const::Ty(constant) = value {
                let ty = constant.ty();

                match &ty.kind() {
                    rustc_middle::ty::TyKind::Int(int_ty) => {
                        let uint_value = constant.try_to_scalar().unwrap().assert_int();
                        let int_value = uint_value.try_to_int(uint_value.size()).unwrap();

                        return Rc::new(Pattern::Literal(Rc::new(Literal::Integer(
                            LiteralInteger {
                                name: capitalize(&format!("{int_ty:?}")),
                                negative_sign: int_value < 0,
                                // The `unsigned_abs` method is necessary to get the minimal int128's
                                // absolute value.
                                value: int_value.unsigned_abs(),
                            },
                        ))));
                    }
                    rustc_middle::ty::TyKind::Uint(uint_ty) => {
                        let uint_value = constant.try_to_scalar().unwrap().assert_int();

                        return Rc::new(Pattern::Literal(Rc::new(Literal::Integer(
                            LiteralInteger {
                                name: capitalize(&format!("{uint_ty:?}")),
                                negative_sign: false,
                                value: uint_value.assert_bits(uint_value.size()),
                            },
                        ))));
                    }
                    // TODO: handle other kinds of constants
                    _ => {}
                }
            }
            env.tcx
                .sess
                .struct_span_warn(
                    pat.span,
                    "This kind of constant in patterns is not yet supported.",
                )
                .emit();

            Rc::new(Pattern::Wild)
        }
        PatKind::Range(_) => {
            env.tcx
                .sess
                .struct_span_warn(pat.span, "Ranges in patterns are not yet supported.")
                .emit();
            Rc::new(Pattern::Wild)
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
            let prefix: Vec<Rc<Pattern>> =
                prefix.iter().map(|pat| compile_pattern(env, pat)).collect();
            let suffix: Vec<Rc<Pattern>> =
                suffix.iter().map(|pat| compile_pattern(env, pat)).collect();
            match slice {
                Some(pat_middle) => {
                    if suffix.is_empty() {
                        let pat_middle = compile_pattern(env, pat_middle);
                        Rc::new(Pattern::Slice {
                            init_patterns: prefix,
                            slice_pattern: Some(pat_middle),
                        })
                    } else {
                        env.tcx
                            .sess
                            .struct_span_warn(
                                pat.span,
                                "Destructuring after slice patterns is not supported.",
                            )
                            .help("Reverse the slice instead.")
                            .emit();
                        Rc::new(Pattern::Wild)
                    }
                }
                None => {
                    let all_patterns = [prefix, suffix].concat().to_vec();
                    Rc::new(Pattern::Slice {
                        init_patterns: all_patterns,
                        slice_pattern: None,
                    })
                }
            }
        }
        PatKind::Or { pats } => Rc::new(Pattern::Or(
            pats.iter().map(|pat| compile_pattern(env, pat)).collect(),
        )),
        PatKind::InlineConstant { .. } | PatKind::Never | PatKind::Error(_) => todo!(),
    }
}
