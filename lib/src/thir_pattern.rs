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
            var: _,
            ty: _,
            subpattern,
            is_primary: _,
        } => {
            let name = to_valid_coq_name(IsValue::Yes, name.as_str());
            let rustc_ast::ast::BindingMode(by_ref, _) = mode;
            let is_with_ref = matches!(by_ref, rustc_ast::ast::ByRef::Yes(_));
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
                Path::new(&[variant.name.as_str()]),
            ]);
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
                Rc::new(Pattern::StructTuple(path, fields))
            } else {
                Rc::new(Pattern::StructRecord(path, fields))
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
                Rc::new(Pattern::StructTuple(path, fields))
            } else {
                Rc::new(Pattern::StructRecord(path, fields))
            }
        }
        PatKind::Deref { subpattern } => Rc::new(Pattern::Deref(compile_pattern(env, subpattern))),
        PatKind::Constant { value } => {
            if let rustc_middle::mir::Const::Ty(ty, constant) = value {
                // Brutal way to handle the case of rustc_middle::ty::TyKind::Str
                // Since the type would be erased when it comes down to THIR level
                // TODO: have a translation that works for all strings
                let kind_name = format!("{:?}", ty.kind());
                if kind_name == "&'{erased} str" {
                    let string_value = constant.to_string();
                    // The generated string comes with extra "" so we trim the 1st and last character out
                    let mut chars = string_value.chars();
                    chars.next();
                    chars.next_back();
                    let string_value = chars.as_str();
                    return Rc::new(Pattern::Literal(Rc::new(Literal::String(
                        string_value.to_string(),
                    ))));
                }
                // And for the rest...
                match &ty.kind() {
                    rustc_middle::ty::TyKind::Int(int_ty) => {
                        let uint_value = constant.try_to_scalar().unwrap().assert_scalar_int();
                        let int_value = uint_value.to_int(uint_value.size());

                        return Rc::new(Pattern::Literal(Rc::new(Literal::Integer(
                            LiteralInteger {
                                kind: capitalize(&format!("{int_ty:?}")),
                                negative_sign: int_value < 0,
                                // The `unsigned_abs` method is necessary to get the minimal int128's
                                // absolute value.
                                value: int_value.unsigned_abs(),
                            },
                        ))));
                    }
                    rustc_middle::ty::TyKind::Uint(uint_ty) => {
                        let uint_value = constant.try_to_scalar().unwrap().assert_scalar_int();

                        return Rc::new(Pattern::Literal(Rc::new(Literal::Integer(
                            LiteralInteger {
                                kind: capitalize(&format!("{uint_ty:?}")),
                                negative_sign: false,
                                value: uint_value.to_bits(uint_value.size()),
                            },
                        ))));
                    }
                    rustc_middle::ty::TyKind::Bool => {
                        let bool_value = constant.try_to_scalar().unwrap().to_bool().unwrap();

                        return Rc::new(Pattern::Literal(Rc::new(Literal::Bool(bool_value))));
                    }
                    rustc_middle::ty::TyKind::Char => {
                        let char_value = constant.try_to_scalar().unwrap().to_char().unwrap();

                        return Rc::new(Pattern::Literal(Rc::new(Literal::Char(char_value))));
                    }
                    // TODO: handle other kinds of constants
                    _ => {}
                }
            }
            emit_warning_with_note(
                env,
                &pat.span,
                "This kind of constant in patterns is not yet supported.",
                None,
            );

            Rc::new(Pattern::Wild)
        }
        PatKind::Range(_) => {
            emit_warning_with_note(
                env,
                &pat.span,
                "Ranges in patterns are not yet supported.",
                None,
            );
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
            let slice_pattern: Option<Rc<Pattern>> = slice
                .as_ref()
                .map(|pat_middle| compile_pattern(env, pat_middle));
            Rc::new(Pattern::Slice {
                prefix_patterns: prefix,
                slice_pattern,
                suffix_patterns: suffix,
            })
        }
        PatKind::Or { pats } => Rc::new(Pattern::Or(
            pats.iter().map(|pat| compile_pattern(env, pat)).collect(),
        )),
        PatKind::InlineConstant { .. }
        | PatKind::Never
        | PatKind::Error(_)
        | PatKind::DerefPattern { .. } => todo!(),
    }
}
