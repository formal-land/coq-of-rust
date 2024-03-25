use crate::env::*;
use crate::expression::*;
use crate::path::*;
use crate::pattern::*;
use crate::render::*;
use crate::thir_ty::*;
use crate::ty::CoqType;
use rustc_hir::def::DefKind;
use rustc_middle::mir::{BinOp, UnOp};
use rustc_middle::thir;
use rustc_middle::thir::{AdtExpr, LogicalOp};
use rustc_middle::ty::TyKind;
use std::rc::Rc;

fn path_of_bin_op(bin_op: &BinOp) -> (&'static str, CallKind) {
    match bin_op {
        BinOp::Add => ("BinOp.Panic.add", CallKind::Effectful),
        BinOp::Sub => ("BinOp.Panic.sub", CallKind::Effectful),
        BinOp::Mul => ("BinOp.Panic.mul", CallKind::Effectful),
        BinOp::Div => ("BinOp.Panic.div", CallKind::Effectful),
        BinOp::Rem => ("BinOp.Panic.rem", CallKind::Effectful),
        BinOp::BitXor => ("BinOp.Pure.bit_xor", CallKind::Pure),
        BinOp::BitAnd => ("BinOp.Pure.bit_and", CallKind::Pure),
        BinOp::BitOr => ("BinOp.Pure.bit_or", CallKind::Pure),
        BinOp::Shl => ("BinOp.Panic.shl", CallKind::Effectful),
        BinOp::Shr => ("BinOp.Panic.shr", CallKind::Effectful),
        BinOp::Eq => ("BinOp.Pure.eq", CallKind::Pure),
        BinOp::Ne => ("BinOp.Pure.ne", CallKind::Pure),
        BinOp::Lt => ("BinOp.Pure.lt", CallKind::Pure),
        BinOp::Le => ("BinOp.Pure.le", CallKind::Pure),
        BinOp::Ge => ("BinOp.Pure.ge", CallKind::Pure),
        BinOp::Gt => ("BinOp.Pure.gt", CallKind::Pure),
        BinOp::Offset => ("BinOp.Pure.offset", CallKind::Pure),
        _ => todo!(),
    }
}

pub(crate) fn allocate_bindings(bindings: &[String], body: Rc<Expr>) -> Rc<Expr> {
    bindings.iter().rfold(body, |body, binding| {
        Rc::new(Expr::Let {
            is_monadic: false,
            name: Some(binding.clone()),
            init: Expr::local_var(binding).alloc(),
            body,
        })
    })
}

fn build_inner_match(
    patterns: Vec<(String, Rc<Pattern>)>,
    body: Rc<Expr>,
    depth: usize,
) -> Rc<Expr> {
    patterns
        .into_iter()
        .rfold(body, |body, (scrutinee, pattern)| match pattern.as_ref() {
            Pattern::Wild => body,
            Pattern::Binding {
                name,
                is_with_ref,
                pattern,
            } => Rc::new(Expr::Let {
                is_monadic: false,
                name: Some(name.clone()),
                init: if *is_with_ref {
                    Expr::local_var(&scrutinee).alloc()
                } else {
                    Expr::local_var(&scrutinee).copy()
                },
                body: match pattern {
                    None => body,
                    Some(pattern) => {
                        build_inner_match(vec![(scrutinee, pattern.clone())], body, depth + 1)
                    }
                },
            }),
            Pattern::StructStruct(path, fields, _) => {
                let body = build_inner_match(
                    fields
                        .iter()
                        .enumerate()
                        .map(|(index, (_, field_pattern))| {
                            (format!("γ{depth}_{index}"), field_pattern.clone())
                        })
                        .collect(),
                    body,
                    depth + 1,
                );

                fields
                    .iter()
                    .enumerate()
                    .rfold(body, |body, (index, (field_name, _))| {
                        Rc::new(Expr::Let {
                            is_monadic: false,
                            name: Some(format!("γ{depth}_{index}")),
                            init: Rc::new(Expr::Call {
                                func: Expr::local_var("M.get_struct_record_field_or_break_match"),
                                args: vec![
                                    Expr::local_var(&scrutinee),
                                    Rc::new(Expr::InternalString(path.to_string())),
                                    Rc::new(Expr::InternalString(field_name.clone())),
                                ],
                                kind: CallKind::Effectful,
                            }),
                            body,
                        })
                    })
            }
            Pattern::StructTuple(path, patterns, _) => {
                let body = build_inner_match(
                    patterns
                        .iter()
                        .enumerate()
                        .map(|(index, pattern)| (format!("γ{depth}_{index}"), pattern.clone()))
                        .collect(),
                    body,
                    depth + 1,
                );

                patterns.iter().enumerate().rfold(body, |body, (index, _)| {
                    Rc::new(Expr::Let {
                        is_monadic: false,
                        name: Some(format!("γ{depth}_{index}")),
                        init: Rc::new(Expr::Call {
                            func: Expr::local_var("M.get_struct_tuple_field_or_break_match"),
                            args: vec![
                                Expr::local_var(&scrutinee),
                                Rc::new(Expr::InternalString(path.to_string())),
                                Rc::new(Expr::InternalInteger(index)),
                            ],
                            kind: CallKind::Effectful,
                        }),
                        body,
                    })
                })
            }
            Pattern::Deref(pattern) => Rc::new(Expr::Let {
                is_monadic: false,
                name: Some(scrutinee.clone()),
                init: Expr::local_var(&scrutinee).read(),
                body: build_inner_match(
                    vec![(scrutinee.clone(), pattern.clone())],
                    body,
                    depth + 1,
                ),
            }),
            Pattern::Or(_) => panic!("Or pattern should have been flattened"),
            Pattern::Tuple(patterns) => {
                let body = build_inner_match(
                    patterns
                        .iter()
                        .enumerate()
                        .map(|(index, pattern)| (format!("γ{depth}_{index}"), pattern.clone()))
                        .collect(),
                    body,
                    depth + 1,
                );

                patterns.iter().enumerate().rfold(body, |body, (index, _)| {
                    Rc::new(Expr::Let {
                        is_monadic: false,
                        name: Some(format!("γ{depth}_{index}")),
                        init: Rc::new(Expr::Call {
                            func: Expr::local_var("M.get_tuple_field"),
                            args: vec![
                                Expr::local_var(&scrutinee),
                                Rc::new(Expr::InternalInteger(index)),
                            ],
                            kind: CallKind::Pure,
                        }),
                        body,
                    })
                })
            }
            Pattern::Literal(literal) => Rc::new(Expr::Let {
                is_monadic: false,
                name: None,
                init: Rc::new(Expr::Call {
                    func: Expr::local_var("M.is_constant_or_break_match"),
                    args: vec![
                        Expr::local_var(&scrutinee).read(),
                        Rc::new(Expr::Literal(literal.clone())),
                    ],
                    kind: CallKind::Effectful,
                }),
                body,
            }),
            Pattern::Slice {
                init_patterns,
                slice_pattern,
            } => {
                let body = build_inner_match(
                    [
                        init_patterns
                            .iter()
                            .enumerate()
                            .map(|(index, pattern)| (format!("γ{depth}_{index}"), pattern.clone()))
                            .collect(),
                        match slice_pattern {
                            None => vec![],
                            Some(slice_pattern) => {
                                vec![(format!("γ{depth}_rest"), slice_pattern.clone())]
                            }
                        },
                    ]
                    .concat(),
                    body,
                    depth + 1,
                );
                let body = match slice_pattern {
                    None => body,
                    Some(_) => Rc::new(Expr::Let {
                        is_monadic: false,
                        name: Some(format!("γ{depth}_rest")),
                        init: Rc::new(Expr::Call {
                            func: Expr::local_var("M.get_slice_rest_or_break_match"),
                            args: vec![
                                Expr::local_var(&scrutinee),
                                Rc::new(Expr::InternalInteger(init_patterns.len())),
                            ],
                            kind: CallKind::Effectful,
                        }),
                        body,
                    }),
                };

                init_patterns
                    .iter()
                    .enumerate()
                    .rfold(body, |body, (index, _)| {
                        Rc::new(Expr::Let {
                            is_monadic: false,
                            name: Some(format!("γ{depth}_{index}")),
                            init: Rc::new(Expr::Call {
                                func: Expr::local_var("get_slice_index_or_break_match"),
                                args: vec![
                                    Expr::local_var(&scrutinee),
                                    Rc::new(Expr::InternalInteger(index)),
                                ],
                                kind: CallKind::Effectful,
                            }),
                            body,
                        })
                    })
            }
        })
}

fn build_match(scrutinee: Rc<Expr>, arms: Vec<MatchArm>) -> Rc<Expr> {
    let arms_with_flatten_patterns = arms.into_iter().flat_map(|MatchArm { pattern, body }| {
        pattern
            .flatten_ors()
            .into_iter()
            .map(move |pattern| MatchArm {
                pattern,
                body: body.clone(),
            })
    });

    Rc::new(Expr::Call {
        func: Expr::local_var("match_operator"),
        args: vec![
            scrutinee,
            Rc::new(Expr::Array {
                elements: arms_with_flatten_patterns
                    .map(|MatchArm { pattern, body }| {
                        Rc::new(Expr::Lambda {
                            args: vec![("γ".to_string(), None)],
                            body: build_inner_match(vec![("γ".to_string(), pattern)], body, 0),
                            is_internal: true,
                        })
                    })
                    .collect(),
                is_internal: true,
            }),
        ],
        kind: CallKind::Effectful,
    })
}

fn get_let_if<'a>(
    env: &Env<'a>,
    generics: &'a rustc_middle::ty::Generics,
    thir: &rustc_middle::thir::Thir<'a>,
    expr_id: &rustc_middle::thir::ExprId,
) -> Option<(Rc<Pattern>, Rc<Expr>)> {
    let expr = thir.exprs.get(*expr_id).unwrap();

    match &expr.kind {
        thir::ExprKind::Scope { value, .. } => get_let_if(env, generics, thir, value),
        thir::ExprKind::Let { expr, pat, .. } => Some((
            crate::thir_pattern::compile_pattern(env, pat),
            compile_expr(env, generics, thir, expr),
        )),
        _ => None,
    }
}

fn compile_literal_integer(
    env: &Env,
    span: &rustc_span::Span,
    ty: &rustc_middle::ty::Ty,
    negative_sign: bool,
    integer: u128,
) -> LiteralInteger {
    let uncapitalized_name = match ty.kind() {
        TyKind::Int(int_ty) => format!("{int_ty:?}"),
        TyKind::Uint(uint_ty) => format!("{uint_ty:?}"),
        _ => {
            emit_warning_with_note(env, span, "Unknown integer type", "Please report 🙏");

            "unknown_kind_of_integer".to_string()
        }
    };
    let name = capitalize(&uncapitalized_name);

    LiteralInteger {
        name,
        negative_sign,
        value: integer,
    }
}

pub(crate) fn compile_expr<'a>(
    env: &Env<'a>,
    generics: &'a rustc_middle::ty::Generics,
    thir: &rustc_middle::thir::Thir<'a>,
    expr_id: &rustc_middle::thir::ExprId,
) -> Rc<Expr> {
    let expr = thir.exprs.get(*expr_id).unwrap();

    match &expr.kind {
        thir::ExprKind::Scope { value, .. } => compile_expr(env, generics, thir, value),
        thir::ExprKind::Box { value } => {
            let value_ty = compile_type(env, generics, &thir.exprs.get(*value).unwrap().ty);
            let value = compile_expr(env, generics, thir, value);

            Rc::new(Expr::Call {
                func: Rc::new(Expr::GetAssociatedFunction {
                    ty: Rc::new(CoqType::Application {
                        func: Rc::new(CoqType::Path {
                            path: Rc::new(Path::new(&["alloc", "boxed", "Box"])),
                        }),
                        args: vec![
                            value_ty,
                            Rc::new(CoqType::Path {
                                path: Rc::new(Path::new(&["alloc", "alloc", "Global"])),
                            }),
                        ],
                    }),
                    func: "new".to_string(),
                    generic_tys: vec![],
                }),
                args: vec![value],
                kind: CallKind::Closure,
            })
        }
        thir::ExprKind::If {
            cond,
            then,
            else_opt,
            ..
        } => {
            let success = compile_expr(env, generics, thir, then);
            let failure = match else_opt {
                Some(else_expr) => compile_expr(env, generics, thir, else_expr),
                None => Expr::tt(),
            };

            if let Some((pattern, expr)) = get_let_if(env, generics, thir, cond) {
                return build_match(
                    expr,
                    vec![
                        MatchArm {
                            pattern,
                            body: success,
                        },
                        MatchArm {
                            pattern: Rc::new(Pattern::Wild),
                            body: failure,
                        },
                    ],
                );
            }

            let condition = compile_expr(env, generics, thir, cond).read();

            Rc::new(Expr::If {
                condition,
                success,
                failure,
            })
        }
        thir::ExprKind::Call { fun, args, .. } => {
            let args = args
                .iter()
                .map(|arg| compile_expr(env, generics, thir, arg).read())
                .collect();
            let func = compile_expr(env, generics, thir, fun);
            let kind = {
                let default = CallKind::Closure;

                match func.match_simple_call(&["M.alloc"]).as_ref() {
                    Some(expr) => match expr.as_ref() {
                        Expr::Constructor(_) => CallKind::Pure,
                        _ => default,
                    },
                    _ => default,
                }
            };
            let func = func.read();

            Rc::new(Expr::Call { func, args, kind }).alloc()
        }
        thir::ExprKind::Deref { arg } => compile_expr(env, generics, thir, arg).read(),
        thir::ExprKind::Binary { op, lhs, rhs } => {
            let (path, kind) = path_of_bin_op(op);
            let lhs = compile_expr(env, generics, thir, lhs);
            let rhs = compile_expr(env, generics, thir, rhs);

            Rc::new(Expr::Call {
                func: Expr::local_var(path),
                args: vec![lhs.read(), rhs.read()],
                kind,
            })
            .alloc()
        }
        thir::ExprKind::LogicalOp { op, lhs, rhs } => {
            let path = match op {
                LogicalOp::And => "LogicalOp.and",
                LogicalOp::Or => "LogicalOp.or",
            };
            let lhs = compile_expr(env, generics, thir, lhs).read();
            let rhs = compile_expr(env, generics, thir, rhs).read();

            Rc::new(Expr::LogicalOperator {
                name: path.to_string(),
                lhs,
                rhs,
            })
            .alloc()
        }
        thir::ExprKind::Unary { op, arg } => {
            let (path, kind) = match op {
                UnOp::Not => ("UnOp.Pure.not", CallKind::Pure),
                UnOp::Neg => ("UnOp.Panic.neg", CallKind::Effectful),
            };
            let arg = compile_expr(env, generics, thir, arg);

            Rc::new(Expr::Call {
                func: Expr::local_var(path),
                args: vec![arg.read()],
                kind,
            })
            .alloc()
        }
        thir::ExprKind::Cast { source } => {
            let func = Expr::local_var("M.rust_cast");
            let source = compile_expr(env, generics, thir, source);

            Rc::new(Expr::Call {
                func,
                args: vec![source.read()],
                kind: CallKind::Pure,
            })
            .alloc()
        }
        thir::ExprKind::Use { source } => {
            let source = compile_expr(env, generics, thir, source);

            Rc::new(Expr::Use(source))
        }
        thir::ExprKind::NeverToAny { source } => {
            let func = Expr::local_var("M.never_to_any");
            let source = compile_expr(env, generics, thir, source);

            Rc::new(Expr::Call {
                func,
                args: vec![source.read()],
                kind: CallKind::Effectful,
            })
            .alloc()
        }
        thir::ExprKind::PointerCoercion { source, cast } => {
            let func = Expr::local_var("M.pointer_coercion");
            let source = compile_expr(env, generics, thir, source).read();
            let cast = Rc::new(Expr::Message(format!("{cast:?}")));

            Rc::new(Expr::Call {
                func,
                args: vec![cast, source],
                kind: CallKind::Pure,
            })
            .alloc()
        }
        thir::ExprKind::Loop { body, .. } => {
            let body = compile_expr(env, generics, thir, body);

            Rc::new(Expr::Loop { body })
        }
        thir::ExprKind::Let { .. } => {
            Rc::new(Expr::Message("`if let` expected into an `if`".to_string()))
        }
        thir::ExprKind::Match {
            scrutinee, arms, ..
        } => {
            let scrutinee = compile_expr(env, generics, thir, scrutinee);
            let arms: Vec<MatchArm> = arms
                .iter()
                .map(|arm_id| {
                    let arm = thir.arms.get(*arm_id).unwrap();
                    let pattern = crate::thir_pattern::compile_pattern(env, &arm.pattern);
                    let body = compile_expr(env, generics, thir, &arm.body);
                    MatchArm { pattern, body }
                })
                .collect();

            build_match(scrutinee, arms)
        }
        thir::ExprKind::Block { block: block_id } => compile_block(env, generics, thir, block_id),
        thir::ExprKind::Assign { lhs, rhs } => {
            let func = Expr::local_var("M.assign");
            let args = vec![
                compile_expr(env, generics, thir, lhs),
                compile_expr(env, generics, thir, rhs).read(),
            ];

            Rc::new(Expr::Call {
                func,
                args,
                kind: CallKind::Effectful,
            })
        }
        thir::ExprKind::AssignOp { op, lhs, rhs } => {
            let (path, kind) = path_of_bin_op(op);
            let lhs = compile_expr(env, generics, thir, lhs);
            let rhs = compile_expr(env, generics, thir, rhs);

            Rc::new(Expr::Let {
                is_monadic: false,
                name: Some("β".to_string()),
                init: lhs,
                body: Rc::new(Expr::Call {
                    func: Expr::local_var("M.assign"),
                    args: vec![
                        Expr::local_var("β"),
                        Rc::new(Expr::Call {
                            func: Expr::local_var(path),
                            args: vec![Expr::local_var("β").read(), rhs.read()],
                            kind,
                        }),
                    ],
                    kind: CallKind::Effectful,
                }),
            })
        }
        thir::ExprKind::Field {
            lhs,
            variant_index,
            name,
        } => {
            let base = compile_expr(env, generics, thir, lhs);
            let ty = thir.exprs.get(*lhs).unwrap().ty;

            match ty.ty_adt_def() {
                Some(adt_def) => {
                    let variant = adt_def.variant(*variant_index);
                    let name = variant.fields.get(*name).unwrap().name.to_string();
                    let is_name_a_number = name.chars().all(|c| c.is_ascii_digit());
                    let getter_name = if is_name_a_number {
                        "M.get_struct_tuple_field"
                    } else {
                        "M.get_struct_record_field"
                    };
                    let constructor_name = compile_def_id(env, adt_def.did()).to_string();
                    let constructor = Rc::new(Expr::InternalString(constructor_name));
                    let index = if is_name_a_number {
                        Expr::local_var(&name)
                    } else {
                        Rc::new(Expr::InternalString(name))
                    };

                    Rc::new(Expr::Call {
                        func: Expr::local_var(getter_name),
                        args: vec![base, constructor, index],
                        kind: CallKind::Pure,
                    })
                }
                None => {
                    // We assume that we are in the case of a tuple.
                    Rc::new(Expr::Call {
                        func: Expr::local_var("M.get_tuple_field"),
                        args: vec![base, Rc::new(Expr::InternalInteger(name.as_usize()))],
                        kind: CallKind::Pure,
                    })
                }
            }
        }
        thir::ExprKind::Index { lhs, index } => {
            let base = compile_expr(env, generics, thir, lhs);
            let index = compile_expr(env, generics, thir, index);

            Rc::new(Expr::Index { base, index })
        }
        thir::ExprKind::VarRef { id } => {
            let name = to_valid_coq_name(env.tcx.hir().opt_name(id.0).unwrap().as_str());

            Rc::new(Expr::LocalVar(name))
        }
        thir::ExprKind::UpvarRef { var_hir_id, .. } => {
            let name = to_valid_coq_name(env.tcx.hir().opt_name(var_hir_id.0).unwrap().as_str());

            Rc::new(Expr::LocalVar(name))
        }
        thir::ExprKind::Borrow {
            borrow_kind: _,
            arg,
        }
        | thir::ExprKind::AddressOf { mutability: _, arg } => {
            compile_expr(env, generics, thir, arg).alloc()
        }
        thir::ExprKind::Break { .. } => Rc::new(Expr::ControlFlow(LoopControlFlow::Break)),
        thir::ExprKind::Continue { .. } => Rc::new(Expr::ControlFlow(LoopControlFlow::Continue)),
        thir::ExprKind::Return { value } => {
            let value = match value {
                Some(value) => compile_expr(env, generics, thir, value).read(),
                None => Expr::tt().read(),
            };

            Rc::new(Expr::Return(value))
        }
        rustc_middle::thir::ExprKind::Become { value } => {
            let value = compile_expr(env, generics, thir, value).read();

            Rc::new(Expr::Return(value))
        }
        thir::ExprKind::ConstBlock { did, .. } => {
            Rc::new(Expr::GetConst(compile_def_id(env, *did)))
        }
        thir::ExprKind::Repeat { value, count } => {
            let func = Expr::local_var("repeat");
            let args = vec![
                compile_expr(env, generics, thir, value).read(),
                Expr::local_var(&count.to_string()),
            ];

            Rc::new(Expr::Call {
                func,
                args,
                kind: CallKind::Pure,
            })
            .alloc()
        }
        thir::ExprKind::Array { fields } => Rc::new(Expr::Array {
            elements: fields
                .iter()
                .map(|field| compile_expr(env, generics, thir, field).read())
                .collect(),
            is_internal: false,
        })
        .alloc(),
        thir::ExprKind::Tuple { fields } => {
            let elements: Vec<_> = fields
                .iter()
                .map(|field| compile_expr(env, generics, thir, field).read())
                .collect();
            if elements.is_empty() {
                Expr::tt()
            } else {
                Rc::new(Expr::Tuple { elements }).alloc()
            }
        }
        thir::ExprKind::Adt(adt_expr) => {
            let AdtExpr {
                adt_def,
                variant_index,
                fields,
                base,
                ..
            } = adt_expr.as_ref();
            let variant = adt_def.variant(*variant_index);
            let path = compile_def_id(env, variant.def_id);
            let fields: Vec<_> = fields
                .iter()
                .map(|field| {
                    (
                        to_valid_coq_name(variant.fields.get(field.name).unwrap().name.as_str()),
                        compile_expr(env, generics, thir, &field.expr).read(),
                    )
                })
                .collect();
            let is_a_tuple = !fields.is_empty()
                && fields
                    .iter()
                    .all(|(name, _)| name.starts_with(|c: char| c.is_ascii_digit()));
            let struct_or_variant = if adt_def.is_enum() {
                StructOrVariant::Variant {
                    nb_cases: adt_def.variants().len(),
                }
            } else {
                StructOrVariant::Struct
            };
            let base = base
                .as_ref()
                .map(|base| compile_expr(env, generics, thir, &base.base).read());

            if fields.is_empty() {
                return Rc::new(Expr::StructUnit {
                    path,
                    struct_or_variant,
                })
                .alloc();
            }

            if is_a_tuple {
                let fields = fields.into_iter().map(|(_, pattern)| pattern).collect();
                Rc::new(Expr::StructTuple {
                    path,
                    fields,
                    struct_or_variant,
                })
                .alloc()
            } else {
                Rc::new(Expr::StructStruct {
                    path,
                    fields,
                    base,
                    struct_or_variant,
                })
                .alloc()
            }
        }
        thir::ExprKind::PlaceTypeAscription { source, .. }
        | thir::ExprKind::ValueTypeAscription { source, .. } => {
            compile_expr(env, generics, thir, source)
        }
        thir::ExprKind::Closure(closure) => {
            let rustc_middle::thir::ClosureExpr { closure_id, .. } = closure.as_ref();
            let result = apply_on_thir(env, closure_id, |thir, expr_id| {
                let args: Vec<(Rc<Pattern>, Rc<CoqType>)> = thir
                    .params
                    .iter()
                    .filter_map(|param| match &param.pat {
                        Some(pattern) => {
                            let pattern =
                                crate::thir_pattern::compile_pattern(env, pattern.as_ref());
                            let ty = compile_type(env, generics, &param.ty);
                            Some((pattern, ty))
                        }
                        None => None,
                    })
                    .collect();
                let args = if args.is_empty() {
                    vec![(Rc::new(Pattern::Wild), CoqType::unit())]
                } else {
                    args
                };
                let body = compile_expr(env, generics, thir, expr_id).read();
                let body = args
                    .iter()
                    .enumerate()
                    .rfold(body, |body, (index, (pattern, _))| {
                        build_match(
                            Expr::local_var(&format!("α{index}")).alloc(),
                            vec![MatchArm {
                                pattern: pattern.clone(),
                                body,
                            }],
                        )
                    });
                let args = args
                    .iter()
                    .enumerate()
                    .map(|(index, (_, ty))| (format!("α{index}"), Some(ty.clone())))
                    .collect();

                Rc::new(Expr::Lambda {
                    args,
                    body,
                    is_internal: false,
                })
                .alloc()
            });

            match result {
                Ok(expr) => expr,
                Err(error) => Rc::new(Expr::Message(error)),
            }
        }
        thir::ExprKind::Literal { lit, neg } => match lit.node {
            rustc_ast::LitKind::Str(symbol, _) => {
                Rc::new(Expr::Literal(Rc::new(Literal::String(symbol.to_string()))))
            }
            rustc_ast::LitKind::Char(c) => {
                Rc::new(Expr::Literal(Rc::new(Literal::Char(c)))).alloc()
            }
            rustc_ast::LitKind::Int(i, _) => Rc::new(Expr::Literal(Rc::new(Literal::Integer(
                compile_literal_integer(env, &expr.span, &expr.ty, *neg, i),
            ))))
            .alloc(),
            rustc_ast::LitKind::Bool(c) => {
                Rc::new(Expr::Literal(Rc::new(Literal::Bool(c)))).alloc()
            }
            _ => Rc::new(Expr::Literal(Rc::new(Literal::Error))),
        },
        thir::ExprKind::NonHirLiteral { lit, .. } => Rc::new(Expr::Literal(Rc::new(
            Literal::Integer(compile_literal_integer(
                env,
                &expr.span,
                &expr.ty,
                false,
                lit.try_to_uint(lit.size()).unwrap(),
            )),
        )))
        .alloc(),
        thir::ExprKind::ZstLiteral { .. } => match &expr.ty.kind() {
            TyKind::FnDef(def_id, generic_args) => {
                let key = env.tcx.def_key(def_id);
                let symbol = key.get_opt_name();
                let parent = env.tcx.opt_parent(*def_id).unwrap();
                let parent_kind = env.tcx.def_kind(parent);

                Rc::new(match parent_kind {
                    DefKind::Impl { .. } => {
                        let parent_generics = env.tcx.generics_of(parent);
                        let nb_parent_generics = parent_generics.params.len();
                        let parent_type =
                            env.tcx.type_of(parent).instantiate(env.tcx, generic_args);
                        let ty = compile_type(env, generics, &parent_type);
                        let func = symbol.unwrap().to_string();
                        // We remove [nb_parent_generics] elements from the start of [generic_args]
                        // as these are already inferred from the `Self` type.
                        let generic_tys = generic_args
                            .iter()
                            .skip(nb_parent_generics)
                            .filter_map(|generic_arg| generic_arg
                                .as_type()
                                .as_ref()
                                .map(|ty| compile_type(env, generics, ty)))
                            .collect();

                        Expr::GetAssociatedFunction { ty, func, generic_tys }
                    }
                    DefKind::Trait => {
                        let parent_generics = env.tcx.generics_of(parent);
                        let nb_parent_generics = parent_generics.params.len();
                        let parent_path = compile_def_id(env, parent);
                        let self_ty_and_trait_tys = generic_args
                            .iter()
                            .take(nb_parent_generics)
                            .filter_map(|generic_arg| generic_arg
                                .as_type()
                                .as_ref()
                                .map(|ty| compile_type(env, generics, ty)))
                            .collect::<Vec<_>>();
                        let (self_ty, trait_tys) = match self_ty_and_trait_tys.as_slice() {
                            [self_ty, trait_tys @ ..] => (self_ty.clone(), trait_tys.to_vec()),
                            _ => panic!("Expected at least one element"),
                        };
                        let method_name = symbol.unwrap().to_string();
                        let generic_tys = generic_args
                            .iter()
                            .skip(nb_parent_generics)
                            .filter_map(|generic_arg| generic_arg
                                .as_type()
                                .as_ref()
                                .map(|ty| compile_type(env, generics, ty)))
                            .collect::<Vec<_>>();

                        Expr::GetTraitMethod {
                            trait_name: parent_path,
                            self_ty,
                            trait_tys,
                            method_name,
                            generic_tys,
                        }
                    }
                    DefKind::Mod | DefKind::ForeignMod => {
                        let generic_tys =
                            generic_args
                            .iter()
                            .filter_map(|generic_arg| {
                                generic_arg
                                    .as_type()
                                    .as_ref()
                                    .map(|ty| compile_type(env, generics, ty))
                            })
                            .collect::<Vec<_>>();

                        Expr::GetFunction {
                            func: compile_def_id(env, *def_id),
                            generic_tys,
                        }
                    }
                    DefKind::Variant => Expr::Constructor(compile_def_id(env, *def_id)),
                    DefKind::Struct => {
                        let path = compile_def_id(env, *def_id);

                        Expr::Call {
                            func: Expr::local_var("M.constructor_as_closure"),
                            args: vec![
                                Rc::new(Expr::InternalString(path.to_string())),
                            ],
                            kind: CallKind::Pure,
                        }
                    }
                    DefKind::AssocFn => {
                        let parent_symbol = env.tcx.def_key(parent).get_opt_name().unwrap();

                        Expr::GetAssociatedFunction {
                            ty: Rc::new(CoqType::Var("Self".to_string())),
                            func: format!("{}.{}", symbol.unwrap(), parent_symbol),
                            generic_tys: vec![],
                        }
                    }
                    DefKind::Fn => {
                        let parent_path = compile_def_id(env, parent);
                        let mut segments = parent_path.segments.clone();
                        let last_segment = segments.pop().unwrap();
                        segments.push(format!("{}.{}", last_segment, symbol.unwrap()));

                        Expr::GetFunction {
                            func: Path { segments },
                            generic_tys: vec![],
                        }
                    }
                    _ => {
                        emit_warning_with_note(
                            env,
                            &expr.span,
                            "We do not support this kind of expression",
                            &format!("Please report 🙏\n\nparent_kind: {parent_kind:#?}\nexpression: {expr:#?}"),
                        );

                        Expr::Message("unimplemented parent_kind".to_string())
                    }
                })
                .alloc()
            }
            _ => {
                let error_message = "Expected a function name";
                env.tcx
                    .sess
                    .struct_span_warn(expr.span, error_message)
                    .emit();

                Rc::new(Expr::Message(error_message.to_string()))
            }
        },
        thir::ExprKind::NamedConst { def_id, .. } => {
            let path = compile_def_id(env, *def_id);
            let expr = Rc::new(Expr::GetConst(path));
            let parent = env.tcx.opt_parent(*def_id).unwrap();
            let parent_kind = env.tcx.def_kind(parent);

            if matches!(parent_kind, DefKind::Variant) {
                return expr.alloc();
            }

            expr
        }
        thir::ExprKind::ConstParam { def_id, .. } => {
            Rc::new(Expr::GetConst(compile_def_id(env, *def_id)))
        }
        thir::ExprKind::StaticRef { def_id, .. } => {
            Rc::new(Expr::GetConst(compile_def_id(env, *def_id)))
        }
        thir::ExprKind::InlineAsm(_) => Rc::new(Expr::LocalVar("InlineAssembly".to_string())),
        thir::ExprKind::OffsetOf { .. } => Rc::new(Expr::LocalVar("OffsetOf".to_string())),
        thir::ExprKind::ThreadLocalRef(def_id) => {
            Rc::new(Expr::GetConst(compile_def_id(env, *def_id)))
        }
        thir::ExprKind::Yield { value } => {
            let func = Expr::local_var("yield");
            let args = vec![compile_expr(env, generics, thir, value)];

            Rc::new(Expr::Call {
                func,
                args,
                kind: CallKind::Effectful,
            })
        }
    }
}

fn compile_stmts<'a>(
    env: &Env<'a>,
    generics: &'a rustc_middle::ty::Generics,
    thir: &rustc_middle::thir::Thir<'a>,
    stmt_ids: &[rustc_middle::thir::StmtId],
    expr_id: Option<rustc_middle::thir::ExprId>,
) -> Rc<Expr> {
    stmt_ids.iter().rev().fold(
        {
            match &expr_id {
                Some(expr_id) => compile_expr(env, generics, thir, expr_id),
                None => Expr::tt(),
            }
        },
        |body, stmt_id| {
            let stmt = thir.stmts.get(*stmt_id).unwrap();
            match &stmt.kind {
                thir::StmtKind::Let {
                    pattern,
                    initializer,
                    ..
                } => {
                    let init = match initializer {
                        Some(initializer) => compile_expr(env, generics, thir, initializer),
                        None => Expr::local_var("Value.DeclaredButUndefined"),
                    };
                    let pattern = crate::thir_pattern::compile_pattern(env, pattern);

                    match pattern.as_ref() {
                        Pattern::Binding {
                            name,
                            pattern: None,
                            is_with_ref: false,
                        } => Rc::new(Expr::Let {
                            is_monadic: false,
                            name: Some(name.clone()),
                            init: init.copy(),
                            body,
                        }),
                        _ => build_match(init, vec![MatchArm { pattern, body }]),
                    }
                }
                thir::StmtKind::Expr { expr: expr_id, .. } => {
                    let init = compile_expr(env, generics, thir, expr_id);
                    let init_ty = &thir.exprs.get(*expr_id).unwrap().ty;
                    // Special case with the [never] type
                    if let TyKind::Never = init_ty.kind() {
                        return init;
                    }

                    Rc::new(Expr::Let {
                        is_monadic: false,
                        name: None,
                        init,
                        body,
                    })
                }
            }
        },
    )
}

fn compile_block<'a>(
    env: &Env<'a>,
    generics: &'a rustc_middle::ty::Generics,
    thir: &rustc_middle::thir::Thir<'a>,
    block_id: &rustc_middle::thir::BlockId,
) -> Rc<Expr> {
    let block = thir.blocks.get(*block_id).unwrap();

    compile_stmts(env, generics, thir, &block.stmts, block.expr)
}
