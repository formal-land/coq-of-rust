use crate::env::*;
use crate::expression::*;
use crate::path::*;
use crate::pattern::*;
use crate::thir_ty::*;
use crate::ty::CoqType;
use rustc_hir::def::DefKind;
use rustc_middle::mir::{BinOp, BorrowKind, UnOp};
use rustc_middle::thir;
use rustc_middle::thir::{AdtExpr, LogicalOp};
use rustc_middle::ty::TyKind;
use std::rc::Rc;

fn path_of_bin_op(
    bin_op: &BinOp,
    ty_left: &Rc<CoqType>,
    ty_right: &Rc<CoqType>,
) -> (&'static str, Purity) {
    match bin_op {
        BinOp::Add => ("BinOp.Panic.add", Purity::Effectful),
        BinOp::Sub => ("BinOp.Panic.sub", Purity::Effectful),
        BinOp::Mul => ("BinOp.Panic.mul", Purity::Effectful),
        BinOp::Div => ("BinOp.Panic.div", Purity::Effectful),
        BinOp::Rem => ("BinOp.Panic.rem", Purity::Effectful),
        BinOp::BitXor => ("BinOp.Pure.bit_xor", Purity::Pure),
        BinOp::BitAnd => ("BinOp.Pure.bit_and", Purity::Pure),
        BinOp::BitOr => ("BinOp.Pure.bit_or", Purity::Pure),
        BinOp::Shl => ("BinOp.Panic.shl", Purity::Effectful),
        BinOp::Shr => ("BinOp.Panic.shr", Purity::Effectful),
        BinOp::Eq => ("BinOp.Pure.eq", Purity::Pure),
        BinOp::Ne => ("BinOp.Pure.ne", Purity::Pure),
        BinOp::Lt => ("BinOp.Pure.lt", Purity::Pure),
        BinOp::Le => ("BinOp.Pure.le", Purity::Pure),
        BinOp::Ge => ("BinOp.Pure.ge", Purity::Pure),
        BinOp::Gt => ("BinOp.Pure.gt", Purity::Pure),
        BinOp::Offset => ("BinOp.Pure.offset", Purity::Pure),
        _ => todo!(),
    }
}

pub(crate) fn is_mutable_borrow_kind(borrow_kind: &BorrowKind) -> bool {
    match borrow_kind {
        BorrowKind::Shared => false,
        BorrowKind::Mut { .. } => true,
        BorrowKind::Fake => todo!(),
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
    let default_match_arm = Rc::new(MatchArm {
        pattern: Rc::new(Pattern::Wild),
        body: Rc::new(Expr::Call {
            func: Expr::local_var("M.break_match"),
            args: vec![],
            purity: Purity::Effectful,
            from_user: false,
        }),
    });

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
                init: match is_with_ref {
                    None => Expr::local_var(&scrutinee).copy(),
                    Some(is_with_ref) => {
                        let func = if *is_with_ref { "borrow_mut" } else { "borrow" };

                        Rc::new(Expr::Call {
                            func: Expr::local_var(func),
                            args: vec![Expr::local_var(&scrutinee)],
                            purity: Purity::Pure,
                            from_user: false,
                        })
                        .alloc()
                    }
                },
                body: match pattern {
                    None => body,
                    Some(pattern) => {
                        build_inner_match(vec![(scrutinee, pattern.clone())], body, depth + 1)
                    }
                },
            }),
            Pattern::StructStruct(path, fields, struct_or_variant) => Rc::new(Expr::Match {
                scrutinee: Expr::local_var(&scrutinee).read(),
                arms: [
                    vec![Rc::new(MatchArm {
                        pattern: Rc::new(Pattern::StructStruct(
                            path.clone(),
                            fields
                                .iter()
                                .map(|(field_name, _)| (field_name.clone(), Rc::new(Pattern::Wild)))
                                .collect(),
                            *struct_or_variant,
                        )),
                        body: {
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

                            fields.iter().enumerate().rfold(
                                body,
                                |body, (index, (field_name, _))| {
                                    let getter_path = match struct_or_variant {
                                        StructOrVariant::Struct => Path::concat(&[
                                            path.clone(),
                                            Path::new(&[format!("Get_{field_name}")]),
                                        ]),
                                        StructOrVariant::Variant { .. } => Path::concat(&[
                                            Path::new(&path.segments[0..path.segments.len() - 1]),
                                            Path::new(&[format!(
                                                "Get_{variant}_{field_name}",
                                                variant = path.segments.last().unwrap()
                                            )]),
                                        ]),
                                    };

                                    Rc::new(Expr::Let {
                                        is_monadic: false,
                                        name: Some(format!("γ{depth}_{index}")),
                                        init: Rc::new(Expr::Call {
                                            func: Rc::new(Expr::Var(getter_path)),
                                            args: vec![Expr::local_var(&scrutinee)],
                                            purity: Purity::Pure,
                                            from_user: false,
                                        }),
                                        body,
                                    })
                                },
                            )
                        },
                    })],
                    match struct_or_variant {
                        StructOrVariant::Struct | StructOrVariant::Variant { nb_cases: 1 } => {
                            vec![]
                        }
                        StructOrVariant::Variant { .. } => vec![default_match_arm.clone()],
                    },
                ]
                .concat(),
            }),
            Pattern::StructTuple(path, patterns, struct_or_variant) => Rc::new(Expr::Match {
                scrutinee: Expr::local_var(&scrutinee).read(),
                arms: [
                    vec![Rc::new(MatchArm {
                        pattern: Rc::new(Pattern::StructTuple(
                            path.clone(),
                            patterns.iter().map(|_| Rc::new(Pattern::Wild)).collect(),
                            *struct_or_variant,
                        )),
                        body: {
                            let body = build_inner_match(
                                patterns
                                    .iter()
                                    .enumerate()
                                    .map(|(index, pattern)| {
                                        (format!("γ{depth}_{index}"), pattern.clone())
                                    })
                                    .collect(),
                                body,
                                depth + 1,
                            );

                            patterns.iter().enumerate().rfold(body, |body, (index, _)| {
                                let getter_path = match struct_or_variant {
                                    StructOrVariant::Struct => Path::concat(&[
                                        path.clone(),
                                        Path::new(&[format!("Get_{index}")]),
                                    ]),
                                    StructOrVariant::Variant { .. } => Path::concat(&[
                                        Path::new(&path.segments[0..path.segments.len() - 1]),
                                        Path::new(&[format!(
                                            "Get_{variant}_{index}",
                                            variant = path.segments.last().unwrap(),
                                        )]),
                                    ]),
                                };

                                Rc::new(Expr::Let {
                                    is_monadic: false,
                                    name: Some(format!("γ{depth}_{index}")),
                                    init: Rc::new(Expr::Call {
                                        func: Rc::new(Expr::Var(getter_path)),
                                        args: vec![Expr::local_var(&scrutinee)],
                                        purity: Purity::Pure,
                                        from_user: false,
                                    }),
                                    body,
                                })
                            })
                        },
                    })],
                    match struct_or_variant {
                        StructOrVariant::Struct | StructOrVariant::Variant { nb_cases: 1 } => {
                            vec![]
                        }
                        StructOrVariant::Variant { .. } => vec![default_match_arm.clone()],
                    },
                ]
                .concat(),
            }),
            Pattern::Deref(pattern) => Rc::new(Expr::Let {
                is_monadic: false,
                name: Some(scrutinee.clone()),
                init: Rc::new(Expr::Call {
                    func: Expr::local_var("deref"),
                    args: vec![Expr::local_var(&scrutinee).read()],
                    purity: Purity::Pure,
                    from_user: false,
                }),
                body: build_inner_match(
                    vec![(scrutinee.clone(), pattern.clone())],
                    body,
                    depth + 1,
                ),
            }),
            Pattern::Or(_) => panic!("Or pattern should have been flattened"),
            Pattern::Tuple(patterns) => Rc::new(Expr::Match {
                scrutinee: Expr::local_var(&scrutinee).read(),
                arms: vec![Rc::new(MatchArm {
                    pattern: Rc::new(Pattern::Tuple(
                        patterns.iter().map(|_| Rc::new(Pattern::Wild)).collect(),
                    )),
                    body: {
                        let body = build_inner_match(
                            patterns
                                .iter()
                                .enumerate()
                                .map(|(index, pattern)| {
                                    (format!("γ{depth}_{index}"), pattern.clone())
                                })
                                .collect(),
                            body,
                            depth + 1,
                        );

                        patterns.iter().enumerate().rfold(body, |body, (index, _)| {
                            Rc::new(Expr::Let {
                                is_monadic: false,
                                name: Some(format!("γ{depth}_{index}")),
                                init: {
                                    let init = (0..(patterns.len() - 1 - index)).fold(
                                        Expr::local_var(&scrutinee),
                                        |init, _| {
                                            Rc::new(Expr::Call {
                                                func: Expr::local_var("Tuple.Access.left"),
                                                args: vec![init],
                                                purity: Purity::Pure,
                                                from_user: false,
                                            })
                                        },
                                    );

                                    if index == 0 {
                                        init
                                    } else {
                                        Rc::new(Expr::Call {
                                            func: Expr::local_var("Tuple.Access.right"),
                                            args: vec![init],
                                            purity: Purity::Pure,
                                            from_user: false,
                                        })
                                    }
                                },
                                body,
                            })
                        })
                    },
                })],
            }),
            Pattern::Lit(_) => Rc::new(Expr::Match {
                scrutinee: Expr::local_var(&scrutinee).read(),
                arms: vec![
                    Rc::new(MatchArm {
                        pattern: pattern.clone(),
                        body,
                    }),
                    default_match_arm.clone(),
                ],
            }),
            Pattern::Slice {
                init_patterns,
                slice_pattern,
            } => Rc::new(Expr::Match {
                scrutinee: Expr::local_var(&scrutinee).read(),
                arms: vec![
                    Rc::new(MatchArm {
                        pattern: Rc::new(Pattern::Slice {
                            init_patterns: init_patterns
                                .iter()
                                .map(|_| Rc::new(Pattern::Wild))
                                .collect(),
                            slice_pattern: slice_pattern.as_ref().map(|_| Rc::new(Pattern::Wild)),
                        }),
                        body: {
                            let body = build_inner_match(
                                [
                                    init_patterns
                                        .iter()
                                        .enumerate()
                                        .map(|(index, pattern)| {
                                            (format!("γ{depth}_{index}"), pattern.clone())
                                        })
                                        .collect(),
                                    match slice_pattern {
                                        None => vec![],
                                        Some(slice_pattern) => {
                                            vec![(format!("γ{depth}_slice"), slice_pattern.clone())]
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
                                    name: Some(format!("γ{depth}_slice")),
                                    init: Rc::new(Expr::Call {
                                        func: Expr::local_var(&format!(
                                            "[{}].slice",
                                            init_patterns.len()
                                        )),
                                        args: vec![Expr::local_var(&scrutinee)],
                                        purity: Purity::Pure,
                                        from_user: false,
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
                                            func: Expr::local_var(&format!("[{index}]")),
                                            args: vec![Expr::local_var(&scrutinee)],
                                            purity: Purity::Pure,
                                            from_user: false,
                                        }),
                                        body,
                                    })
                                })
                        },
                    }),
                    default_match_arm.clone(),
                ],
            }),
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
                            is_for_match: true,
                        })
                    })
                    .collect(),
            }),
        ],
        purity: Purity::Effectful,
        from_user: false,
    })
}

fn get_let_if<'a>(
    env: &Env<'a>,
    thir: &rustc_middle::thir::Thir<'a>,
    expr_id: &rustc_middle::thir::ExprId,
) -> Option<(Rc<Pattern>, Rc<Expr>)> {
    let expr = thir.exprs.get(*expr_id).unwrap();

    match &expr.kind {
        thir::ExprKind::Scope { value, .. } => get_let_if(env, thir, value),
        thir::ExprKind::Let { expr, pat, .. } => Some((
            crate::thir_pattern::compile_pattern(env, pat),
            compile_expr(env, thir, expr),
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
            emit_warning_with_note(
                env,
                span,
                "Unknown integer type",
                "Please report the error!",
            );

            "unknown_kind_of_integer".to_string()
        }
    };
    let name = uncapitalized_name
        .chars()
        .next()
        .unwrap()
        .to_uppercase()
        .collect::<String>()
        + &uncapitalized_name[1..];

    LiteralInteger {
        name,
        negative_sign,
        value: integer,
    }
}

pub(crate) fn compile_expr<'a>(
    env: &Env<'a>,
    thir: &rustc_middle::thir::Thir<'a>,
    expr_id: &rustc_middle::thir::ExprId,
) -> Rc<Expr> {
    let expr = thir.exprs.get(*expr_id).unwrap();
    let ty = compile_type(env, &expr.ty);

    match &expr.kind {
        thir::ExprKind::Scope { value, .. } => compile_expr(env, thir, value),
        thir::ExprKind::Box { value } => {
            let value_ty = compile_type(env, &thir.exprs.get(*value).unwrap().ty);
            let value = compile_expr(env, thir, value);

            Rc::new(Expr::Call {
                func: Rc::new(Expr::AssociatedFunction {
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
                }),
                args: vec![value],
                purity: Purity::Effectful,
                from_user: true,
            })
        }
        thir::ExprKind::If {
            cond,
            then,
            else_opt,
            ..
        } => {
            let success = compile_expr(env, thir, then);
            let failure = match else_opt {
                Some(else_expr) => compile_expr(env, thir, else_expr),
                None => Expr::tt(),
            };

            if let Some((pattern, expr)) = get_let_if(env, thir, cond) {
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

            let condition = compile_expr(env, thir, cond).read();

            Rc::new(Expr::If {
                condition,
                success,
                failure,
            })
        }
        thir::ExprKind::Call { fun, args, .. } => {
            let args = args
                .iter()
                .map(|arg| compile_expr(env, thir, arg).read())
                .collect();
            let func = compile_expr(env, thir, fun);
            let (purity, from_user) = {
                let default = (Purity::Effectful, true);

                match func.match_simple_call(&["M.alloc"]).as_ref() {
                    Some(expr) => match expr.as_ref() {
                        Expr::Constructor(_) => (Purity::Pure, false),
                        _ => default,
                    },
                    _ => default,
                }
            };
            let func = func.read();

            Rc::new(Expr::Call {
                func,
                args,
                purity,
                from_user,
            })
            .alloc()
        }
        thir::ExprKind::Deref { arg } => compile_expr(env, thir, arg).read(),
        thir::ExprKind::Binary { op, lhs, rhs } => {
            let left_ty = compile_type(env, &thir.exprs.get(*lhs).unwrap().ty);
            let right_ty = compile_type(env, &thir.exprs.get(*rhs).unwrap().ty);
            let (path, purity) = path_of_bin_op(op, &left_ty, &right_ty);
            let lhs = compile_expr(env, thir, lhs);
            let rhs = compile_expr(env, thir, rhs);

            Rc::new(Expr::Call {
                func: Expr::local_var(path),
                args: vec![lhs.read(), rhs.read()],
                purity,
                from_user: false,
            })
            .alloc()
        }
        thir::ExprKind::LogicalOp { op, lhs, rhs } => {
            let path = match op {
                LogicalOp::And => "BinOp.Pure.and",
                LogicalOp::Or => "BinOp.Pure.or",
            };
            let lhs = compile_expr(env, thir, lhs);
            let rhs = compile_expr(env, thir, rhs);

            Rc::new(Expr::Call {
                func: Expr::local_var(path),
                args: vec![lhs.read(), rhs.read()],
                purity: Purity::Pure,
                from_user: false,
            })
            .alloc()
        }
        thir::ExprKind::Unary { op, arg } => {
            let (path, purity) = match op {
                UnOp::Not => ("UnOp.not", Purity::Pure),
                UnOp::Neg => ("UnOp.neg", Purity::Effectful),
            };
            let arg = compile_expr(env, thir, arg);

            Rc::new(Expr::Call {
                func: Expr::local_var(path),
                args: vec![arg.read()],
                purity,
                from_user: false,
            })
            .alloc()
        }
        thir::ExprKind::Cast { source } => {
            let func = Expr::local_var("M.rust_cast");
            let source = compile_expr(env, thir, source);

            Rc::new(Expr::Call {
                func,
                args: vec![source.read()],
                purity: Purity::Pure,
                from_user: false,
            })
            .alloc()
        }
        thir::ExprKind::Use { source } => {
            let source = compile_expr(env, thir, source);

            Rc::new(Expr::Use(source))
        }
        thir::ExprKind::NeverToAny { source } => {
            let func = Expr::local_var("M.never_to_any");
            let source = compile_expr(env, thir, source);

            Rc::new(Expr::Call {
                func,
                args: vec![source.read()],
                purity: Purity::Effectful,
                from_user: false,
            })
            .alloc()
        }
        thir::ExprKind::PointerCoercion { source, cast } => {
            let func = Expr::local_var("M.pointer_coercion");
            let source = compile_expr(env, thir, source).read();
            let cast = Rc::new(Expr::Message(format!("{cast:?}")));

            Rc::new(Expr::Call {
                func,
                args: vec![cast, source],
                purity: Purity::Pure,
                from_user: false,
            })
            .alloc()
        }
        thir::ExprKind::Loop { body, .. } => {
            let body = compile_expr(env, thir, body);

            Rc::new(Expr::Loop { body })
        }
        thir::ExprKind::Let { .. } => {
            Rc::new(Expr::Message("`if let` expected into an `if`".to_string()))
        }
        thir::ExprKind::Match {
            scrutinee, arms, ..
        } => {
            let scrutinee = compile_expr(env, thir, scrutinee);
            let arms: Vec<MatchArm> = arms
                .iter()
                .map(|arm_id| {
                    let arm = thir.arms.get(*arm_id).unwrap();
                    let pattern = crate::thir_pattern::compile_pattern(env, &arm.pattern);
                    let body = compile_expr(env, thir, &arm.body);
                    MatchArm { pattern, body }
                })
                .collect();

            build_match(scrutinee, arms)
        }
        thir::ExprKind::Block { block: block_id } => compile_block(env, thir, block_id),
        thir::ExprKind::Assign { lhs, rhs } => {
            let func = Expr::local_var("M.assign");
            let args = vec![
                compile_expr(env, thir, lhs),
                compile_expr(env, thir, rhs).read(),
            ];

            Rc::new(Expr::Call {
                func,
                args,
                purity: Purity::Effectful,
                from_user: false,
            })
        }
        thir::ExprKind::AssignOp { op, lhs, rhs } => {
            let left_ty = compile_type(env, &thir.exprs.get(*lhs).unwrap().ty);
            let right_ty = compile_type(env, &thir.exprs.get(*rhs).unwrap().ty);
            let (path, purity) = path_of_bin_op(op, &left_ty, &right_ty);
            let lhs = compile_expr(env, thir, lhs);
            let rhs = compile_expr(env, thir, rhs);

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
                            purity,
                            from_user: false,
                        }),
                    ],
                    purity: Purity::Effectful,
                    from_user: false,
                }),
            })
        }
        thir::ExprKind::Field {
            lhs,
            variant_index,
            name,
        } => {
            let base = compile_expr(env, thir, lhs);
            let ty = thir.exprs.get(*lhs).unwrap().ty;

            match ty.ty_adt_def() {
                Some(adt_def) => {
                    let variant = adt_def.variant(*variant_index);
                    let name = variant.fields.get(*name).unwrap().name.to_string();
                    let is_name_a_number = name.chars().all(|c| c.is_ascii_digit());
                    let getter_name = if is_name_a_number {
                        "M.get_struct_tuple"
                    } else {
                        "M.get_struct_record"
                    };
                    let name_as_index = if is_name_a_number {
                        name
                    } else {
                        format!("\"{name}\"")
                    };
                    let index = Expr::local_var(&name_as_index);

                    Rc::new(Expr::Call {
                        func: Expr::local_var(getter_name),
                        args: vec![base, index],
                        purity: Purity::Pure,
                        from_user: false,
                    })
                }
                None => {
                    emit_warning_with_note(
                        env,
                        &expr.span,
                        "Unknown Field",
                        "Please report the error!",
                    );

                    Rc::new(Expr::Message("Unknown Field".to_string()))
                }
            }
        }
        thir::ExprKind::Index { lhs, index } => {
            let base = compile_expr(env, thir, lhs);
            let index = compile_expr(env, thir, index);

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
        | thir::ExprKind::AddressOf { mutability: _, arg } => compile_expr(env, thir, arg).alloc(),
        thir::ExprKind::Break { .. } => Rc::new(Expr::ControlFlow(LoopControlFlow::Break)),
        thir::ExprKind::Continue { .. } => Rc::new(Expr::ControlFlow(LoopControlFlow::Continue)),
        thir::ExprKind::Return { value } => {
            let value = match value {
                Some(value) => compile_expr(env, thir, value).read(),
                None => Expr::tt().read(),
            };

            Rc::new(Expr::Return(value))
        }
        rustc_middle::thir::ExprKind::Become { value } => {
            let value = compile_expr(env, thir, value).read();

            Rc::new(Expr::Return(value))
        }
        thir::ExprKind::ConstBlock { did, .. } => Rc::new(Expr::Var(compile_def_id(env, *did))),
        thir::ExprKind::Repeat { value, count } => {
            let func = Expr::local_var("repeat");
            let args = vec![
                compile_expr(env, thir, value).read(),
                Expr::local_var(&count.to_string()),
            ];

            Rc::new(Expr::Call {
                func,
                args,
                purity: Purity::Pure,
                from_user: false,
            })
            .alloc()
        }
        thir::ExprKind::Array { fields } => Rc::new(Expr::Array {
            elements: fields
                .iter()
                .map(|field| compile_expr(env, thir, field).read())
                .collect(),
        })
        .alloc(),
        thir::ExprKind::Tuple { fields } => {
            let elements: Vec<_> = fields
                .iter()
                .map(|field| compile_expr(env, thir, field).read())
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
                        compile_expr(env, thir, &field.expr).read(),
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
                .map(|base| compile_expr(env, thir, &base.base).read());

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
        | thir::ExprKind::ValueTypeAscription { source, .. } => compile_expr(env, thir, source),
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
                            let ty = compile_type(env, &param.ty);
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
                let body = compile_expr(env, thir, expr_id).read();
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
                    is_for_match: false,
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
                Rc::new(Expr::Literal(Literal::String(symbol.to_string())))
            }
            rustc_ast::LitKind::Char(c) => Rc::new(Expr::Literal(Literal::Char(c))).alloc(),
            rustc_ast::LitKind::Int(i, _) => Rc::new(Expr::Literal(Literal::Integer(
                compile_literal_integer(env, &expr.span, &expr.ty, *neg, i),
            )))
            .alloc(),
            rustc_ast::LitKind::Bool(c) => Rc::new(Expr::Literal(Literal::Bool(c))).alloc(),
            _ => Rc::new(Expr::Literal(Literal::Error)),
        },
        thir::ExprKind::NonHirLiteral { lit, .. } => {
            Rc::new(Expr::Literal(Literal::Integer(compile_literal_integer(
                env,
                &expr.span,
                &expr.ty,
                false,
                lit.try_to_uint(lit.size()).unwrap(),
            ))))
            .alloc()
        }
        thir::ExprKind::ZstLiteral { .. } => match &expr.ty.kind() {
            TyKind::FnDef(def_id, generic_args) => {
                let key = env.tcx.def_key(def_id);
                let symbol = key.get_opt_name();
                let parent = env.tcx.opt_parent(*def_id).unwrap();
                let parent_kind = env.tcx.def_kind(parent);
                Rc::new(match parent_kind {
                    DefKind::Impl { .. } => {
                        let parent_type =
                            env.tcx.type_of(parent).instantiate(env.tcx, generic_args);
                        let ty = compile_type(env, &parent_type);
                        let func = symbol.unwrap().to_string();
                        Expr::AssociatedFunction { ty, func }
                    }
                    DefKind::Trait => {
                        let generics = env.tcx.generics_of(def_id);
                        let parent_path = compile_def_id(env, parent);
                        let path = Path::concat(&[
                            parent_path.clone(),
                            Path::local(symbol.unwrap().as_str()),
                        ]);
                        let parent_generics = env.tcx.generics_of(parent);
                        let tys = [
                            parent_generics
                                .params
                                .iter()
                                .map(|param| param.name.to_string())
                                .collect::<Vec<_>>(),
                            generics
                                .params
                                .iter()
                                .map(|param| param.name.to_string())
                                .collect::<Vec<_>>(),
                        ]
                        .concat()
                        .into_iter()
                        .zip(generic_args.iter())
                        .filter_map(|(param, generic_arg)| {
                            generic_arg
                                .as_type()
                                .as_ref()
                                .map(|ty| (param, compile_type(env, ty)))
                        })
                        .collect::<Vec<_>>();
                        // We know that the first type is the `Self` type
                        let self_ty = &tys.first().unwrap().1;

                        Expr::TraitMethod {
                            trait_name: parent_path,
                            method_name: symbol.unwrap().to_string(),
                            self_and_generic_tys: tys,
                        }
                    }
                    DefKind::Mod | DefKind::ForeignMod => {
                        Expr::GetFunction(compile_def_id(env, *def_id))
                    }
                    DefKind::Variant => Expr::Constructor(compile_def_id(env, *def_id)),
                    DefKind::Struct => {
                        let mut segments = compile_def_id(env, *def_id).segments;
                        segments.push("Build_t".to_string());

                        Expr::Lambda {
                            args: vec![("α".to_string(), None)],
                            body: Rc::new(Expr::Call {
                                func: Rc::new(Expr::Constructor(Path { segments })),
                                args: vec![Expr::local_var("α")],
                                purity: Purity::Pure,
                                from_user: false,
                            }),
                            is_for_match: false,
                        }
                    }
                    _ => {
                        eprintln!("unimplemented parent_kind: {:#?}", parent_kind);
                        eprintln!("expression: {:#?}", expr);

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
            let expr = Rc::new(Expr::Var(path));
            let parent = env.tcx.opt_parent(*def_id).unwrap();
            let parent_kind = env.tcx.def_kind(parent);

            if matches!(parent_kind, DefKind::Variant) {
                return expr.alloc();
            }

            expr
        }
        thir::ExprKind::ConstParam { def_id, .. } => {
            Rc::new(Expr::Var(compile_def_id(env, *def_id)))
        }
        thir::ExprKind::StaticRef { def_id, .. } => {
            Rc::new(Expr::Var(compile_def_id(env, *def_id)))
        }
        thir::ExprKind::InlineAsm(_) => Rc::new(Expr::LocalVar("InlineAssembly".to_string())),
        thir::ExprKind::OffsetOf { .. } => Rc::new(Expr::LocalVar("OffsetOf".to_string())),
        thir::ExprKind::ThreadLocalRef(def_id) => Rc::new(Expr::Var(compile_def_id(env, *def_id))),
        thir::ExprKind::Yield { value } => {
            let func = Expr::local_var("yield");
            let args = vec![compile_expr(env, thir, value)];
            Rc::new(Expr::Call {
                func,
                args,
                purity: Purity::Effectful,
                from_user: false,
            })
        }
    }
}

fn compile_stmts<'a>(
    env: &Env<'a>,
    thir: &rustc_middle::thir::Thir<'a>,
    stmt_ids: &[rustc_middle::thir::StmtId],
    expr_id: Option<rustc_middle::thir::ExprId>,
) -> Rc<Expr> {
    stmt_ids.iter().rev().fold(
        {
            match &expr_id {
                Some(expr_id) => compile_expr(env, thir, expr_id),
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
                        Some(initializer) => compile_expr(env, thir, initializer),
                        None => Expr::local_var("Value.DeclaredButUndefined"),
                    };
                    let pattern = crate::thir_pattern::compile_pattern(env, pattern);

                    match pattern.as_ref() {
                        Pattern::Binding {
                            name,
                            pattern: None,
                            is_with_ref: None,
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
                    let init = compile_expr(env, thir, expr_id);
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
    thir: &rustc_middle::thir::Thir<'a>,
    block_id: &rustc_middle::thir::BlockId,
) -> Rc<Expr> {
    let block = thir.blocks.get(*block_id).unwrap();
    compile_stmts(env, thir, &block.stmts, block.expr)
}
