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
use rustc_middle::ty::{Const, ConstKind, TyKind};
use std::rc::Rc;

fn path_and_ty_of_bin_op(bin_op: &BinOp, ty_lhs: Rc<CoqType>) -> (&'static str, Rc<CoqType>) {
    match bin_op {
        BinOp::Add => ("BinOp.Wrap.add", ty_lhs),
        BinOp::Sub => ("BinOp.Wrap.sub", ty_lhs),
        BinOp::Mul => ("BinOp.Wrap.mul", ty_lhs),
        BinOp::Div => ("BinOp.Wrap.div", ty_lhs),
        BinOp::Rem => ("BinOp.Wrap.rem", ty_lhs),
        BinOp::BitXor => ("BinOp.Wrap.bit_xor", ty_lhs),
        BinOp::BitAnd => ("BinOp.Wrap.bit_and", ty_lhs),
        BinOp::BitOr => ("BinOp.Wrap.bit_or", ty_lhs),
        BinOp::Shl => ("BinOp.Wrap.shl", ty_lhs),
        BinOp::Shr => ("BinOp.Wrap.shr", ty_lhs),
        BinOp::Eq => ("BinOp.eq", CoqType::path(&["bool"])),
        BinOp::Ne => ("BinOp.ne", CoqType::path(&["bool"])),
        BinOp::Lt => ("BinOp.lt", CoqType::path(&["bool"])),
        BinOp::Le => ("BinOp.le", CoqType::path(&["bool"])),
        BinOp::Ge => ("BinOp.ge", CoqType::path(&["bool"])),
        BinOp::Gt => ("BinOp.gt", CoqType::path(&["bool"])),
        BinOp::Offset => ("BinOp.Pure.offset", ty_lhs),
        _ => todo!(),
    }
}

pub(crate) fn allocate_bindings(bindings: &[(String, Rc<CoqType>)], body: Rc<Expr>) -> Rc<Expr> {
    bindings.iter().rfold(body, |body, (name, ty)| {
        Rc::new(Expr::Let {
            name: Some(name.clone()),
            ty: None,
            init: Expr::local_var(name).alloc(ty.clone()),
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
                ty,
                is_with_ref,
                pattern,
            } => Rc::new(Expr::Let {
                name: Some(name.clone()),
                ty: None,
                init: if *is_with_ref {
                    Expr::local_var(&scrutinee).alloc(ty.clone())
                } else {
                    Expr::local_var(&scrutinee).copy(ty.clone())
                },
                body: match pattern {
                    None => body,
                    Some(pattern) => {
                        build_inner_match(vec![(scrutinee, pattern.clone())], body, depth + 1)
                    }
                },
            }),
            Pattern::StructRecord(path, fields) => {
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
                            name: Some(format!("γ{depth}_{index}")),
                            ty: None,
                            init: Rc::new(Expr::Call {
                                func: Expr::local_var("M.SubPointer.get_struct_record_field"),
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
            Pattern::StructTuple(path, patterns) => {
                let body = build_inner_match(
                    patterns
                        .iter()
                        .enumerate()
                        .map(|(index, pattern)| (format!("γ{depth}_{index}"), pattern.clone()))
                        .collect(),
                    body,
                    depth + 1,
                );

                let body = patterns.iter().enumerate().rfold(body, |body, (index, _)| {
                    Rc::new(Expr::Let {
                        name: Some(format!("γ{depth}_{index}")),
                        ty: None,
                        init: Rc::new(Expr::Call {
                            func: Expr::local_var("M.SubPointer.get_struct_tuple_field"),
                            args: vec![
                                Expr::local_var(&scrutinee),
                                Rc::new(Expr::InternalString(path.to_string())),
                                Rc::new(Expr::InternalInteger(index)),
                            ],
                            kind: CallKind::Effectful,
                        }),
                        body,
                    })
                });

                // We add a test to cover the case where there are no parameters to the constructor,
                // but we still need to check that we have the right one.
                if patterns.is_empty() {
                    return Rc::new(Expr::Let {
                        name: None,
                        ty: None,
                        init: Rc::new(Expr::Call {
                            func: Expr::local_var("M.is_struct_tuple"),
                            args: vec![
                                Expr::local_var(&scrutinee),
                                Rc::new(Expr::InternalString(path.to_string())),
                            ],
                            kind: CallKind::Effectful,
                        }),
                        body,
                    });
                }

                body
            }
            Pattern::Deref(pattern) => Rc::new(Expr::Let {
                name: Some(scrutinee.clone()),
                ty: None,
                init: Expr::local_var(&scrutinee).read(),
                body: build_inner_match(
                    vec![(scrutinee.clone(), pattern.clone())],
                    body,
                    depth + 1,
                ),
            }),
            Pattern::Or(patterns) => match &patterns[..] {
                [] => Rc::new(Expr::Call {
                    func: Expr::local_var("M.break_match"),
                    args: vec![],
                    kind: CallKind::Effectful,
                }),
                [first_pattern, ..] => {
                    let free_vars = first_pattern.get_free_vars();
                    let free_vars_ty = Rc::new(CoqType::Tuple {
                        tys: free_vars.iter().map(|(_, ty)| ty.clone()).collect(),
                    });

                    Rc::new(Expr::Call {
                        kind: CallKind::Effectful,
                        func: Rc::new(Expr::CallTy {
                            func: Expr::local_var("M.find_or_pattern"),
                            ty: free_vars_ty.clone(),
                        }),
                        args: vec![
                            Expr::local_var(&scrutinee),
                            Rc::new(Expr::Array {
                                is_internal: true,
                                elements: patterns
                                    .iter()
                                    .map(|pattern| {
                                        Rc::new(Expr::Lambda {
                                            is_for_match: true,
                                            form: LambdaForm::Function,
                                            args: vec![("γ".to_string(), None)],
                                            body: build_inner_match(
                                                vec![("γ".to_string(), pattern.clone())],
                                                Rc::new(Expr::Tuple {
                                                    elements: free_vars
                                                        .iter()
                                                        .map(|(name, _)| Expr::local_var(name))
                                                        .collect(),
                                                }),
                                                0,
                                            ),
                                        })
                                    })
                                    .collect(),
                            }),
                            Rc::new(Expr::Lambda {
                                is_for_match: true,
                                form: LambdaForm::ListFunction,
                                args: free_vars
                                    .iter()
                                    .map(|(name, ty)| (name.clone(), Some(ty.clone())))
                                    .collect(),
                                body,
                            }),
                        ],
                    })
                }
            },
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
                        name: Some(format!("γ{depth}_{index}")),
                        ty: None,
                        init: Rc::new(Expr::Call {
                            func: Expr::local_var("M.SubPointer.get_tuple_field"),
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
            Pattern::Literal(literal) => Rc::new(Expr::Let {
                name: None,
                ty: None,
                init: Rc::new(Expr::Call {
                    func: Expr::local_var("is_constant_or_break_match"),
                    args: vec![
                        Expr::local_var(&scrutinee).read(),
                        Rc::new(Expr::Literal(literal.clone())),
                    ],
                    kind: CallKind::Effectful,
                }),
                body,
            }),
            Pattern::Slice {
                prefix_patterns,
                slice_pattern,
                suffix_patterns,
            } => {
                let body = build_inner_match(
                    [
                        prefix_patterns
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
                        suffix_patterns
                            .iter()
                            .enumerate()
                            .map(|(index, pattern)| {
                                (format!("γ{depth}_rev{index}"), pattern.clone())
                            })
                            .collect(),
                    ]
                    .concat(),
                    body,
                    depth + 1,
                );

                let body =
                    suffix_patterns
                        .iter()
                        .enumerate()
                        .rev()
                        .rfold(body, |body, (index, _)| {
                            Rc::new(Expr::Let {
                                name: Some(format!("γ{depth}_rev{index}")),
                                ty: None,
                                init: Rc::new(Expr::Call {
                                    func: Expr::local_var("M.SubPointer.get_slice_rev_index"),
                                    args: vec![
                                        Expr::local_var(&scrutinee),
                                        Rc::new(Expr::InternalInteger(index)),
                                    ],
                                    kind: CallKind::Effectful,
                                }),
                                body,
                            })
                        });

                let body = match slice_pattern {
                    None => body,
                    Some(_) => Rc::new(Expr::Let {
                        name: Some(format!("γ{depth}_rest")),
                        ty: None,
                        init: Rc::new(Expr::Call {
                            func: Expr::local_var("M.SubPointer.get_slice_rest"),
                            args: vec![
                                Expr::local_var(&scrutinee),
                                Rc::new(Expr::InternalInteger(prefix_patterns.len())),
                                Rc::new(Expr::InternalInteger(suffix_patterns.len())),
                            ],
                            kind: CallKind::Effectful,
                        }),
                        body,
                    }),
                };

                prefix_patterns
                    .iter()
                    .enumerate()
                    .rfold(body, |body, (index, _)| {
                        Rc::new(Expr::Let {
                            name: Some(format!("γ{depth}_{index}")),
                            ty: None,
                            init: Rc::new(Expr::Call {
                                func: Expr::local_var("M.SubPointer.get_slice_index"),
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

pub(crate) fn build_match(ty: Rc<CoqType>, scrutinee: Rc<Expr>, arms: Vec<MatchArm>) -> Rc<Expr> {
    Rc::new(Expr::Match {
        ty,
        scrutinee,
        arms: arms
            .into_iter()
            .map(
                |MatchArm {
                     pattern,
                     if_let_guard,
                     body,
                 }| {
                    let body = if_let_guard
                        .into_iter()
                        .rfold(body, |body, (pattern, guard)| {
                            Rc::new(Expr::Let {
                                name: Some("γ".to_string()),
                                ty: None,
                                init: guard,
                                body: build_inner_match(vec![("γ".to_string(), pattern)], body, 0),
                            })
                        });

                    Rc::new(Expr::Lambda {
                        is_for_match: true,
                        form: LambdaForm::Function,
                        args: vec![("γ".to_string(), None)],
                        body: build_inner_match(vec![("γ".to_string(), pattern)], body, 0),
                    })
                },
            )
            .collect(),
    })
}

/// In a `if` statement or the `if` guard of a pattern, we can have a list of conditions
/// separated by the `&&` operator. Each of these conditions can be an `if let` statement,
/// in that can we return the associated pattern. They can also be boolean expressions,
/// in that case we return the pattern `true`. This should be the most common case.
fn get_if_conditions<'a>(
    env: &Env<'a>,
    generics: &'a rustc_middle::ty::Generics,
    thir: &rustc_middle::thir::Thir<'a>,
    expr_id: &rustc_middle::thir::ExprId,
) -> Vec<(Rc<Pattern>, Rc<Expr>)> {
    let expr = thir.exprs.get(*expr_id).unwrap();

    match &expr.kind {
        thir::ExprKind::Scope { value, .. } => get_if_conditions(env, generics, thir, value),
        thir::ExprKind::Let { expr, pat, .. } => {
            let pattern = crate::thir_pattern::compile_pattern(env, generics, pat);
            let expr = compile_expr(env, generics, thir, expr);

            vec![(pattern, expr)]
        }
        thir::ExprKind::LogicalOp {
            op: LogicalOp::And,
            lhs,
            rhs,
        } => [
            get_if_conditions(env, generics, thir, lhs),
            get_if_conditions(env, generics, thir, rhs),
        ]
        .concat(),
        _ => {
            let true_pattern = Rc::new(Pattern::Literal(Rc::new(Literal::Bool(true))));
            let expr = compile_expr(env, generics, thir, expr_id);

            vec![(true_pattern, expr)]
        }
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
            emit_warning_with_note(env, span, "Unknown integer type", Some("Please report 🙏"));

            "unknown_kind_of_integer".to_string()
        }
    };
    let kind = capitalize(&uncapitalized_name);

    LiteralInteger {
        kind,
        negative_sign,
        value: integer,
    }
}

fn compile_pointer_coercion_safety(safety: &rustc_hir::Safety) -> PointerCoercionSafety {
    match safety {
        rustc_hir::Safety::Unsafe => PointerCoercionSafety::Unsafe,
        rustc_hir::Safety::Safe => PointerCoercionSafety::Safe,
    }
}

fn compile_pointer_coercion(
    coercion: &rustc_middle::ty::adjustment::PointerCoercion,
) -> PointerCoercion {
    match coercion {
        rustc_middle::ty::adjustment::PointerCoercion::ReifyFnPointer => {
            PointerCoercion::ReifyFnPointer
        }
        rustc_middle::ty::adjustment::PointerCoercion::UnsafeFnPointer => {
            PointerCoercion::UnsafeFnPointer
        }
        rustc_middle::ty::adjustment::PointerCoercion::ClosureFnPointer(safety) => {
            PointerCoercion::ClosureFnPointer(compile_pointer_coercion_safety(safety))
        }
        rustc_middle::ty::adjustment::PointerCoercion::MutToConstPointer => {
            PointerCoercion::MutToConstPointer
        }
        rustc_middle::ty::adjustment::PointerCoercion::ArrayToPointer => {
            PointerCoercion::ArrayToPointer
        }
        rustc_middle::ty::adjustment::PointerCoercion::Unsize => PointerCoercion::Unsize,
        rustc_middle::ty::adjustment::PointerCoercion::DynStar => PointerCoercion::DynStar,
    }
}

pub(crate) fn compile_expr<'a>(
    env: &Env<'a>,
    generics: &'a rustc_middle::ty::Generics,
    thir: &rustc_middle::thir::Thir<'a>,
    expr_id: &rustc_middle::thir::ExprId,
) -> Rc<Expr> {
    let expr = thir.exprs.get(*expr_id).unwrap();
    let ty = compile_type(env, &expr.span, generics, &expr.ty);

    match &expr.kind {
        thir::ExprKind::Scope { value, .. } => compile_expr(env, generics, thir, value),
        thir::ExprKind::Box { value } => {
            let value_ty = compile_type(
                env,
                &expr.span,
                generics,
                &thir.exprs.get(*value).unwrap().ty,
            );
            let value = compile_expr(env, generics, thir, value);
            let ty = Rc::new(CoqType::Application {
                func: Rc::new(CoqType::Path {
                    path: Path::new(&["alloc", "boxed", "Box"]),
                }),
                consts: vec![],
                tys: vec![
                    value_ty,
                    Rc::new(CoqType::Path {
                        path: Path::new(&["alloc", "alloc", "Global"]),
                    }),
                ],
            });

            Rc::new(Expr::Call {
                func: Rc::new(Expr::GetAssociatedFunction {
                    ty: ty.clone(),
                    func: "new".to_string(),
                    generic_consts: vec![],
                    generic_tys: vec![],
                }),
                args: vec![value],
                kind: CallKind::Closure(ty),
            })
        }
        thir::ExprKind::If {
            cond,
            then,
            else_opt,
            ..
        } => {
            let conditions = get_if_conditions(env, generics, thir, cond);
            let success = compile_expr(env, generics, thir, then);
            let failure = match else_opt {
                Some(else_expr) => compile_expr(env, generics, thir, else_expr),
                None => Expr::tt(),
            };

            build_match(
                ty.clone(),
                Expr::tt(),
                vec![
                    MatchArm {
                        pattern: Rc::new(Pattern::Wild),
                        if_let_guard: conditions,
                        body: success.read(),
                    },
                    MatchArm {
                        pattern: Rc::new(Pattern::Wild),
                        if_let_guard: vec![],
                        body: failure.read(),
                    },
                ],
            )
            .alloc(ty)
        }
        thir::ExprKind::Call { fun, args, .. } => {
            let args = args
                .iter()
                .map(|arg| compile_expr(env, generics, thir, arg).read())
                .collect();
            let func = compile_expr(env, generics, thir, fun);
            let func = func.read();

            Rc::new(Expr::Call {
                func,
                args,
                kind: CallKind::Closure(ty.clone()),
            })
            .alloc(ty)
        }
        thir::ExprKind::Deref { arg } => Rc::new(Expr::Call {
            func: Expr::local_var("M.deref"),
            args: vec![compile_expr(env, generics, thir, arg).read()],
            kind: CallKind::Effectful,
        }),
        thir::ExprKind::Binary { op, lhs, rhs } => {
            let lhs_expr = thir.exprs.get(*lhs).unwrap();
            let ty_lhs = compile_type(env, &lhs_expr.span, generics, &lhs_expr.ty);
            let (path, _) = path_and_ty_of_bin_op(op, ty_lhs);
            let lhs = compile_expr(env, generics, thir, lhs);
            let rhs = compile_expr(env, generics, thir, rhs);

            Rc::new(Expr::Call {
                func: Expr::local_var(path),
                args: vec![lhs.read(), rhs.read()],
                kind: CallKind::Closure(ty.clone()),
            })
            .alloc(ty)
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
            .alloc(ty)
        }
        thir::ExprKind::Unary { op, arg } => {
            let (path, kind) = match op {
                UnOp::Not => ("UnOp.not", CallKind::Effectful),
                UnOp::Neg => ("UnOp.neg", CallKind::Effectful),
                UnOp::PtrMetadata => ("UnOp.ptr_metadata", CallKind::Effectful),
            };
            let arg = compile_expr(env, generics, thir, arg);

            Rc::new(Expr::Call {
                func: Expr::local_var(path),
                args: vec![arg.read()],
                kind,
            })
            .alloc(ty)
        }
        thir::ExprKind::Cast { source } => {
            let source = compile_expr(env, generics, thir, source).read();
            let target_ty = compile_type(env, &expr.span, generics, &expr.ty);

            Rc::new(Expr::Cast { target_ty, source }).alloc(ty)
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
            .alloc(ty)
        }
        thir::ExprKind::PointerCoercion {
            source,
            cast,
            is_from_as_cast: _,
        } => {
            let coercion = compile_pointer_coercion(cast);
            let source_expr = thir.exprs.get(*source).unwrap();
            let source_ty = compile_type(env, &source_expr.span, generics, &source_expr.ty);
            let source = compile_expr(env, generics, thir, source).read();
            let func = Rc::new(Expr::PointerCoercion {
                coercion,
                source_ty,
                target_ty: ty.clone(),
            });

            Rc::new(Expr::Call {
                func,
                args: vec![source],
                kind: CallKind::Closure(ty.clone()),
            })
            .alloc(ty)
        }
        thir::ExprKind::Loop { body, .. } => {
            let body = compile_expr(env, generics, thir, body);

            Rc::new(Expr::Loop { ty, body })
        }
        thir::ExprKind::Let { .. } => {
            let error_message = "Unexpected `if let` outside of an `if`";

            emit_warning_with_note(env, &expr.span, error_message, Some("Please report!"));

            Rc::new(Expr::Comment(error_message.to_string(), Expr::tt())).alloc(ty)
        }
        thir::ExprKind::Match {
            scrutinee,
            scrutinee_hir_id: _,
            arms,
            match_source: _,
        } => {
            let scrutinee = compile_expr(env, generics, thir, scrutinee);
            let arms: Vec<MatchArm> = arms
                .iter()
                .map(|arm_id| {
                    let arm = thir.arms.get(*arm_id).unwrap();
                    let pattern = crate::thir_pattern::compile_pattern(env, generics, &arm.pattern);
                    let if_let_guard = match &arm.guard {
                        Some(expr_id) => get_if_conditions(env, generics, thir, expr_id),
                        None => vec![],
                    };
                    let body = compile_expr(env, generics, thir, &arm.body).read();

                    MatchArm {
                        pattern,
                        if_let_guard,
                        body,
                    }
                })
                .collect();

            build_match(ty.clone(), scrutinee, arms).alloc(ty)
        }
        thir::ExprKind::Block { block: block_id } => compile_block(env, generics, thir, block_id),
        thir::ExprKind::Assign { lhs, rhs } => {
            let func = Expr::local_var("M.write");
            let args = vec![
                compile_expr(env, generics, thir, lhs),
                compile_expr(env, generics, thir, rhs).read(),
            ];

            Rc::new(Expr::Call {
                func,
                args,
                kind: CallKind::Effectful,
            })
            .alloc(ty)
        }
        thir::ExprKind::AssignOp { op, lhs, rhs } => {
            let lhs_expr = thir.exprs.get(*lhs).unwrap();
            let ty_lhs = compile_type(env, &lhs_expr.span, generics, &lhs_expr.ty);
            let (path, result_ty) = path_and_ty_of_bin_op(op, ty_lhs);
            let lhs = compile_expr(env, generics, thir, lhs);
            let rhs = compile_expr(env, generics, thir, rhs);

            Rc::new(Expr::Let {
                name: Some("β".to_string()),
                ty: None,
                init: lhs,
                body: Rc::new(Expr::Call {
                    func: Expr::local_var("M.write"),
                    args: vec![
                        Expr::local_var("β"),
                        Rc::new(Expr::Call {
                            func: Expr::local_var(path),
                            args: vec![Expr::local_var("β").read(), rhs.read()],
                            kind: CallKind::Closure(result_ty),
                        }),
                    ],
                    kind: CallKind::Effectful,
                }),
            })
            .alloc(ty)
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
                        "M.SubPointer.get_struct_tuple_field"
                    } else {
                        "M.SubPointer.get_struct_record_field"
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
                        kind: CallKind::Effectful,
                    })
                }
                None => {
                    // We assume that we are in the case of a tuple.
                    Rc::new(Expr::Call {
                        func: Expr::local_var("M.SubPointer.get_tuple_field"),
                        args: vec![base, Rc::new(Expr::InternalInteger(name.as_usize()))],
                        kind: CallKind::Effectful,
                    })
                }
            }
        }
        thir::ExprKind::Index { lhs, index } => {
            let base = compile_expr(env, generics, thir, lhs);
            let index = compile_expr(env, generics, thir, index).read();

            Rc::new(Expr::Index { base, index })
        }
        thir::ExprKind::VarRef { id } => {
            let name =
                to_valid_coq_name(IsValue::Yes, env.tcx.hir().opt_name(id.0).unwrap().as_str());

            Rc::new(Expr::LocalVar(name))
        }
        thir::ExprKind::UpvarRef { var_hir_id, .. } => {
            let name = to_valid_coq_name(
                IsValue::Yes,
                env.tcx.hir().opt_name(var_hir_id.0).unwrap().as_str(),
            );

            Rc::new(Expr::LocalVar(name))
        }
        thir::ExprKind::Borrow { borrow_kind, arg } => Rc::new(Expr::Call {
            func: Expr::local_var("M.borrow"),
            args: vec![
                Expr::local_var(
                    if matches!(borrow_kind, rustc_middle::mir::BorrowKind::Mut { .. }) {
                        "Pointer.Kind.MutRef"
                    } else {
                        "Pointer.Kind.Ref"
                    },
                ),
                compile_expr(env, generics, thir, arg),
            ],
            kind: CallKind::Effectful,
        })
        .alloc(ty),
        thir::ExprKind::RawBorrow { mutability, arg } => Rc::new(Expr::Call {
            func: Expr::local_var("M.borrow"),
            args: vec![
                Expr::local_var(
                    if matches!(mutability, rustc_middle::mir::Mutability::Mut) {
                        "Pointer.Kind.MutPointer"
                    } else {
                        "Pointer.Kind.ConstPointer"
                    },
                ),
                compile_expr(env, generics, thir, arg),
            ],
            kind: CallKind::Effectful,
        })
        .alloc(ty),
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
            let return_ty = compile_type(env, &expr.span, generics, &expr.ty);

            Rc::new(Expr::GetConstant {
                path: compile_def_id(env, *did),
                return_ty,
            })
        }
        thir::ExprKind::Repeat { value, count } => {
            let func = Expr::local_var("lib.repeat");
            let args = vec![
                compile_expr(env, generics, thir, value).read(),
                compile_const(env, &expr.span, count),
            ];

            Rc::new(Expr::Call {
                func,
                args,
                kind: CallKind::Effectful,
            })
            .alloc(ty)
        }
        thir::ExprKind::Array { fields } => Rc::new(Expr::Array {
            elements: fields
                .iter()
                .map(|field| compile_expr(env, generics, thir, field).read())
                .collect(),
            is_internal: false,
        })
        .alloc(ty),
        thir::ExprKind::Tuple { fields } => {
            let elements: Vec<_> = fields
                .iter()
                .map(|field| compile_expr(env, generics, thir, field).read())
                .collect();
            if elements.is_empty() {
                Expr::tt()
            } else {
                Rc::new(Expr::Tuple { elements }).alloc(ty)
            }
        }
        thir::ExprKind::Adt(adt_expr) => {
            let (arg_consts, arg_tys) = match ty.as_ref() {
                CoqType::Application {
                    func: _,
                    consts,
                    tys,
                } => (consts.clone(), tys.clone()),
                _ => (vec![], vec![]),
            };
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
                        to_valid_coq_name(
                            IsValue::No,
                            variant.fields.get(field.name).unwrap().name.as_str(),
                        ),
                        compile_expr(env, generics, thir, &field.expr).read(),
                    )
                })
                .collect();
            let is_a_tuple = !fields.is_empty()
                && fields
                    .iter()
                    .all(|(name, _)| name.starts_with(|c: char| c.is_ascii_digit()));
            let base = base
                .as_ref()
                .map(|base| compile_expr(env, generics, thir, &base.base).read());

            if fields.is_empty() {
                return Rc::new(Expr::StructTuple {
                    path,
                    arg_consts,
                    arg_tys,
                    fields: vec![],
                })
                .alloc(ty);
            }

            if is_a_tuple {
                let fields = fields.into_iter().map(|(_, pattern)| pattern).collect();
                Rc::new(Expr::StructTuple {
                    path,
                    arg_consts,
                    arg_tys,
                    fields,
                })
                .alloc(ty)
            } else {
                Rc::new(Expr::StructStruct {
                    path,
                    arg_consts,
                    arg_tys,
                    fields,
                    base,
                })
                .alloc(ty)
            }
        }
        thir::ExprKind::PlaceTypeAscription { source, .. }
        | thir::ExprKind::ValueTypeAscription { source, .. } => {
            compile_expr(env, generics, thir, source)
        }
        thir::ExprKind::Closure(closure) => {
            let rustc_middle::thir::ClosureExpr { closure_id, .. } = closure.as_ref();
            let result = apply_on_thir(env, closure_id, |thir, body_id| {
                let args: Vec<(Rc<Pattern>, Rc<CoqType>)> = thir
                    .params
                    .iter()
                    .filter_map(|param| match &param.pat {
                        Some(pattern) => {
                            let pattern = crate::thir_pattern::compile_pattern(
                                env,
                                generics,
                                pattern.as_ref(),
                            );
                            let ty = compile_type(env, &expr.span, generics, &param.ty);
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
                let body = compile_expr(env, generics, thir, body_id).read();
                let body_expr = thir.exprs.get(*body_id).unwrap();
                let body_ty = compile_type(env, &body_expr.span, generics, &body_expr.ty);
                let body =
                    args.iter()
                        .enumerate()
                        .rfold(body, |body, (index, (pattern, pattern_ty))| {
                            build_match(
                                body_ty.clone(),
                                Expr::local_var(&format!("α{index}")).alloc(pattern_ty.clone()),
                                vec![MatchArm {
                                    pattern: pattern.clone(),
                                    if_let_guard: vec![],
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
                    form: LambdaForm::Closure,
                })
                .alloc(ty)
            });

            match result {
                Ok(expr) => expr,
                Err(error) => Rc::new(Expr::Comment(error, Expr::tt())).alloc(CoqType::unit()),
            }
        }
        thir::ExprKind::Literal { lit, neg } => match lit.node {
            rustc_ast::LitKind::Str(symbol, _) => {
                Rc::new(Expr::Literal(Rc::new(Literal::String(symbol.to_string())))).alloc(ty)
            }
            rustc_ast::LitKind::Char(c) => {
                Rc::new(Expr::Literal(Rc::new(Literal::Char(c)))).alloc(ty)
            }
            rustc_ast::LitKind::Int(i, _) => Rc::new(Expr::Literal(Rc::new(Literal::Integer(
                compile_literal_integer(env, &expr.span, &expr.ty, *neg, i.get()),
            ))))
            .alloc(ty),
            rustc_ast::LitKind::Bool(c) => {
                Rc::new(Expr::Literal(Rc::new(Literal::Bool(c)))).alloc(ty)
            }
            _ => Rc::new(Expr::Literal(Rc::new(Literal::Error))),
        },
        thir::ExprKind::NonHirLiteral { lit, .. } => {
            Rc::new(Expr::Literal(Rc::new(Literal::Integer(
                compile_literal_integer(env, &expr.span, &expr.ty, false, lit.to_uint(lit.size())),
            ))))
            .alloc(ty)
        }
        thir::ExprKind::ZstLiteral { .. } => {
            match &expr.ty.kind() {
                TyKind::FnDef(def_id, generic_args) => {
                    let key = env.tcx.def_key(def_id);
                    let symbol = key.get_opt_name();
                    let parent = env.tcx.opt_parent(*def_id).unwrap();
                    let parent_kind = env.tcx.def_kind(parent);

                    match parent_kind {
                        DefKind::Impl { .. } => {
                            let parent_generics = env.tcx.generics_of(parent);
                            let nb_parent_generics = parent_generics.own_params.len();
                            let parent_type =
                                env.tcx.type_of(parent).instantiate(env.tcx, generic_args);
                            let parent_ty = compile_type(env, &expr.span, generics, &parent_type);
                            let func = symbol.unwrap().to_string();
                            // We remove [nb_parent_generics] elements from the start of [generic_args]
                            // as these are already inferred from the `Self` type.
                            let generic_consts = generic_args
                                .iter()
                                .skip(nb_parent_generics)
                                .filter_map(|generic_arg| {
                                    generic_arg
                                        .as_const()
                                        .as_ref()
                                        .map(|ct| compile_const(env, &expr.span, ct))
                                })
                                .collect();
                            let generic_tys = generic_args
                                .iter()
                                .skip(nb_parent_generics)
                                .filter_map(|generic_arg| {
                                    generic_arg
                                        .as_type()
                                        .as_ref()
                                        .map(|ty| compile_type(env, &expr.span, generics, ty))
                                })
                                .collect();

                            Rc::new(Expr::GetAssociatedFunction {
                                ty: parent_ty,
                                func,
                                generic_consts,
                                generic_tys,
                            })
                            .alloc(ty)
                        }
                        DefKind::Trait => {
                            let parent_generics = env.tcx.generics_of(parent);
                            let nb_parent_generics = parent_generics.own_params.len();
                            let parent_path = compile_def_id(env, parent);
                            let self_ty_and_trait_tys = generic_args
                                .iter()
                                .take(nb_parent_generics)
                                .filter_map(|generic_arg| {
                                    generic_arg
                                        .as_type()
                                        .as_ref()
                                        .map(|ty| compile_type(env, &expr.span, generics, ty))
                                })
                                .collect::<Vec<_>>();
                            let (self_ty, trait_tys) = match self_ty_and_trait_tys.as_slice() {
                                [self_ty, trait_tys @ ..] => (self_ty.clone(), trait_tys.to_vec()),
                                _ => panic!("Expected at least one element"),
                            };
                            let trait_consts = generic_args
                                .iter()
                                .take(nb_parent_generics)
                                .filter_map(|generic_arg| {
                                    generic_arg
                                        .as_const()
                                        .as_ref()
                                        .map(|ct| compile_const(env, &expr.span, ct))
                                })
                                .collect::<Vec<_>>();
                            let method_name = symbol.unwrap().to_string();
                            let generic_consts = generic_args
                                .iter()
                                .skip(nb_parent_generics)
                                .filter_map(|generic_arg| {
                                    generic_arg
                                        .as_const()
                                        .as_ref()
                                        .map(|ct| compile_const(env, &expr.span, ct))
                                })
                                .collect::<Vec<_>>();
                            let generic_tys = generic_args
                                .iter()
                                .skip(nb_parent_generics)
                                .filter_map(|generic_arg| {
                                    generic_arg
                                        .as_type()
                                        .as_ref()
                                        .map(|ty| compile_type(env, &expr.span, generics, ty))
                                })
                                .collect::<Vec<_>>();

                            Rc::new(Expr::GetTraitMethod {
                                trait_name: parent_path,
                                self_ty,
                                trait_consts,
                                trait_tys,
                                method_name,
                                generic_consts,
                                generic_tys,
                            })
                            .alloc(ty)
                        }
                        DefKind::Mod | DefKind::ForeignMod => {
                            let generic_consts = generic_args
                                .iter()
                                .filter_map(|generic_arg| {
                                    generic_arg
                                        .as_const()
                                        .as_ref()
                                        .map(|ct| compile_const(env, &expr.span, ct))
                                })
                                .collect::<Vec<_>>();
                            let generic_tys = generic_args
                                .iter()
                                .filter_map(|generic_arg| {
                                    generic_arg
                                        .as_type()
                                        .as_ref()
                                        .map(|ty| compile_type(env, &expr.span, generics, ty))
                                })
                                .collect::<Vec<_>>();

                            Rc::new(Expr::GetFunction {
                                func: compile_def_id(env, *def_id),
                                generic_consts,
                                generic_tys,
                            })
                            .alloc(ty)
                        }
                        DefKind::Struct | DefKind::Variant => {
                            let path = compile_def_id(env, *def_id);
                            let generic_consts = generic_args
                                .iter()
                                .filter_map(|generic_arg| {
                                    generic_arg
                                        .as_const()
                                        .as_ref()
                                        .map(|ct| compile_const(env, &expr.span, ct))
                                })
                                .collect::<Vec<_>>();
                            let generic_tys = generic_args
                                .iter()
                                .filter_map(|generic_arg| {
                                    generic_arg
                                        .as_type()
                                        .as_ref()
                                        .map(|ty| compile_type(env, &expr.span, generics, ty))
                                })
                                .collect::<Vec<_>>();

                            Rc::new(Expr::ConstructorAsClosure {
                                path,
                                generic_consts,
                                generic_tys,
                            })
                            .alloc(ty)
                        }
                        DefKind::AssocFn => {
                            let parent_symbol = env.tcx.def_key(parent).get_opt_name().unwrap();

                            Rc::new(Expr::GetAssociatedFunction {
                                ty: CoqType::var("Self"),
                                func: format!("{}.{}", symbol.unwrap(), parent_symbol),
                                generic_consts: vec![],
                                generic_tys: vec![],
                            })
                            .alloc(ty)
                        }
                        DefKind::Fn => {
                            let parent_path = compile_def_id(env, parent);
                            let mut segments = parent_path.segments.clone();
                            let last_segment = segments.pop().unwrap();
                            segments.push(format!("{}.{}", last_segment, symbol.unwrap()));

                            Rc::new(Expr::GetFunction {
                                func: Rc::new(Path { segments }),
                                generic_consts: vec![],
                                generic_tys: vec![],
                            })
                            .alloc(ty)
                        }
                        _ => {
                            emit_warning_with_note(
                            env,
                            &expr.span,
                            "We do not support this kind of expression",
                            Some(format!("Please report 🙏\n\nparent_kind: {parent_kind:#?}\nexpression: {expr:#?}").as_str()),
                        );

                            Rc::new(Expr::Comment(
                                "Unimplemented parent_kind".to_string(),
                                Expr::tt(),
                            ))
                        }
                    }
                }
                _ => {
                    let error_message = "Expected a function name";

                    emit_warning_with_note(
                        env,
                        &expr.span,
                        error_message,
                        Some("Please report 🙏"),
                    );

                    Rc::new(Expr::Comment(error_message.to_string(), Expr::tt()))
                }
            }
        }
        thir::ExprKind::NamedConst { def_id, args, .. } => {
            let path = compile_def_id(env, *def_id);
            let symbol = env.tcx.def_key(*def_id).get_opt_name();
            let parent = env.tcx.opt_parent(*def_id).unwrap();
            let parent_kind = env.tcx.def_kind(parent);
            let return_ty = compile_type(env, &expr.span, generics, &expr.ty);

            match parent_kind {
                DefKind::Variant => Rc::new(Expr::GetConstant { path, return_ty }),
                DefKind::Impl { .. } => {
                    let parent_type = env.tcx.type_of(parent).instantiate(env.tcx, args);
                    let ty = compile_type(env, &expr.span, generics, &parent_type);
                    Rc::new(Expr::GetAssociatedConstant {
                        ty,
                        constant: symbol.unwrap().to_string(),
                        return_ty,
                    })
                }
                _ => Rc::new(Expr::GetConstant { path, return_ty }),
            }
        }
        thir::ExprKind::ConstParam { param, .. } => {
            let name = to_valid_coq_name(IsValue::No, param.name.as_str());

            Expr::local_var(name.as_str()).alloc(ty)
        }
        thir::ExprKind::StaticRef { def_id, .. } => {
            let return_ty = compile_type(env, &expr.span, generics, &expr.ty);

            Rc::new(Expr::GetConstant {
                path: compile_def_id(env, *def_id),
                return_ty,
            })
        }
        thir::ExprKind::InlineAsm(_) => Rc::new(Expr::LocalVar("InlineAssembly".to_string())),
        thir::ExprKind::OffsetOf { .. } => {
            let error_message = "`OffsetOf` expression are not handled yet";

            emit_warning_with_note(env, &expr.span, error_message, Some("Please report!"));

            Rc::new(Expr::Comment(error_message.to_string(), Expr::tt()))
        }
        thir::ExprKind::ThreadLocalRef(def_id) => {
            let return_ty = compile_type(env, &expr.span, generics, &expr.ty);

            Rc::new(Expr::GetConstant {
                path: compile_def_id(env, *def_id),
                return_ty,
            })
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
    let return_ty = match &expr_id {
        Some(expr_id) => {
            let expr = thir.exprs.get(*expr_id).unwrap();
            compile_type(env, &expr.span, generics, &expr.ty)
        }
        None => CoqType::unit(),
    };

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
                    else_block,
                    ..
                } => {
                    let init = match initializer {
                        Some(initializer) => compile_expr(env, generics, thir, initializer),
                        None => Expr::local_var("Value.DeclaredButUndefined"),
                    };
                    let else_block = else_block
                        .as_ref()
                        .map(|else_block| compile_block(env, generics, thir, else_block));
                    let compiled_pattern =
                        crate::thir_pattern::compile_pattern(env, generics, pattern);
                    let init_ty =
                        initializer.map(|initializer| thir.exprs.get(initializer).unwrap().ty);

                    match (compiled_pattern.as_ref(), &else_block) {
                        (
                            Pattern::Binding {
                                name,
                                ty: _,
                                pattern: None,
                                is_with_ref: false,
                            },
                            None,
                        ) => Rc::new(Expr::Let {
                            name: Some(name.clone()),
                            ty: init_ty
                                .as_ref()
                                .map(|init_ty| compile_type(env, &pattern.span, generics, init_ty)),
                            init: init.read(),
                            body,
                        }),
                        _ => {
                            let mut arms = vec![MatchArm {
                                pattern: compiled_pattern,
                                if_let_guard: vec![],
                                body: body.read(),
                            }];
                            if let Some(else_block) = else_block {
                                // If there is an else block, we add a wildcard arm to the match.
                                // This is to handle the case where the pattern does not match.
                                // If the pattern matches, the else block is not executed.
                                arms.push(MatchArm {
                                    pattern: Rc::new(Pattern::Wild),
                                    if_let_guard: vec![],
                                    body: else_block.read(),
                                });
                            }

                            build_match(return_ty.clone(), init, arms).alloc(return_ty.clone())
                        }
                    }
                }
                thir::StmtKind::Expr { expr: expr_id, .. } => {
                    let expr = thir.exprs.get(*expr_id).unwrap();
                    let init = compile_expr(env, generics, thir, expr_id);
                    let init_ty = &thir.exprs.get(*expr_id).unwrap().ty;
                    // Special case with the [never] type
                    if let TyKind::Never = init_ty.kind() {
                        return init;
                    }

                    Rc::new(Expr::Let {
                        name: None,
                        ty: Some(compile_type(env, &expr.span, generics, init_ty)),
                        init: init.read(),
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

pub(crate) fn compile_const(env: &Env, span: &rustc_span::Span, const_: &Const) -> Rc<Expr> {
    match &const_.kind() {
        ConstKind::Param(param) => {
            let name = to_valid_coq_name(IsValue::No, param.name.as_str());

            Expr::local_var(name.as_str())
        }
        ConstKind::Infer(_) => Expr::local_var("InferConst"),
        ConstKind::Bound(_, _) => Expr::local_var("BoundConst"),
        ConstKind::Placeholder(_) => Expr::local_var("PlaceholderConst"),
        ConstKind::Unevaluated(unevaluated_const) => {
            // We do not know yet how to handle this kind of constant. We return something that
            // type-check for now.
            let path = compile_def_id(env, unevaluated_const.def);

            Rc::new(Expr::Call {
                func: Expr::local_var("M.unevaluated_const"),
                args: vec![Rc::new(Expr::Literal(Rc::new(Literal::String(
                    path.to_name().as_str().to_string(),
                ))))],
                kind: CallKind::Pure,
            })
        }
        ConstKind::Value(ty, value) => match value {
            rustc_middle::ty::ValTree::Leaf(leaf) => match ty.kind() {
                TyKind::Bool => Rc::new(Expr::Literal(Rc::new(Literal::Bool(
                    leaf.try_to_bool().unwrap(),
                )))),
                TyKind::Int(_) | TyKind::Uint(_) => {
                    Rc::new(Expr::Literal(Rc::new(Literal::Integer(
                        compile_literal_integer(env, span, ty, false, leaf.to_uint(leaf.size())),
                    ))))
                }
                _ => {
                    emit_warning_with_note(
                        env,
                        span,
                        "We do not support this kind of constant",
                        Some("Please report 🙏"),
                    );

                    Rc::new(Expr::Comment(
                        "Unimplemented constant".to_string(),
                        Expr::tt(),
                    ))
                }
            },
            rustc_middle::ty::ValTree::Branch(_) => Expr::local_var("ValueBranchConst"),
        },
        ConstKind::Error(_) => Expr::local_var("ErrorConst"),
        ConstKind::Expr(_) => Expr::local_var("ExprConst"),
    }
}
