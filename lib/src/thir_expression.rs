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

impl ExprKind {
    pub(crate) fn alloc(self: Rc<Self>, ty: Option<Rc<CoqType>>) -> Rc<Self> {
        Rc::new(ExprKind::Call {
            func: Rc::new(Expr {
                kind: Rc::new(ExprKind::LocalVar("M.alloc".to_string())),
                ty: None,
            }),
            args: vec![Rc::new(Expr { kind: self, ty })],
            purity: Purity::Effectful,
            from_user: false,
        })
    }
}

fn path_of_bin_op(bin_op: &BinOp, ty_left: &Rc<CoqType>, ty_right: &Rc<CoqType>) -> (Path, Purity) {
    match bin_op {
        BinOp::Add => (Path::new(&["BinOp", "Panic", "add"]), Purity::Effectful),
        BinOp::Sub => (Path::new(&["BinOp", "Panic", "sub"]), Purity::Effectful),
        BinOp::Mul => (Path::new(&["BinOp", "Panic", "mul"]), Purity::Effectful),
        BinOp::Div => (Path::new(&["BinOp", "Panic", "div"]), Purity::Effectful),
        BinOp::Rem => (Path::new(&["BinOp", "Panic", "rem"]), Purity::Effectful),
        BinOp::BitXor => (Path::new(&["BinOp", "Pure", "bit_xor"]), Purity::Pure),
        BinOp::BitAnd => (Path::new(&["BinOp", "Pure", "bit_and"]), Purity::Pure),
        BinOp::BitOr => (Path::new(&["BinOp", "Pure", "bit_or"]), Purity::Pure),
        BinOp::Shl => (Path::new(&["BinOp", "Panic", "shl"]), Purity::Effectful),
        BinOp::Shr => (Path::new(&["BinOp", "Panic", "shr"]), Purity::Effectful),
        BinOp::Eq => {
            if matches!(ty_left.as_ref(), CoqType::Path { path } if path.segments == ["bool", "t"])
                && matches!(ty_right.as_ref(), CoqType::Path { path } if path.segments == ["bool", "t"])
            {
                (Path::new(&["Bool", "eqb"]), Purity::Pure)
            } else {
                (Path::new(&["BinOp", "Pure", "eq"]), Purity::Pure)
            }
        }
        BinOp::Ne => (Path::new(&["BinOp", "Pure", "ne"]), Purity::Pure),
        BinOp::Lt => (Path::new(&["BinOp", "Pure", "lt"]), Purity::Pure),
        BinOp::Le => (Path::new(&["BinOp", "Pure", "le"]), Purity::Pure),
        BinOp::Ge => (Path::new(&["BinOp", "Pure", "ge"]), Purity::Pure),
        BinOp::Gt => (Path::new(&["BinOp", "Pure", "gt"]), Purity::Pure),
        BinOp::Offset => (Path::new(&["BinOp", "Pure", "offset"]), Purity::Pure),
    }
}

pub(crate) fn compile_expr<'a>(
    env: &mut Env<'a>,
    thir: &rustc_middle::thir::Thir<'a>,
    expr_id: &rustc_middle::thir::ExprId,
) -> Rc<Expr> {
    let expr = thir.exprs.get(*expr_id).unwrap();
    let kind = compile_expr_kind(env, thir, expr_id);
    let ty = compile_type(env, &expr.ty).val();
    Rc::new(Expr { kind, ty: Some(ty) })
}

impl Expr {
    fn match_simple_call(self: Rc<Self>, name_in: &[&str]) -> Option<Rc<Self>> {
        if let ExprKind::Call {
            func,
            args,
            purity: _,
            from_user: _,
        } = self.kind.as_ref()
        {
            if let ExprKind::LocalVar(func) = func.kind.as_ref() {
                if name_in.contains(&func.as_str()) && args.len() == 1 {
                    return Some(args.get(0).unwrap().clone());
                }
            }
        }

        None
    }

    /// Return the borrowed expression if the expression is a borrow.
    fn match_borrow(self: Rc<Self>) -> Option<Rc<Self>> {
        self.match_simple_call(&["borrow", "borrow_mut"])
    }

    fn match_deref(self: Rc<Self>) -> Option<Rc<Self>> {
        self.match_simple_call(&["deref"])
    }

    pub(crate) fn read(self: Rc<Self>) -> Rc<Self> {
        // If we read an allocated expression, we just return the expression.
        if let Some(expr) = self.clone().match_simple_call(&["M.alloc"]) {
            return expr;
        }

        Rc::new(Expr {
            ty: match self.ty.clone() {
                None => None,
                Some(ty) => {
                    let ty = ty.unval();
                    let is_never = match &ty {
                        Some(ty) => match &**ty {
                            CoqType::Path { path } => path.segments == ["never", "t"],
                            _ => false,
                        },
                        None => false,
                    };
                    if is_never {
                        // This is a special case to prevent errors with the never type
                        // returned by the panic function, that is used as `unit` after.
                        // Is it a bug from the Rust AST?
                        None
                    } else {
                        ty
                    }
                }
            },
            kind: Rc::new(ExprKind::Call {
                func: Rc::new(Expr {
                    kind: Rc::new(ExprKind::LocalVar("M.read".to_string())),
                    ty: None,
                }),
                args: vec![self],
                purity: Purity::Effectful,
                from_user: false,
            }),
        })
    }

    fn copy(self: Rc<Self>) -> Rc<Self> {
        if self.clone().match_simple_call(&["M.alloc"]).is_some() {
            return self;
        }

        Rc::new(Expr {
            ty: self.ty.clone(),
            kind: Rc::new(ExprKind::Call {
                func: Rc::new(Expr {
                    kind: Rc::new(ExprKind::LocalVar("M.copy".to_string())),
                    ty: None,
                }),
                args: vec![self],
                purity: Purity::Effectful,
                from_user: false,
            }),
        })
    }
}

pub(crate) fn is_mutable_borrow_kind(borrow_kind: &BorrowKind) -> bool {
    match borrow_kind {
        BorrowKind::Shared | BorrowKind::Shallow => false,
        BorrowKind::Unique | BorrowKind::Mut { .. } => true,
    }
}

fn compile_borrow(borrow_kind: &BorrowKind, arg: Rc<Expr>) -> Rc<ExprKind> {
    let func = if is_mutable_borrow_kind(borrow_kind) {
        "borrow_mut".to_string()
    } else {
        "borrow".to_string()
    };

    if let Some(derefed) = arg.clone().match_deref() {
        if let Some(ty) = derefed.ty.clone() {
            if let Some((ref_name, _, _)) = ty.match_ref() {
                if (func == "borrow" && ref_name == "ref")
                    || (func == "borrow_mut" && ref_name == "mut_ref")
                {
                    return derefed.kind.clone();
                }
            }
        }
    }

    Rc::new(ExprKind::Call {
        func: Rc::new(Expr {
            kind: Rc::new(ExprKind::LocalVar(func)),
            ty: None,
        }),
        args: vec![arg],
        purity: Purity::Pure,
        from_user: false,
    })
}

pub(crate) fn allocate_bindings(bindings: &[String], body: Rc<Expr>) -> Rc<Expr> {
    bindings.iter().rfold(body, |body, binding| {
        Rc::new(Expr {
            ty: body.ty.clone(),
            kind: Rc::new(ExprKind::Let {
                is_monadic: false,
                name: Some(binding.clone()),
                init: Rc::new(Expr {
                    kind: Rc::new(ExprKind::LocalVar(binding.clone())).alloc(None),
                    ty: None,
                }),
                body,
            }),
        })
    })
}

fn build_inner_match(patterns: Vec<(String, Rc<Pattern>)>, body: Rc<Expr>) -> Rc<Expr> {
    let default_match_arm = Rc::new(MatchArm {
        pattern: Rc::new(Pattern::Wild),
        body: Rc::new(Expr {
            kind: Rc::new(ExprKind::Call {
                func: Expr::local_var("M.break_match"),
                args: vec![],
                purity: Purity::Effectful,
                from_user: false,
            }),
            ty: None,
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
            } => Rc::new(Expr {
                ty: body.ty.clone(),
                kind: Rc::new(ExprKind::Let {
                    is_monadic: false,
                    name: Some(name.clone()),
                    init: match is_with_ref {
                        None => Expr::local_var(&scrutinee).copy(),
                        Some(is_with_ref) => {
                            let func = if *is_with_ref { "borrow" } else { "borrow_mut" };

                            Rc::new(Expr {
                                ty: None,
                                kind: Rc::new(ExprKind::Call {
                                    func: Expr::local_var(func),
                                    args: vec![Expr::local_var(&scrutinee)],
                                    purity: Purity::Pure,
                                    from_user: false,
                                })
                                .alloc(None),
                            })
                        }
                    },
                    body: match pattern {
                        None => body,
                        Some(pattern) => {
                            build_inner_match(vec![(scrutinee, pattern.clone())], body)
                        }
                    },
                }),
            }),
            Pattern::StructStruct(path, fields, struct_or_variant) => Rc::new(Expr {
                ty: body.ty.clone(),
                kind: Rc::new(ExprKind::Match {
                    scrutinee: Expr::local_var(&scrutinee).read(),
                    arms: [
                        vec![Rc::new(MatchArm {
                            pattern: Rc::new(Pattern::StructStruct(
                                path.clone(),
                                fields
                                    .iter()
                                    .map(|(field_name, _)| {
                                        (field_name.clone(), Rc::new(Pattern::Wild))
                                    })
                                    .collect(),
                                *struct_or_variant,
                            )),
                            body: {
                                let body = build_inner_match(
                                    fields
                                        .iter()
                                        .enumerate()
                                        .map(|(index, (_, field_pattern))| {
                                            (format!("γ{index}"), field_pattern.clone())
                                        })
                                        .collect(),
                                    body,
                                );

                                fields.iter().enumerate().rfold(
                                    body,
                                    |body, (index, (field_name, _))| {
                                        Rc::new(Expr {
                                            ty: body.ty.clone(),
                                            kind: Rc::new(ExprKind::Let {
                                                is_monadic: false,
                                                name: Some(format!("γ{index}")),
                                                init: Rc::new(Expr {
                                                    ty: None,
                                                    kind: Rc::new(ExprKind::NamedField {
                                                        base: Expr::local_var(&scrutinee),
                                                        name: format!(
                                                            "{}.{field_name}",
                                                            path.segments.last().unwrap(),
                                                        ),
                                                    }),
                                                }),
                                                body,
                                            }),
                                        })
                                    },
                                )
                            },
                        })],
                        match struct_or_variant {
                            StructOrVariant::Struct => vec![],
                            StructOrVariant::Variant => vec![default_match_arm.clone()],
                        },
                    ]
                    .concat(),
                }),
            }),
            Pattern::StructTuple(path, patterns, struct_or_variant) => Rc::new(Expr {
                ty: body.ty.clone(),
                kind: Rc::new(ExprKind::Match {
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
                                            (format!("γ{index}"), pattern.clone())
                                        })
                                        .collect(),
                                    body,
                                );

                                patterns.iter().enumerate().rfold(body, |body, (index, _)| {
                                    Rc::new(Expr {
                                        ty: body.ty.clone(),
                                        kind: Rc::new(ExprKind::Let {
                                            is_monadic: false,
                                            name: Some(format!("γ{index}")),
                                            init: Rc::new(Expr {
                                                ty: None,
                                                kind: Rc::new(ExprKind::NamedField {
                                                    base: Expr::local_var(&scrutinee),
                                                    name: format!(
                                                        "{}.{index}",
                                                        path.segments.last().unwrap(),
                                                    ),
                                                }),
                                            }),
                                            body,
                                        }),
                                    })
                                })
                            },
                        })],
                        match struct_or_variant {
                            StructOrVariant::Struct => vec![],
                            StructOrVariant::Variant => vec![default_match_arm.clone()],
                        },
                    ]
                    .concat(),
                }),
            }),
            Pattern::Deref(pattern) => Rc::new(Expr {
                ty: body.ty.clone(),
                kind: Rc::new(ExprKind::Let {
                    is_monadic: false,
                    name: Some(scrutinee.clone()),
                    init: Rc::new(Expr {
                        ty: None,
                        kind: Rc::new(ExprKind::Call {
                            func: Expr::local_var("deref"),
                            args: vec![Expr::local_var(&scrutinee).read()],
                            purity: Purity::Pure,
                            from_user: false,
                        }),
                    }),
                    body: build_inner_match(vec![(scrutinee.clone(), pattern.clone())], body),
                }),
            }),
            Pattern::Or(_) => panic!("Or pattern should have been flattened"),
            Pattern::Tuple(patterns) => Rc::new(Expr {
                ty: body.ty.clone(),
                kind: Rc::new(ExprKind::Match {
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
                                    .map(|(index, pattern)| (format!("γ{index}"), pattern.clone()))
                                    .collect(),
                                body,
                            );

                            patterns.iter().enumerate().rfold(body, |body, (index, _)| {
                                Rc::new(Expr {
                                    ty: body.ty.clone(),
                                    kind: Rc::new(ExprKind::Let {
                                        is_monadic: false,
                                        name: Some(format!("γ{index}")),
                                        init: {
                                            let init = (0..(patterns.len() - 1 - index)).fold(
                                                Expr::local_var(&scrutinee),
                                                |init, _| {
                                                    Rc::new(Expr {
                                                        ty: None,
                                                        kind: Rc::new(ExprKind::Call {
                                                            func: Expr::local_var(
                                                                "Tuple.Access.left",
                                                            ),
                                                            args: vec![init],
                                                            purity: Purity::Pure,
                                                            from_user: false,
                                                        }),
                                                    })
                                                },
                                            );

                                            if index == 0 {
                                                init
                                            } else {
                                                Rc::new(Expr {
                                                    ty: None,
                                                    kind: Rc::new(ExprKind::Call {
                                                        func: Expr::local_var("Tuple.Access.right"),
                                                        args: vec![init],
                                                        purity: Purity::Pure,
                                                        from_user: false,
                                                    }),
                                                })
                                            }
                                        },
                                        body,
                                    }),
                                })
                            })
                        },
                    })],
                }),
            }),
            Pattern::Lit(_) => Rc::new(Expr {
                ty: body.ty.clone(),
                kind: Rc::new(ExprKind::Match {
                    scrutinee: Expr::local_var(&scrutinee).read(),
                    arms: vec![
                        Rc::new(MatchArm {
                            pattern: pattern.clone(),
                            body,
                        }),
                        default_match_arm.clone(),
                    ],
                }),
            }),
            Pattern::Slice {
                init_patterns,
                slice_pattern,
            } => Rc::new(Expr {
                ty: body.ty.clone(),
                kind: Rc::new(ExprKind::Match {
                    scrutinee: Expr::local_var(&scrutinee).read(),
                    arms: vec![
                        Rc::new(MatchArm {
                            pattern: Rc::new(Pattern::Slice {
                                init_patterns: init_patterns
                                    .iter()
                                    .map(|_| Rc::new(Pattern::Wild))
                                    .collect(),
                                slice_pattern: slice_pattern
                                    .as_ref()
                                    .map(|_| Rc::new(Pattern::Wild)),
                            }),
                            body: {
                                let body = build_inner_match(
                                    vec![
                                        init_patterns
                                            .iter()
                                            .enumerate()
                                            .map(|(index, pattern)| {
                                                (format!("γ{index}"), pattern.clone())
                                            })
                                            .collect(),
                                        match slice_pattern {
                                            None => vec![],
                                            Some(slice_pattern) => {
                                                vec![("γ".to_string(), slice_pattern.clone())]
                                            }
                                        },
                                    ]
                                    .concat(),
                                    body,
                                );

                                let body = match slice_pattern {
                                    None => body,
                                    Some(_) => Rc::new(Expr {
                                        ty: body.ty.clone(),
                                        kind: Rc::new(ExprKind::Let {
                                            is_monadic: false,
                                            name: Some("γ".to_string()),
                                            init: Rc::new(Expr {
                                                ty: None,
                                                kind: Rc::new(ExprKind::NamedField {
                                                    base: Expr::local_var(&scrutinee),
                                                    name: format!(
                                                        "[{}].slice",
                                                        init_patterns.len()
                                                    ),
                                                }),
                                            }),
                                            body,
                                        }),
                                    }),
                                };

                                init_patterns
                                    .iter()
                                    .enumerate()
                                    .rfold(body, |body, (index, _)| {
                                        Rc::new(Expr {
                                            ty: body.ty.clone(),
                                            kind: Rc::new(ExprKind::Let {
                                                is_monadic: false,
                                                name: Some(format!("γ{index}")),
                                                init: Rc::new(Expr {
                                                    ty: None,
                                                    kind: Rc::new(ExprKind::NamedField {
                                                        base: Expr::local_var(&scrutinee),
                                                        name: format!("[{index}]",),
                                                    }),
                                                }),
                                                body,
                                            }),
                                        })
                                    })
                            },
                        }),
                        default_match_arm.clone(),
                    ],
                }),
            }),
        })
}

fn build_match(scrutinee: Rc<Expr>, arms: Vec<MatchArm>, _ty: Option<Rc<CoqType>>) -> Rc<ExprKind> {
    let arms_with_flatten_patterns = arms.into_iter().flat_map(|MatchArm { pattern, body }| {
        pattern
            .flatten_ors()
            .into_iter()
            .map(move |pattern| MatchArm {
                pattern,
                body: body.clone(),
            })
    });

    Rc::new(ExprKind::Call {
        func: Expr::local_var("match_operator"),
        args: vec![
            scrutinee,
            Rc::new(Expr {
                kind: Rc::new(ExprKind::Array {
                    elements: arms_with_flatten_patterns
                        .map(|MatchArm { pattern, body }| {
                            Rc::new(Expr {
                                kind: Rc::new(ExprKind::Lambda {
                                    args: vec![("γ".to_string(), None)],
                                    body: build_inner_match(vec![("γ".to_string(), pattern)], body),
                                    is_for_match: true,
                                }),
                                ty: None,
                            })
                        })
                        .collect(),
                }),
                ty: None,
            }),
        ],
        purity: Purity::Effectful,
        from_user: false,
    })
}

fn compile_expr_kind<'a>(
    env: &mut Env<'a>,
    thir: &rustc_middle::thir::Thir<'a>,
    expr_id: &rustc_middle::thir::ExprId,
) -> Rc<ExprKind> {
    let expr = thir.exprs.get(*expr_id).unwrap();
    let ty = compile_type(env, &expr.ty);

    match &expr.kind {
        thir::ExprKind::Scope { value, .. } => compile_expr_kind(env, thir, value),
        thir::ExprKind::Box { value } => {
            let value = compile_expr(env, thir, value);

            Rc::new(ExprKind::Call {
                func: Rc::new(Expr {
                    kind: Rc::new(ExprKind::LocalVar(
                        "(alloc.boxed.Box _ alloc.boxed.Box.Default.A)::[\"new\"]".to_string(),
                    )),
                    ty: None,
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
            let condition = compile_expr(env, thir, cond).read();
            let success = compile_expr(env, thir, then);
            let failure = match else_opt {
                Some(else_expr) => compile_expr(env, thir, else_expr),
                None => Expr::tt(),
            };
            Rc::new(ExprKind::If {
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

                match func.clone().match_simple_call(&["M.alloc"]).as_ref() {
                    Some(expr) => match expr.kind.as_ref() {
                        ExprKind::Constructor(_) => (Purity::Pure, false),
                        _ => default,
                    },
                    _ => default,
                }
            };
            let func = func.read();

            Rc::new(ExprKind::Call {
                func,
                args,
                purity,
                from_user,
            })
            .alloc(Some(ty))
        }
        thir::ExprKind::Deref { arg } => {
            let arg = compile_expr(env, thir, arg).read();

            if let Some(borrowed) = Expr::match_borrow(arg.clone()) {
                return borrowed.kind.clone();
            }

            Rc::new(ExprKind::Call {
                func: Rc::new(Expr {
                    kind: Rc::new(ExprKind::LocalVar("deref".to_string())),
                    ty: None,
                }),
                args: vec![arg],
                purity: Purity::Pure,
                from_user: false,
            })
        }
        thir::ExprKind::Binary { op, lhs, rhs } => {
            let left_ty = compile_type(env, &thir.exprs.get(*lhs).unwrap().ty);
            let right_ty = compile_type(env, &thir.exprs.get(*rhs).unwrap().ty);
            let (path, purity) = path_of_bin_op(op, &left_ty, &right_ty);
            let lhs = compile_expr(env, thir, lhs);
            let rhs = compile_expr(env, thir, rhs);
            Rc::new(ExprKind::Call {
                func: Rc::new(Expr {
                    kind: Rc::new(ExprKind::Var(path)),
                    ty: None,
                }),
                args: vec![lhs.read(), rhs.read()],
                purity,
                from_user: false,
            })
            .alloc(Some(ty))
        }
        thir::ExprKind::LogicalOp { op, lhs, rhs } => {
            let path = match op {
                LogicalOp::And => Path::new(&["BinOp", "Pure", "and"]),
                LogicalOp::Or => Path::new(&["BinOp", "Pure", "or"]),
            };
            let lhs = compile_expr(env, thir, lhs);
            let rhs = compile_expr(env, thir, rhs);
            Rc::new(ExprKind::Call {
                func: Rc::new(Expr {
                    kind: Rc::new(ExprKind::Var(path)),
                    ty: None,
                }),
                args: vec![lhs.read(), rhs.read()],
                purity: Purity::Pure,
                from_user: false,
            })
            .alloc(Some(ty))
        }
        thir::ExprKind::Unary { op, arg } => {
            let (path, purity) = match op {
                UnOp::Not => (Path::new(&["UnOp", "not"]), Purity::Pure),
                UnOp::Neg => (Path::new(&["UnOp", "neg"]), Purity::Effectful),
            };
            let arg = compile_expr(env, thir, arg);
            Rc::new(ExprKind::Call {
                func: Rc::new(Expr {
                    kind: Rc::new(ExprKind::Var(path)),
                    ty: None,
                }),
                args: vec![arg.read()],
                purity,
                from_user: false,
            })
            .alloc(Some(ty))
        }
        thir::ExprKind::Cast { source } => {
            let func = Expr::local_var("M.cast");
            let source = compile_expr(env, thir, source);

            Rc::new(ExprKind::Call {
                func,
                args: vec![source.read()],
                purity: Purity::Effectful,
                from_user: false,
            })
            .alloc(Some(ty))
        }
        thir::ExprKind::Use { source } => {
            let source = compile_expr(env, thir, source);

            Rc::new(ExprKind::Use(source))
        }
        thir::ExprKind::NeverToAny { source } => {
            let func = Rc::new(Expr {
                kind: Rc::new(ExprKind::LocalVar("never_to_any".to_string())),
                ty: None,
            });
            let source = compile_expr(env, thir, source);
            Rc::new(ExprKind::Call {
                func,
                args: vec![source.read()],
                purity: Purity::Effectful,
                from_user: false,
            })
            .alloc(Some(ty))
        }
        thir::ExprKind::Pointer { source, cast } => {
            let func = Rc::new(Expr {
                kind: Rc::new(ExprKind::LocalVar("pointer_coercion".to_string())),
                ty: None,
            });
            let source = compile_expr(env, thir, source);
            let cast = Rc::new(Expr {
                kind: Rc::new(ExprKind::Message(format!("{cast:?}"))),
                ty: None,
            });
            Rc::new(ExprKind::Call {
                func,
                args: vec![cast, source],
                purity: Purity::Pure,
                from_user: false,
            })
        }
        thir::ExprKind::Loop { body, .. } => {
            let body = compile_expr(env, thir, body);
            Rc::new(ExprKind::Loop { body })
        }
        thir::ExprKind::Let { expr, pat } => {
            let pat = crate::thir_pattern::compile_pattern(env, pat);
            let init = compile_expr(env, thir, expr);
            Rc::new(ExprKind::LetIf { pat, init })
        }
        thir::ExprKind::Match { scrutinee, arms } => {
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
            build_match(scrutinee, arms, Some(ty.val()))
        }
        thir::ExprKind::Block { block: block_id } => {
            compile_block(env, thir, block_id).kind.clone()
        }
        thir::ExprKind::Assign { lhs, rhs } => {
            let func = Rc::new(Expr {
                kind: Rc::new(ExprKind::LocalVar("assign".to_string())),
                ty: None,
            });
            let args = vec![
                compile_expr(env, thir, lhs),
                compile_expr(env, thir, rhs).read(),
            ];
            Rc::new(ExprKind::Call {
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

            Rc::new(ExprKind::Let {
                is_monadic: false,
                name: Some("β".to_string()),
                init: lhs,
                body: Rc::new(Expr {
                    kind: Rc::new(ExprKind::Call {
                        func: Rc::new(Expr {
                            kind: Rc::new(ExprKind::Var(Path::new(&["assign"]))),
                            ty: None,
                        }),
                        args: vec![
                            Rc::new(Expr {
                                kind: Rc::new(ExprKind::LocalVar("β".to_string())),
                                ty: None,
                            }),
                            Rc::new(Expr {
                                kind: Rc::new(ExprKind::Call {
                                    func: Rc::new(Expr {
                                        kind: Rc::new(ExprKind::Var(path)),
                                        ty: None,
                                    }),
                                    args: vec![
                                        Rc::new(Expr {
                                            kind: Rc::new(ExprKind::LocalVar("β".to_string())),
                                            ty: None,
                                        })
                                        .read(),
                                        rhs.read(),
                                    ],
                                    purity,
                                    from_user: false,
                                }),
                                ty: None,
                            }),
                        ],
                        purity: Purity::Effectful,
                        from_user: false,
                    }),
                    ty: None,
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
                    Rc::new(ExprKind::NamedField { base, name })
                }
                None => Rc::new(ExprKind::Message("Unknown Field".to_string())),
            }
        }
        thir::ExprKind::Index { lhs, index } => {
            let base = compile_expr(env, thir, lhs);
            let index = compile_expr(env, thir, index);
            Rc::new(ExprKind::Index { base, index })
        }
        thir::ExprKind::VarRef { id } => {
            let name = to_valid_coq_name(env.tcx.hir().opt_name(id.0).unwrap().as_str());
            Rc::new(ExprKind::LocalVar(name))
        }
        thir::ExprKind::UpvarRef { var_hir_id, .. } => {
            let name = to_valid_coq_name(env.tcx.hir().opt_name(var_hir_id.0).unwrap().as_str());
            Rc::new(ExprKind::LocalVar(name))
        }
        thir::ExprKind::Borrow { borrow_kind, arg } => {
            let arg = compile_expr(env, thir, arg);

            compile_borrow(borrow_kind, arg).alloc(Some(ty))
        }
        thir::ExprKind::AddressOf { mutability, arg } => {
            let func = match mutability {
                rustc_middle::mir::Mutability::Not => "addr_of".to_string(),
                rustc_middle::mir::Mutability::Mut => "addr_of_mut".to_string(),
            };
            let arg = compile_expr(env, thir, arg);
            Rc::new(ExprKind::Call {
                func: Rc::new(Expr {
                    kind: Rc::new(ExprKind::LocalVar(func)),
                    ty: None,
                }),
                args: vec![arg],
                purity: Purity::Pure,
                from_user: false,
            })
        }
        thir::ExprKind::Break { .. } => Rc::new(ExprKind::ControlFlow(LoopControlFlow::Break)),
        thir::ExprKind::Continue { .. } => {
            Rc::new(ExprKind::ControlFlow(LoopControlFlow::Continue))
        }
        thir::ExprKind::Return { value } => {
            let value = match value {
                Some(value) => compile_expr(env, thir, value).read(),
                None => Expr::tt(),
            };
            Rc::new(ExprKind::Return(value))
        }
        thir::ExprKind::ConstBlock { did, .. } => Rc::new(ExprKind::Var(compile_def_id(env, *did))),
        thir::ExprKind::Repeat { value, count } => {
            let func = Rc::new(Expr {
                kind: Rc::new(ExprKind::LocalVar("repeat".to_string())),
                ty: None,
            });
            let args = vec![
                compile_expr(env, thir, value).read(),
                Rc::new(Expr {
                    kind: Rc::new(ExprKind::LocalVar(count.to_string())),
                    ty: None,
                }),
            ];
            Rc::new(ExprKind::Call {
                func,
                args,
                purity: Purity::Pure,
                from_user: false,
            })
            .alloc(Some(ty))
        }
        thir::ExprKind::Array { fields } => Rc::new(ExprKind::Array {
            elements: fields
                .iter()
                .map(|field| compile_expr(env, thir, field).read())
                .collect(),
        })
        .alloc(Some(ty)),
        thir::ExprKind::Tuple { fields } => {
            let elements: Vec<_> = fields
                .iter()
                .map(|field| compile_expr(env, thir, field).read())
                .collect();
            if elements.is_empty() {
                ExprKind::tt()
            } else {
                Rc::new(ExprKind::Tuple { elements }).alloc(Some(ty))
            }
        }
        thir::ExprKind::Adt(adt_expr) => {
            let AdtExpr {
                adt_def,
                variant_index,
                fields,
                ..
            } = &**adt_expr;
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
                StructOrVariant::Variant
            } else {
                StructOrVariant::Struct
            };
            if fields.is_empty() {
                return Rc::new(ExprKind::StructUnit {
                    path,
                    struct_or_variant,
                })
                .alloc(Some(ty));
            }
            if is_a_tuple {
                let fields = fields.into_iter().map(|(_, pattern)| pattern).collect();
                Rc::new(ExprKind::StructTuple {
                    path,
                    fields,
                    struct_or_variant,
                })
                .alloc(Some(ty))
            } else {
                Rc::new(ExprKind::StructStruct {
                    path,
                    fields,
                    base: None,
                    struct_or_variant,
                })
                .alloc(Some(ty))
            }
        }
        thir::ExprKind::PlaceTypeAscription { source, .. }
        | thir::ExprKind::ValueTypeAscription { source, .. } => {
            compile_expr_kind(env, thir, source)
        }
        thir::ExprKind::Closure(closure) => {
            let rustc_middle::thir::ClosureExpr { closure_id, .. } = &**closure;
            let thir = env.tcx.thir_body(closure_id);
            let Ok((thir, expr_id)) = thir else {
                panic!("thir failed to compile");
            };
            let thir = thir.borrow();
            let args: Vec<(Rc<Pattern>, Rc<CoqType>)> = thir
                .params
                .iter()
                .filter_map(|param| match &param.pat {
                    Some(pattern) => {
                        let pattern = crate::thir_pattern::compile_pattern(env, pattern.as_ref());
                        let ty = compile_type(env, &param.ty);
                        Some((pattern, ty))
                    }
                    None => None,
                })
                .collect();
            let body = compile_expr(env, &thir, &expr_id).read();
            let body = args
                .iter()
                .enumerate()
                .rfold(body, |body, (index, (pattern, _))| {
                    let ty = body.ty.clone();

                    Rc::new(Expr {
                        kind: build_match(
                            Rc::new(Expr {
                                kind: Rc::new(ExprKind::LocalVar(format!("α{index}"))).alloc(None),
                                ty: None,
                            }),
                            vec![MatchArm {
                                pattern: pattern.clone(),
                                body,
                            }],
                            ty.clone(),
                        ),
                        ty,
                    })
                });
            let args = args
                .iter()
                .enumerate()
                .map(|(index, (_, ty))| (format!("α{index}"), Some(ty.clone())))
                .collect();

            Rc::new(ExprKind::Lambda {
                args,
                body,
                is_for_match: false,
            })
            .alloc(Some(ty))
        }
        thir::ExprKind::Literal { lit, neg } => match lit.node {
            rustc_ast::LitKind::Str(symbol, _) => {
                Rc::new(ExprKind::Literal(Literal::String(symbol.to_string())))
            }
            rustc_ast::LitKind::Char(c) => {
                Rc::new(ExprKind::Literal(Literal::Char(c))).alloc(Some(ty))
            }
            rustc_ast::LitKind::Int(i, _) => Rc::new(ExprKind::Literal(Literal::Integer {
                value: i,
                neg: *neg,
            }))
            .alloc(Some(ty)),
            rustc_ast::LitKind::Bool(c) => {
                Rc::new(ExprKind::Literal(Literal::Bool(c))).alloc(Some(ty))
            }
            _ => Rc::new(ExprKind::Literal(Literal::Error)),
        },
        thir::ExprKind::NonHirLiteral { lit, .. } => Rc::new(ExprKind::NonHirLiteral(*lit)),
        thir::ExprKind::ZstLiteral { .. } => match &expr.ty.kind() {
            TyKind::FnDef(def_id, generic_args) => {
                let key = env.tcx.def_key(def_id);
                let symbol = key.get_opt_name();
                let parent = env.tcx.opt_parent(*def_id).unwrap();
                let parent_kind = env.tcx.opt_def_kind(parent).unwrap();
                Rc::new(match parent_kind {
                    DefKind::Impl { .. } => {
                        let parent_type = env.tcx.type_of(parent).subst(env.tcx, generic_args);
                        let ty = compile_type(env, &parent_type);
                        let func = symbol.unwrap().to_string();
                        ExprKind::AssociatedFunction { ty, func }
                    }
                    DefKind::Trait => {
                        let parent_path = compile_def_id(env, parent);
                        let path = Path::concat(&[
                            parent_path.clone(),
                            Path::local(symbol.unwrap().as_str()),
                        ]);
                        let self_ty = generic_args.type_at(0);
                        let self_ty = crate::thir_ty::compile_type(env, &self_ty);

                        if Some((parent_path, self_ty.clone())) == env.current_trait_impl {
                            ExprKind::LocalVar(symbol.unwrap().to_string())
                        } else {
                            ExprKind::VarWithSelfTy { path, self_ty }
                        }
                    }
                    DefKind::Mod | DefKind::ForeignMod => {
                        ExprKind::Var(compile_def_id(env, *def_id))
                    }
                    DefKind::Variant => ExprKind::Constructor(compile_def_id(env, *def_id)),
                    _ => {
                        println!("unimplemented parent_kind: {:#?}", parent_kind);
                        println!("expression: {:#?}", expr);
                        ExprKind::Message("unimplemented parent_kind".to_string())
                    }
                })
                .alloc(Some(ty))
            }
            _ => {
                let error_message = "Expected a function name";
                env.tcx
                    .sess
                    .struct_span_warn(expr.span, error_message)
                    .emit();
                Rc::new(ExprKind::Message(error_message.to_string()))
            }
        },
        thir::ExprKind::NamedConst { def_id, substs, .. } => {
            let path = compile_def_id(env, *def_id);
            if substs.is_empty() {
                return Rc::new(ExprKind::Var(path));
            }
            let self_ty = substs.type_at(0);
            let self_ty = crate::thir_ty::compile_type(env, &self_ty);
            Rc::new(ExprKind::VarWithSelfTy { path, self_ty })
        }
        thir::ExprKind::ConstParam { def_id, .. } => {
            Rc::new(ExprKind::Var(compile_def_id(env, *def_id)))
        }
        thir::ExprKind::StaticRef { def_id, .. } => {
            Rc::new(ExprKind::Var(compile_def_id(env, *def_id)))
        }
        thir::ExprKind::InlineAsm(_) => Rc::new(ExprKind::LocalVar("InlineAssembly".to_string())),
        thir::ExprKind::OffsetOf { .. } => Rc::new(ExprKind::LocalVar("OffsetOf".to_string())),
        thir::ExprKind::ThreadLocalRef(def_id) => {
            Rc::new(ExprKind::Var(compile_def_id(env, *def_id)))
        }
        thir::ExprKind::Yield { value } => {
            let func = Rc::new(Expr {
                kind: Rc::new(ExprKind::LocalVar("yield".to_string())),
                ty: None,
            });
            let args = vec![compile_expr(env, thir, value)];
            Rc::new(ExprKind::Call {
                func,
                args,
                purity: Purity::Effectful,
                from_user: false,
            })
        }
    }
}

fn compile_stmts<'a>(
    env: &mut Env<'a>,
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
                    let pattern = crate::thir_pattern::compile_pattern(env, pattern);
                    let init = match initializer {
                        Some(initializer) => compile_expr(env, thir, initializer),
                        None => Expr::tt(),
                    };
                    let ty = body.ty.clone();
                    let kind = match pattern.as_ref() {
                        Pattern::Binding {
                            name,
                            pattern: None,
                            ..
                        } => Rc::new(ExprKind::Let {
                            is_monadic: false,
                            name: Some(name.clone()),
                            init: init.copy(),
                            body,
                        }),
                        _ => build_match(init, vec![MatchArm { pattern, body }], ty.clone()),
                    };
                    Rc::new(Expr { kind, ty })
                }
                thir::StmtKind::Expr { expr: expr_id, .. } => {
                    let init = compile_expr(env, thir, expr_id);
                    let ty = body.ty.clone();
                    Rc::new(Expr {
                        kind: Rc::new(ExprKind::Let {
                            is_monadic: false,
                            name: None,
                            init,
                            body,
                        }),
                        ty,
                    })
                }
            }
        },
    )
}

fn compile_block<'a>(
    env: &mut Env<'a>,
    thir: &rustc_middle::thir::Thir<'a>,
    block_id: &rustc_middle::thir::BlockId,
) -> Rc<Expr> {
    let block = thir.blocks.get(*block_id).unwrap();
    compile_stmts(env, thir, &block.stmts, block.expr)
}
