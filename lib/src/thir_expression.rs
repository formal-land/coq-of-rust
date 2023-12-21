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
    pub(crate) fn alloc(self, ty: Option<Rc<CoqType>>) -> Self {
        ExprKind::Call {
            func: Box::new(Expr {
                kind: ExprKind::LocalVar("M.alloc".to_string()),
                ty: None,
            }),
            args: vec![Expr { kind: self, ty }],
            purity: Purity::Effectful,
            from_user: false,
        }
    }
}

fn path_of_bin_op(bin_op: &BinOp) -> (Path, Purity) {
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
        BinOp::Eq => (Path::new(&["BinOp", "Pure", "eq"]), Purity::Pure),
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
) -> Expr {
    let expr = thir.exprs.get(*expr_id).unwrap();
    let kind = compile_expr_kind(env, thir, expr_id);
    let ty = compile_type(env, &expr.ty).val();
    Expr { kind, ty: Some(ty) }
}

impl Expr {
    fn match_simple_call(&self, name_in: &[&str]) -> Option<Self> {
        if let ExprKind::Call {
            func,
            args,
            purity: _,
            from_user: _,
        } = &self.kind
        {
            if let ExprKind::LocalVar(func) = &func.kind {
                if name_in.contains(&func.as_str()) && args.len() == 1 {
                    return Some(args.get(0).unwrap().clone());
                }
            }
        }

        None
    }

    /// Return the borrowed expression if the expression is a borrow.
    fn match_borrow(&self) -> Option<Self> {
        self.match_simple_call(&["borrow", "borrow_mut"])
    }

    fn match_deref(&self) -> Option<Self> {
        self.match_simple_call(&["deref"])
    }

    pub(crate) fn read(self) -> Self {
        // If we read an allocated expression, we just return the expression.
        if let Some(expr) = self.match_simple_call(&["M.alloc"]) {
            return expr;
        }

        Expr {
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
            kind: ExprKind::Call {
                func: Box::new(Expr {
                    kind: ExprKind::LocalVar("M.read".to_string()),
                    ty: None,
                }),
                args: vec![self],
                purity: Purity::Effectful,
                from_user: false,
            },
        }
    }

    fn copy(self) -> Self {
        if self.match_simple_call(&["M.alloc"]).is_some() {
            return self;
        }

        Expr {
            ty: self.ty.clone(),
            kind: ExprKind::Call {
                func: Box::new(Expr {
                    kind: ExprKind::LocalVar("M.copy".to_string()),
                    ty: None,
                }),
                args: vec![self],
                purity: Purity::Effectful,
                from_user: false,
            },
        }
    }
}

fn compile_borrow(borrow_kind: &BorrowKind, arg: Expr) -> ExprKind {
    let func = match borrow_kind {
        BorrowKind::Shared | BorrowKind::Shallow => "borrow".to_string(),
        BorrowKind::Unique | BorrowKind::Mut { .. } => "borrow_mut".to_string(),
    };

    if let Some(derefed) = arg.match_deref() {
        if let Some(ty) = derefed.ty {
            if let Some((ref_name, _, _)) = ty.match_ref() {
                if (func == "borrow" && ref_name == "ref")
                    || (func == "borrow_mut" && ref_name == "mut_ref")
                {
                    return derefed.kind;
                }
            }
        }
    }

    ExprKind::Call {
        func: Box::new(Expr {
            kind: ExprKind::LocalVar(func),
            ty: None,
        }),
        args: vec![arg],
        purity: Purity::Pure,
        from_user: false,
    }
}

pub(crate) fn allocate_bindings(bindings: &[String], body: Box<Expr>) -> Box<Expr> {
    bindings.iter().rfold(body, |body, binding| {
        Box::new(Expr {
            ty: body.ty.clone(),
            kind: ExprKind::Let {
                is_monadic: false,
                pattern: Box::new(Pattern::Variable(binding.clone())),
                init: Box::new(Expr {
                    kind: ExprKind::LocalVar(binding.clone()).alloc(None),
                    ty: None,
                }),
                body,
            },
        })
    })
}

/// Allocate all the bindings in the [pattern] to some [M.Val]
fn allocate_bindings_in_pattern(pattern: &Pattern, body: Box<Expr>) -> Box<Expr> {
    let bindings = pattern.get_bindings();
    allocate_bindings(&bindings, body)
}

fn compile_expr_kind<'a>(
    env: &mut Env<'a>,
    thir: &rustc_middle::thir::Thir<'a>,
    expr_id: &rustc_middle::thir::ExprId,
) -> ExprKind {
    let expr = thir.exprs.get(*expr_id).unwrap();
    let ty = compile_type(env, &expr.ty);

    match &expr.kind {
        thir::ExprKind::Scope { value, .. } => compile_expr_kind(env, thir, value),
        thir::ExprKind::Box { value } => {
            let value = compile_expr(env, thir, value);
            ExprKind::Call {
                func: Box::new(Expr {
                    kind: ExprKind::LocalVar(
                        "(alloc.boxed.Box _ alloc.boxed.Box.Default.A)::[\"new\"]".to_string(),
                    ),
                    ty: None,
                }),
                args: vec![value],
                purity: Purity::Effectful,
                from_user: true,
            }
        }
        thir::ExprKind::If {
            cond,
            then,
            else_opt,
            ..
        } => {
            let condition = Box::new(compile_expr(env, thir, cond).read());
            let success = Box::new(compile_expr(env, thir, then));
            let failure = match else_opt {
                Some(else_expr) => Box::new(compile_expr(env, thir, else_expr)),
                None => Box::new(Expr::tt()),
            };
            ExprKind::If {
                condition,
                success,
                failure,
            }
        }
        thir::ExprKind::Call { fun, args, .. } => {
            let args = args
                .iter()
                .map(|arg| compile_expr(env, thir, arg).read())
                .collect();
            let func = compile_expr(env, thir, fun);
            let (purity, from_user) = match &func.match_simple_call(&["M.alloc"]) {
                Some(Expr {
                    kind: ExprKind::Constructor(_),
                    ..
                }) => (Purity::Pure, false),
                _ => (Purity::Effectful, true),
            };
            let func = Box::new(func.read());

            ExprKind::Call {
                func,
                args,
                purity,
                from_user,
            }
            .alloc(Some(ty))
        }
        thir::ExprKind::Deref { arg } => {
            let arg = compile_expr(env, thir, arg).read();

            if let Some(borrowed) = Expr::match_borrow(&arg) {
                return borrowed.kind;
            }

            ExprKind::Call {
                func: Box::new(Expr {
                    kind: ExprKind::LocalVar("deref".to_string()),
                    ty: None,
                }),
                args: vec![arg],
                purity: Purity::Pure,
                from_user: false,
            }
        }
        thir::ExprKind::Binary { op, lhs, rhs } => {
            let (path, purity) = path_of_bin_op(op);
            let lhs = compile_expr(env, thir, lhs);
            let rhs = compile_expr(env, thir, rhs);
            ExprKind::Call {
                func: Box::new(Expr {
                    kind: ExprKind::Var(path),
                    ty: None,
                }),
                args: vec![lhs.read(), rhs.read()],
                purity,
                from_user: false,
            }
            .alloc(Some(ty))
        }
        thir::ExprKind::LogicalOp { op, lhs, rhs } => {
            let path = match op {
                LogicalOp::And => Path::new(&["BinOp", "Pure", "and"]),
                LogicalOp::Or => Path::new(&["BinOp", "Pure", "or"]),
            };
            let lhs = compile_expr(env, thir, lhs);
            let rhs = compile_expr(env, thir, rhs);
            ExprKind::Call {
                func: Box::new(Expr {
                    kind: ExprKind::Var(path),
                    ty: None,
                }),
                args: vec![lhs.read(), rhs.read()],
                purity: Purity::Pure,
                from_user: false,
            }
            .alloc(Some(ty))
        }
        thir::ExprKind::Unary { op, arg } => {
            let (path, purity) = match op {
                UnOp::Not => (Path::new(&["UnOp", "not"]), Purity::Pure),
                UnOp::Neg => (Path::new(&["UnOp", "neg"]), Purity::Effectful),
            };
            let arg = compile_expr(env, thir, arg);
            ExprKind::Call {
                func: Box::new(Expr {
                    kind: ExprKind::Var(path),
                    ty: None,
                }),
                args: vec![arg.read()],
                purity,
                from_user: false,
            }
            .alloc(Some(ty))
        }
        thir::ExprKind::Cast { source } => {
            let func = Box::new(Expr {
                kind: ExprKind::LocalVar("cast".to_string()),
                ty: None,
            });
            let source = compile_expr(env, thir, source);
            ExprKind::Call {
                func,
                args: vec![source.read()],
                purity: Purity::Effectful,
                from_user: false,
            }
            .alloc(Some(ty))
        }
        thir::ExprKind::Use { source } => {
            let source = compile_expr(env, thir, source);
            ExprKind::Use(Box::new(source))
        }
        thir::ExprKind::NeverToAny { source } => {
            let func = Box::new(Expr {
                kind: ExprKind::LocalVar("never_to_any".to_string()),
                ty: None,
            });
            let source = compile_expr(env, thir, source);
            ExprKind::Call {
                func,
                args: vec![source.read()],
                purity: Purity::Effectful,
                from_user: false,
            }
            .alloc(Some(ty))
        }
        thir::ExprKind::Pointer { source, cast } => {
            let func = Box::new(Expr {
                kind: ExprKind::LocalVar("pointer_coercion".to_string()),
                ty: None,
            });
            let source = compile_expr(env, thir, source);
            let cast = Expr {
                kind: ExprKind::Message(format!("{cast:?}")),
                ty: None,
            };
            ExprKind::Call {
                func,
                args: vec![cast, source],
                purity: Purity::Pure,
                from_user: false,
            }
        }
        thir::ExprKind::Loop { body, .. } => {
            let body = Box::new(compile_expr(env, thir, body));
            ExprKind::Loop { body }
        }
        thir::ExprKind::Let { expr, pat } => {
            let pat = Box::new(crate::thir_pattern::compile_pattern(env, pat));
            let init = Box::new(compile_expr(env, thir, expr));
            ExprKind::LetIf { pat, init }
        }
        thir::ExprKind::Match { scrutinee, arms } => {
            let scrutinee = Box::new(compile_expr(env, thir, scrutinee).read());
            let arms = arms
                .iter()
                .map(|arm_id| {
                    let arm = thir.arms.get(*arm_id).unwrap();
                    let pattern = crate::thir_pattern::compile_pattern(env, &arm.pattern);
                    let body = Box::new(compile_expr(env, thir, &arm.body));
                    let body = allocate_bindings_in_pattern(&pattern, body);
                    MatchArm {
                        pattern,
                        body: *body,
                    }
                })
                .collect();
            ExprKind::Match { scrutinee, arms }
        }
        thir::ExprKind::Block { block: block_id } => compile_block(env, thir, block_id).kind,
        thir::ExprKind::Assign { lhs, rhs } => {
            let func = Box::new(Expr {
                kind: ExprKind::LocalVar("assign".to_string()),
                ty: None,
            });
            let args = vec![
                compile_expr(env, thir, lhs),
                compile_expr(env, thir, rhs).read(),
            ];
            ExprKind::Call {
                func,
                args,
                purity: Purity::Effectful,
                from_user: false,
            }
        }
        thir::ExprKind::AssignOp { op, lhs, rhs } => {
            let (path, purity) = path_of_bin_op(op);
            let lhs = compile_expr(env, thir, lhs);
            let rhs = compile_expr(env, thir, rhs);

            ExprKind::Let {
                is_monadic: false,
                pattern: Box::new(Pattern::Variable("β".to_string())),
                init: Box::new(lhs),
                body: Box::new(Expr {
                    kind: ExprKind::Call {
                        func: Box::new(Expr {
                            kind: ExprKind::Var(Path::new(&["assign"])),
                            ty: None,
                        }),
                        args: vec![
                            Expr {
                                kind: ExprKind::LocalVar("β".to_string()),
                                ty: None,
                            },
                            Expr {
                                kind: ExprKind::Call {
                                    func: Box::new(Expr {
                                        kind: ExprKind::Var(path),
                                        ty: None,
                                    }),
                                    args: vec![
                                        Expr {
                                            kind: ExprKind::LocalVar("β".to_string()),
                                            ty: None,
                                        }
                                        .read(),
                                        rhs.read(),
                                    ],
                                    purity,
                                    from_user: false,
                                },
                                ty: None,
                            },
                        ],
                        purity: Purity::Effectful,
                        from_user: false,
                    },
                    ty: None,
                }),
            }
        }
        thir::ExprKind::Field {
            lhs,
            variant_index,
            name,
        } => {
            let base = Box::new(compile_expr(env, thir, lhs));
            let ty = thir.exprs.get(*lhs).unwrap().ty;
            match ty.ty_adt_def() {
                Some(adt_def) => {
                    let variant = adt_def.variant(*variant_index);
                    let name = variant.fields.get(*name).unwrap().name.to_string();
                    ExprKind::NamedField { base, name }
                }
                None => ExprKind::Message("Unknown Field".to_string()),
            }
        }
        thir::ExprKind::Index { lhs, index } => {
            let base = Box::new(compile_expr(env, thir, lhs));
            let index = Box::new(compile_expr(env, thir, index));
            ExprKind::Index { base, index }
        }
        thir::ExprKind::VarRef { id } => {
            let name = to_valid_coq_name(env.tcx.hir().opt_name(id.0).unwrap().as_str());
            ExprKind::LocalVar(name)
        }
        thir::ExprKind::UpvarRef { var_hir_id, .. } => {
            let name = to_valid_coq_name(env.tcx.hir().opt_name(var_hir_id.0).unwrap().as_str());
            ExprKind::LocalVar(name)
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
            ExprKind::Call {
                func: Box::new(Expr {
                    kind: ExprKind::LocalVar(func),
                    ty: None,
                }),
                args: vec![arg],
                purity: Purity::Pure,
                from_user: false,
            }
        }
        thir::ExprKind::Break { .. } => ExprKind::ControlFlow(LoopControlFlow::Break),
        thir::ExprKind::Continue { .. } => ExprKind::ControlFlow(LoopControlFlow::Continue),
        thir::ExprKind::Return { value } => {
            let value = match value {
                Some(value) => compile_expr(env, thir, value).read(),
                None => Expr::tt(),
            };
            ExprKind::Return(Box::new(value))
        }
        thir::ExprKind::ConstBlock { did, .. } => ExprKind::Var(compile_def_id(env, *did)),
        thir::ExprKind::Repeat { value, count } => {
            let func = Box::new(Expr {
                kind: ExprKind::LocalVar("repeat".to_string()),
                ty: None,
            });
            let args = vec![
                compile_expr(env, thir, value).read(),
                Expr {
                    kind: ExprKind::LocalVar(count.to_string()),
                    ty: None,
                },
            ];
            ExprKind::Call {
                func,
                args,
                purity: Purity::Pure,
                from_user: false,
            }
            .alloc(Some(ty))
        }
        thir::ExprKind::Array { fields } => ExprKind::Array {
            elements: fields
                .iter()
                .map(|field| compile_expr(env, thir, field).read())
                .collect(),
        }
        .alloc(Some(ty)),
        thir::ExprKind::Tuple { fields } => {
            let elements: Vec<_> = fields
                .iter()
                .map(|field| compile_expr(env, thir, field).read())
                .collect();
            if elements.is_empty() {
                ExprKind::tt()
            } else {
                ExprKind::Tuple { elements }.alloc(Some(ty))
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
                return ExprKind::StructUnit {
                    path,
                    struct_or_variant,
                }
                .alloc(Some(ty));
            }
            if is_a_tuple {
                let fields = fields.into_iter().map(|(_, pattern)| pattern).collect();
                ExprKind::StructTuple {
                    path,
                    fields,
                    struct_or_variant,
                }
                .alloc(Some(ty))
            } else {
                ExprKind::StructStruct {
                    path,
                    fields,
                    base: None,
                    struct_or_variant,
                }
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
            let args: Vec<(Pattern, Rc<CoqType>)> = thir
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
            let body = Box::new(compile_expr(env, &thir, &expr_id).read());
            let body = allocate_bindings(
                &args
                    .iter()
                    .map(|(pattern, _)| pattern.get_bindings())
                    .collect::<Vec<_>>()
                    .concat(),
                body,
            );

            ExprKind::Lambda { args, body }.alloc(Some(ty))
        }
        thir::ExprKind::Literal { lit, neg } => match lit.node {
            rustc_ast::LitKind::Str(symbol, _) => {
                ExprKind::Literal(Literal::String(symbol.to_string()))
            }
            rustc_ast::LitKind::Char(c) => ExprKind::Literal(Literal::Char(c)).alloc(Some(ty)),
            rustc_ast::LitKind::Int(i, _) => ExprKind::Literal(Literal::Integer {
                value: i,
                neg: *neg,
            })
            .alloc(Some(ty)),
            rustc_ast::LitKind::Bool(c) => ExprKind::Literal(Literal::Bool(c)).alloc(Some(ty)),
            _ => ExprKind::Literal(Literal::Error),
        },
        thir::ExprKind::NonHirLiteral { lit, .. } => ExprKind::NonHirLiteral(*lit),
        thir::ExprKind::ZstLiteral { .. } => match &expr.ty.kind() {
            TyKind::FnDef(def_id, generic_args) => {
                let key = env.tcx.def_key(def_id);
                let symbol = key.get_opt_name();
                let parent = env.tcx.opt_parent(*def_id).unwrap();
                let parent_kind = env.tcx.opt_def_kind(parent).unwrap();
                match parent_kind {
                    DefKind::Impl { .. } => {
                        let parent_type = env.tcx.type_of(parent).subst(env.tcx, generic_args);
                        let ty = compile_type(env, &parent_type);
                        let func = symbol.unwrap().to_string();
                        ExprKind::AssociatedFunction { ty, func }
                    }
                    DefKind::Trait => {
                        let path = Path::concat(&[
                            compile_def_id(env, parent),
                            Path::local(symbol.unwrap().as_str()),
                        ]);
                        let self_ty = generic_args.type_at(0);
                        let self_ty = crate::thir_ty::compile_type(env, &self_ty);
                        ExprKind::VarWithSelfTy { path, self_ty }
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
                }
                .alloc(Some(ty))
            }
            _ => {
                let error_message = "Expected a function name";
                env.tcx
                    .sess
                    .struct_span_warn(expr.span, error_message)
                    .emit();
                ExprKind::Message(error_message.to_string())
            }
        },
        thir::ExprKind::NamedConst { def_id, substs, .. } => {
            let path = compile_def_id(env, *def_id);
            if substs.is_empty() {
                return ExprKind::Var(path);
            }
            let self_ty = substs.type_at(0);
            let self_ty = crate::thir_ty::compile_type(env, &self_ty);
            ExprKind::VarWithSelfTy { path, self_ty }
        }
        thir::ExprKind::ConstParam { def_id, .. } => ExprKind::Var(compile_def_id(env, *def_id)),
        thir::ExprKind::StaticRef { def_id, .. } => ExprKind::Var(compile_def_id(env, *def_id)),
        thir::ExprKind::InlineAsm(_) => ExprKind::LocalVar("InlineAssembly".to_string()),
        thir::ExprKind::OffsetOf { .. } => ExprKind::LocalVar("OffsetOf".to_string()),
        thir::ExprKind::ThreadLocalRef(def_id) => ExprKind::Var(compile_def_id(env, *def_id)),
        thir::ExprKind::Yield { value } => {
            let func = Box::new(Expr {
                kind: ExprKind::LocalVar("yield".to_string()),
                ty: None,
            });
            let args = vec![compile_expr(env, thir, value)];
            ExprKind::Call {
                func,
                args,
                purity: Purity::Effectful,
                from_user: false,
            }
        }
    }
}

fn compile_stmts<'a>(
    env: &mut Env<'a>,
    thir: &rustc_middle::thir::Thir<'a>,
    stmt_ids: &[rustc_middle::thir::StmtId],
    expr_id: Option<rustc_middle::thir::ExprId>,
) -> Expr {
    stmt_ids.iter().rev().fold(
        {
            match &expr_id {
                Some(expr_id) => compile_expr(env, thir, expr_id),
                None => Expr::tt(),
            }
        },
        |body, stmt_id| {
            let body = Box::new(body);
            let stmt = thir.stmts.get(*stmt_id).unwrap();
            match &stmt.kind {
                thir::StmtKind::Let {
                    pattern,
                    initializer,
                    ..
                } => {
                    let pattern = Box::new(crate::thir_pattern::compile_pattern(env, pattern));
                    let init = match initializer {
                        Some(initializer) => compile_expr(env, thir, initializer),
                        None => Expr::tt(),
                    };
                    let (init, body) = if matches!(pattern.as_ref(), Pattern::Variable(_)) {
                        (init.copy(), body)
                    } else {
                        (
                            init.read(),
                            allocate_bindings_in_pattern(pattern.as_ref(), body),
                        )
                    };
                    let ty = body.ty.clone();
                    Expr {
                        kind: ExprKind::Let {
                            is_monadic: false,
                            pattern,
                            init: Box::new(init),
                            body,
                        },
                        ty,
                    }
                }
                thir::StmtKind::Expr { expr: expr_id, .. } => {
                    let init = Box::new(compile_expr(env, thir, expr_id));
                    let ty = body.ty.clone();
                    Expr {
                        kind: ExprKind::Let {
                            is_monadic: false,
                            pattern: Box::new(Pattern::Wild),
                            init,
                            body,
                        },
                        ty,
                    }
                }
            }
        },
    )
}

fn compile_block<'a>(
    env: &mut Env<'a>,
    thir: &rustc_middle::thir::Thir<'a>,
    block_id: &rustc_middle::thir::BlockId,
) -> Expr {
    let block = thir.blocks.get(*block_id).unwrap();
    compile_stmts(env, thir, &block.stmts, block.expr)
}
