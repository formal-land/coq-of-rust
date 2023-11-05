use crate::env::*;
use crate::expression::*;
use crate::path::*;
use crate::pattern::*;
use crate::thir_ty::*;
use rustc_hir::def::DefKind;
use rustc_middle::mir::{BinOp, BorrowKind, UnOp};
use rustc_middle::thir;
use rustc_middle::thir::{AdtExpr, LogicalOp};
use rustc_middle::ty::TyKind;

impl ExprKind {
    pub(crate) fn alloc(self) -> Self {
        ExprKind::Call {
            func: Box::new(Expr {
                kind: ExprKind::LocalVar("M.alloc".to_string()),
                ty: None,
            }),
            args: vec![Expr {
                kind: self,
                ty: None,
            }],
        }
    }
}

fn path_of_bin_op(bin_op: &BinOp) -> Path {
    match bin_op {
        BinOp::Add => Path::new(&["BinOp", "add"]),
        BinOp::Sub => Path::new(&["BinOp", "sub"]),
        BinOp::Mul => Path::new(&["BinOp", "mul"]),
        BinOp::Div => Path::new(&["BinOp", "div"]),
        BinOp::Rem => Path::new(&["BinOp", "rem"]),
        BinOp::BitXor => Path::new(&["BinOp", "bit_xor"]),
        BinOp::BitAnd => Path::new(&["BinOp", "bit_and"]),
        BinOp::BitOr => Path::new(&["BinOp", "bit_or"]),
        BinOp::Shl => Path::new(&["BinOp", "shl"]),
        BinOp::Shr => Path::new(&["BinOp", "shr"]),
        BinOp::Eq => Path::new(&["BinOp", "eq"]),
        BinOp::Ne => Path::new(&["BinOp", "ne"]),
        BinOp::Lt => Path::new(&["BinOp", "lt"]),
        BinOp::Le => Path::new(&["BinOp", "le"]),
        BinOp::Ge => Path::new(&["BinOp", "ge"]),
        BinOp::Gt => Path::new(&["BinOp", "gt"]),
        BinOp::Offset => Path::new(&["BinOp", "offset"]),
    }
}

pub(crate) fn compile_expr<'a>(
    env: &mut Env<'a>,
    thir: &rustc_middle::thir::Thir<'a>,
    expr_id: &rustc_middle::thir::ExprId,
) -> Expr {
    let expr = thir.exprs.get(*expr_id).unwrap();
    let kind = compile_expr_kind(env, thir, expr_id);
    let ty = compile_type(env, &expr.ty);
    Expr { kind, ty: Some(ty) }
}

fn compile_expr_kind<'a>(
    env: &mut Env<'a>,
    thir: &rustc_middle::thir::Thir<'a>,
    expr_id: &rustc_middle::thir::ExprId,
) -> ExprKind {
    let expr = thir.exprs.get(*expr_id).unwrap();
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
            }
        }
        thir::ExprKind::If {
            cond,
            then,
            else_opt,
            ..
        } => {
            let condition = Box::new(compile_expr(env, thir, cond));
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
            let func = Box::new(compile_expr(env, thir, fun));
            let args = args
                .iter()
                .map(|arg| compile_expr(env, thir, arg))
                .collect();
            ExprKind::Call { func, args }
        }
        thir::ExprKind::Deref { arg } => {
            let arg = compile_expr(env, thir, arg);
            ExprKind::Call {
                func: Box::new(Expr {
                    kind: ExprKind::LocalVar("deref".to_string()),
                    ty: None,
                }),
                args: vec![arg],
            }
        }
        thir::ExprKind::Binary { op, lhs, rhs } => {
            let path = path_of_bin_op(op);
            let lhs = compile_expr(env, thir, lhs);
            let rhs = compile_expr(env, thir, rhs);
            ExprKind::Call {
                func: Box::new(Expr {
                    kind: ExprKind::Var(path),
                    ty: None,
                }),
                args: vec![lhs, rhs],
            }
        }
        thir::ExprKind::LogicalOp { op, lhs, rhs } => {
            let path = match op {
                LogicalOp::And => Path::new(&["BinOp", "and"]),
                LogicalOp::Or => Path::new(&["BinOp", "or"]),
            };
            let lhs = compile_expr(env, thir, lhs);
            let rhs = compile_expr(env, thir, rhs);
            ExprKind::Call {
                func: Box::new(Expr {
                    kind: ExprKind::Var(path),
                    ty: None,
                }),
                args: vec![lhs, rhs],
            }
        }
        thir::ExprKind::Unary { op, arg } => {
            let path = match op {
                UnOp::Not => Path::new(&["UnOp", "not"]),
                UnOp::Neg => Path::new(&["UnOp", "neg"]),
            };
            let arg = compile_expr(env, thir, arg);
            ExprKind::Call {
                func: Box::new(Expr {
                    kind: ExprKind::Var(path),
                    ty: None,
                }),
                args: vec![arg],
            }
        }
        thir::ExprKind::Cast { source } => {
            let func = Box::new(Expr {
                kind: ExprKind::LocalVar("cast".to_string()),
                ty: None,
            });
            let source = compile_expr(env, thir, source);
            ExprKind::Call {
                func,
                args: vec![source],
            }
        }
        thir::ExprKind::Use { source } => {
            let func = Box::new(Expr {
                kind: ExprKind::LocalVar("use".to_string()),
                ty: None,
            });
            let source = compile_expr(env, thir, source);
            ExprKind::Call {
                func,
                args: vec![source],
            }
        }
        thir::ExprKind::NeverToAny { source } => {
            let func = Box::new(Expr {
                kind: ExprKind::LocalVar("never_to_any".to_string()),
                ty: None,
            });
            let source = compile_expr(env, thir, source);
            ExprKind::Call {
                func,
                args: vec![source],
            }
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
            }
        }
        thir::ExprKind::Loop { body, .. } => {
            let body = compile_expr(env, thir, body);
            let ty = body.ty.clone();
            let body = Box::new(Stmt {
                kind: StmtKind::Expr(Box::new(body)),
                ty,
            });
            ExprKind::Loop { body }
        }
        thir::ExprKind::Let { expr, pat } => {
            let pat = Box::new(crate::thir_pattern::compile_pattern(env, pat));
            let init = Box::new(compile_expr(env, thir, expr));
            ExprKind::LetIf { pat, init }
        }
        thir::ExprKind::Match { scrutinee, arms } => {
            let scrutinee = Box::new(Expr {
                kind: ExprKind::Call {
                    func: Box::new(Expr {
                        kind: ExprKind::LocalVar("M.read".to_string()),
                        ty: None,
                    }),
                    args: vec![compile_expr(env, thir, scrutinee)],
                },
                ty: None,
            });
            let arms = arms
                .iter()
                .map(|arm_id| {
                    let arm = thir.arms.get(*arm_id).unwrap();
                    let pat = crate::thir_pattern::compile_pattern(env, &arm.pattern);
                    let body = compile_expr(env, thir, &arm.body);
                    MatchArm { pat, body }
                })
                .collect();
            ExprKind::Match { scrutinee, arms }
        }
        thir::ExprKind::Block { block: block_id } => {
            ExprKind::Block(Box::new(compile_block(env, thir, block_id)))
        }
        thir::ExprKind::Assign { lhs, rhs } => {
            let func = Box::new(Expr {
                kind: ExprKind::LocalVar("assign".to_string()),
                ty: None,
            });
            let args = vec![compile_expr(env, thir, lhs), compile_expr(env, thir, rhs)];
            ExprKind::Call { func, args }
        }
        thir::ExprKind::AssignOp { op, lhs, rhs } => ExprKind::Call {
            func: Box::new(Expr {
                kind: ExprKind::LocalVar("assign_op".to_string()),
                ty: None,
            }),
            args: vec![
                Expr {
                    kind: ExprKind::LocalVar(compile_bin_op_kind(op.to_hir_binop())),
                    ty: None,
                },
                compile_expr(env, thir, lhs),
                compile_expr(env, thir, rhs),
            ],
        },
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
            let name = env.tcx.hir().opt_name(id.0).unwrap().to_string();
            ExprKind::LocalVar(name)
        }
        thir::ExprKind::UpvarRef { var_hir_id, .. } => {
            let name = env.tcx.hir().opt_name(var_hir_id.0).unwrap().to_string();
            ExprKind::LocalVar(name)
        }
        thir::ExprKind::Borrow { borrow_kind, arg } => {
            let func = match borrow_kind {
                BorrowKind::Shared | BorrowKind::Shallow => "borrow".to_string(),
                BorrowKind::Unique | BorrowKind::Mut { .. } => "borrow_mut".to_string(),
            };
            let arg = compile_expr(env, thir, arg);
            ExprKind::Call {
                func: Box::new(Expr {
                    kind: ExprKind::LocalVar(func),
                    ty: None,
                }),
                args: vec![arg],
            }
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
            }
        }
        thir::ExprKind::Break { .. } => ExprKind::ControlFlow(LoopControlFlow::Break),
        thir::ExprKind::Continue { .. } => ExprKind::ControlFlow(LoopControlFlow::Continue),
        thir::ExprKind::Return { value } => {
            let func = Box::new(Expr {
                kind: ExprKind::LocalVar("M.return_".to_string()),
                ty: None,
            });
            let args = match value {
                Some(value) => vec![compile_expr(env, thir, value)],
                None => vec![Expr::tt()],
            };
            ExprKind::Call { func, args }
        }
        thir::ExprKind::ConstBlock { did, .. } => ExprKind::Var(compile_def_id(env, *did)),
        thir::ExprKind::Repeat { value, count } => {
            let func = Box::new(Expr {
                kind: ExprKind::LocalVar("repeat".to_string()),
                ty: None,
            });
            let args = vec![
                compile_expr(env, thir, value),
                Expr {
                    kind: ExprKind::LocalVar(count.to_string()),
                    ty: None,
                },
            ];
            ExprKind::Call { func, args }
        }
        thir::ExprKind::Array { fields } => ExprKind::Array {
            elements: fields
                .iter()
                .map(|field| compile_expr(env, thir, field))
                .collect(),
        }
        .alloc(),
        thir::ExprKind::Tuple { fields } => {
            let elements: Vec<_> = fields
                .iter()
                .map(|field| compile_expr(env, thir, field))
                .collect();
            if elements.is_empty() {
                ExprKind::tt()
            } else {
                ExprKind::Tuple { elements }.alloc()
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
                        variant.fields.get(field.name).unwrap().name.to_string(),
                        compile_expr(env, thir, &field.expr),
                    )
                })
                .collect();
            let is_a_tuple = fields
                .iter()
                .all(|(name, _)| name.starts_with(|c: char| c.is_ascii_digit()));
            let struct_or_variant = if adt_def.is_enum() {
                StructOrVariant::Variant
            } else {
                StructOrVariant::Struct
            };
            if is_a_tuple {
                let fields = fields.into_iter().map(|(_, pattern)| pattern).collect();
                ExprKind::StructTuple {
                    path,
                    fields,
                    struct_or_variant,
                }
                .alloc()
            } else {
                ExprKind::StructStruct {
                    path,
                    fields,
                    base: None,
                    struct_or_variant,
                }
                .alloc()
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
            let body = Box::new(compile_expr(env, &thir, &expr_id));
            ExprKind::Lambda { args: vec![], body }
        }
        thir::ExprKind::Literal { lit, neg } => ExprKind::Literal {
            literal: lit.node.clone(),
            neg: *neg,
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
                            Path::local(symbol.unwrap().to_string()),
                        ]);
                        let self_ty = generic_args.type_at(0);
                        let self_ty = crate::thir_ty::compile_type(env, &self_ty);
                        ExprKind::VarWithSelfTy { path, self_ty }
                    }
                    DefKind::Mod => ExprKind::Var(compile_def_id(env, *def_id)),
                    _ => {
                        println!("unimplemented parent_kind: {:#?}", parent_kind);
                        ExprKind::Message("unimplemented parent_kind".to_string())
                    }
                }
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
            ExprKind::Call { func, args }
        }
    }
}

fn compile_stmts<'a>(
    env: &mut Env<'a>,
    thir: &rustc_middle::thir::Thir<'a>,
    stmt_ids: &[rustc_middle::thir::StmtId],
    expr_id: Option<rustc_middle::thir::ExprId>,
) -> Stmt {
    stmt_ids.iter().rev().fold(
        {
            let init = match &expr_id {
                Some(expr_id) => compile_expr(env, thir, expr_id),
                None => Expr::tt(),
            };
            let ty = init.ty.clone();
            Stmt {
                kind: StmtKind::Expr(Box::new(init)),
                ty,
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
                        Some(initializer) => Box::new(compile_expr(env, thir, initializer)),
                        None => Box::new(Expr::tt()),
                    };
                    let ty = body.ty.clone();
                    Stmt {
                        kind: StmtKind::Let {
                            is_monadic: false,
                            pattern,
                            init,
                            body,
                        },
                        ty,
                    }
                }
                thir::StmtKind::Expr { expr: expr_id, .. } => {
                    let init = Box::new(compile_expr(env, thir, expr_id));
                    let ty = body.ty.clone();
                    Stmt {
                        kind: StmtKind::Let {
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
) -> Stmt {
    let block = thir.blocks.get(*block_id).unwrap();
    compile_stmts(env, thir, &block.stmts, block.expr)
}
