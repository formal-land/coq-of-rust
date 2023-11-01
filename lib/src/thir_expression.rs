use crate::env::*;
use crate::expression::*;
use crate::path::*;
use crate::pattern::*;
use crate::thir_ty::*;
use crate::ty::CoqType;
use rustc_hir::def::DefKind;
use rustc_middle::mir::{BinOp, BorrowKind, UnOp};
use rustc_middle::thir::{AdtExpr, ExprKind, LogicalOp, StmtKind};
use rustc_middle::ty::TyKind;

impl Expr {
    fn alloc(self) -> Expr {
        Expr::Call {
            func: Box::new(Expr::LocalVar("M.alloc".to_string())),
            args: vec![self],
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
    match &expr.kind {
        ExprKind::Scope { value, .. } => compile_expr(env, thir, value),
        ExprKind::Box { value } => {
            let value = compile_expr(env, thir, value);
            Expr::Call {
                func: Box::new(Expr::LocalVar(
                    "(alloc.boxed.Box _ alloc.boxed.Box.Default.A)::[\"new\"]".to_string(),
                )),
                args: vec![value],
            }
        }
        ExprKind::If {
            cond,
            then,
            else_opt,
            ..
        } => {
            let condition = Box::new(compile_expr(env, thir, cond));
            let success = Box::new(compile_expr(env, thir, then));
            let failure = match else_opt {
                Some(else_expr) => Box::new(compile_expr(env, thir, else_expr)),
                None => Box::new(tt()),
            };
            Expr::If {
                condition,
                success,
                failure,
            }
        }
        ExprKind::Call { fun, args, .. } => {
            let func = Box::new(compile_expr(env, thir, fun));
            let args = args
                .iter()
                .map(|arg| compile_expr(env, thir, arg))
                .collect();
            Expr::Call { func, args }
        }
        ExprKind::Deref { arg } => {
            let ty = Expr::Type(compile_type(env, &expr.ty));
            let arg = compile_expr(env, thir, arg);
            Expr::Call {
                func: Box::new(Expr::LocalVar("deref".to_string())),
                args: vec![arg, ty],
            }
        }
        ExprKind::Binary { op, lhs, rhs } => {
            let path = path_of_bin_op(op);
            let lhs = compile_expr(env, thir, lhs);
            let rhs = compile_expr(env, thir, rhs);
            Expr::Call {
                func: Box::new(Expr::Var(path)),
                args: vec![lhs, rhs],
            }
        }
        ExprKind::LogicalOp { op, lhs, rhs } => {
            let path = match op {
                LogicalOp::And => Path::new(&["BinOp", "and"]),
                LogicalOp::Or => Path::new(&["BinOp", "or"]),
            };
            let lhs = compile_expr(env, thir, lhs);
            let rhs = compile_expr(env, thir, rhs);
            Expr::Call {
                func: Box::new(Expr::Var(path)),
                args: vec![lhs, rhs],
            }
        }
        ExprKind::Unary { op, arg } => {
            let path = match op {
                UnOp::Not => Path::new(&["UnOp", "not"]),
                UnOp::Neg => Path::new(&["UnOp", "neg"]),
            };
            let arg = compile_expr(env, thir, arg);
            Expr::Call {
                func: Box::new(Expr::Var(path)),
                args: vec![arg],
            }
        }
        ExprKind::Cast { source } => {
            let func = Box::new(Expr::LocalVar("cast".to_string()));
            let source = compile_expr(env, thir, source);
            Expr::Call {
                func,
                args: vec![source],
            }
        }
        ExprKind::Use { source } => {
            let func = Box::new(Expr::LocalVar("use".to_string()));
            let source = compile_expr(env, thir, source);
            Expr::Call {
                func,
                args: vec![source],
            }
        }
        ExprKind::NeverToAny { source } => {
            let func = Box::new(Expr::LocalVar("never_to_any".to_string()));
            let source = compile_expr(env, thir, source);
            Expr::Call {
                func,
                args: vec![source],
            }
        }
        ExprKind::Pointer { source, cast } => {
            let func = Box::new(Expr::LocalVar("pointer_coercion".to_string()));
            let source = compile_expr(env, thir, source);
            let cast = Expr::Message(format!("{cast:?}"));
            Expr::Call {
                func,
                args: vec![cast, source],
            }
        }
        ExprKind::Loop { body, .. } => {
            let body = Box::new(Stmt::Expr(Box::new(compile_expr(env, thir, body))));
            Expr::Loop { body }
        }
        ExprKind::Let { expr, pat } => {
            let pat = Box::new(crate::thir_pattern::compile_pattern(env, pat));
            let init = Box::new(compile_expr(env, thir, expr));
            Expr::LetIf { pat, init }
        }
        ExprKind::Match { scrutinee, arms } => {
            let scrutinee = Box::new(compile_expr(env, thir, scrutinee));
            let arms = arms
                .iter()
                .map(|arm_id| {
                    let arm = thir.arms.get(*arm_id).unwrap();
                    let pat = crate::thir_pattern::compile_pattern(env, &arm.pattern);
                    let body = compile_expr(env, thir, &arm.body);
                    MatchArm { pat, body }
                })
                .collect();
            Expr::Match { scrutinee, arms }
        }
        ExprKind::Block { block: block_id } => {
            Expr::Block(Box::new(compile_block(env, thir, block_id)))
        }
        ExprKind::Assign { lhs, rhs } => {
            let func = Box::new(Expr::LocalVar("assign".to_string()));
            let args = vec![compile_expr(env, thir, lhs), compile_expr(env, thir, rhs)];
            Expr::Call { func, args }
        }
        ExprKind::AssignOp { op, lhs, rhs } => Expr::Call {
            func: Box::new(Expr::LocalVar("assign_op".to_string())),
            args: vec![
                Expr::LocalVar(compile_bin_op_kind(op.to_hir_binop())),
                compile_expr(env, thir, lhs),
                compile_expr(env, thir, rhs),
            ],
        },
        ExprKind::Field {
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
                    Expr::NamedField { base, name }
                }
                None => Expr::Message("Unknown Field".to_string()),
            }
        }
        ExprKind::Index { lhs, index } => {
            let base = Box::new(compile_expr(env, thir, lhs));
            let index = Box::new(compile_expr(env, thir, index));
            Expr::Index { base, index }
        }
        ExprKind::VarRef { id } => {
            let name = env.tcx.hir().opt_name(id.0).unwrap().to_string();
            Expr::LocalVar(name)
        }
        ExprKind::UpvarRef { var_hir_id, .. } => {
            let name = env.tcx.hir().opt_name(var_hir_id.0).unwrap().to_string();
            Expr::LocalVar(name)
        }
        ExprKind::Borrow { borrow_kind, arg } => {
            let func = match borrow_kind {
                BorrowKind::Shared | BorrowKind::Shallow => "borrow".to_string(),
                BorrowKind::Unique | BorrowKind::Mut { .. } => "borrow_mut".to_string(),
            };
            let ty = Expr::Type(Box::new(CoqType::remove_ref(*compile_type(env, &expr.ty))));
            let arg = compile_expr(env, thir, arg);
            Expr::Call {
                func: Box::new(Expr::LocalVar(func)),
                args: vec![arg, ty],
            }
        }
        ExprKind::AddressOf { mutability, arg } => {
            let func = match mutability {
                rustc_middle::mir::Mutability::Not => "addr_of".to_string(),
                rustc_middle::mir::Mutability::Mut => "addr_of_mut".to_string(),
            };
            let arg = compile_expr(env, thir, arg);
            Expr::Call {
                func: Box::new(Expr::LocalVar(func)),
                args: vec![arg],
            }
        }
        ExprKind::Break { .. } => Expr::ControlFlow(LoopControlFlow::Break),
        ExprKind::Continue { .. } => Expr::ControlFlow(LoopControlFlow::Continue),
        ExprKind::Return { value } => {
            let func = Box::new(Expr::LocalVar("Return".to_string()));
            let args = match value {
                Some(value) => vec![compile_expr(env, thir, value)],
                None => vec![tt()],
            };
            Expr::Call { func, args }
        }
        ExprKind::ConstBlock { did, .. } => Expr::Var(compile_def_id(env, *did)),
        ExprKind::Repeat { value, count } => {
            let func = Box::new(Expr::LocalVar("repeat".to_string()));
            let args = vec![
                compile_expr(env, thir, value),
                Expr::LocalVar(count.to_string()),
            ];
            Expr::Call { func, args }
        }
        ExprKind::Array { fields } => Expr::Array {
            elements: fields
                .iter()
                .map(|field| compile_expr(env, thir, field))
                .collect(),
        },
        ExprKind::Tuple { fields } => {
            let elements: Vec<_> = fields
                .iter()
                .map(|field| compile_expr(env, thir, field))
                .collect();
            if elements.is_empty() {
                tt()
            } else {
                Expr::Tuple { elements }
            }
        }
        ExprKind::Adt(adt_expr) => {
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
                Expr::StructTuple {
                    path,
                    fields,
                    struct_or_variant,
                }
                .alloc()
            } else {
                Expr::StructStruct {
                    path,
                    fields,
                    base: None,
                    struct_or_variant,
                }
                .alloc()
            }
        }
        ExprKind::PlaceTypeAscription { source, user_ty }
        | ExprKind::ValueTypeAscription { source, user_ty } => {
            let source = compile_expr(env, thir, source);
            match user_ty {
                None => source,
                Some(ty) => {
                    let ty = match &ty.value {
                        rustc_middle::ty::UserType::Ty(ty) => compile_type(env, ty),
                        rustc_middle::ty::UserType::TypeOf(_, _) => {
                            env.tcx
                                .sess
                                .struct_span_warn(expr.span, "Typeof expressions not supported.")
                                .emit();
                            Box::new(CoqType::Infer)
                        }
                    };
                    Expr::TypeAnnotation {
                        expr: Box::new(source),
                        ty,
                    }
                }
            }
        }
        ExprKind::Closure(closure) => {
            let rustc_middle::thir::ClosureExpr { closure_id, .. } = &**closure;
            let thir = env.tcx.thir_body(closure_id);
            let Ok((thir, expr_id)) = thir else {
                panic!("thir failed to compile");
            };
            let thir = thir.borrow();
            let body = Box::new(compile_expr(env, &thir, &expr_id));
            Expr::Lambda { args: vec![], body }
        }
        ExprKind::Literal { lit, neg } => Expr::Literal {
            literal: lit.node.clone(),
            neg: *neg,
        },
        ExprKind::NonHirLiteral { lit, .. } => Expr::NonHirLiteral(*lit),
        ExprKind::ZstLiteral { .. } => match &expr.ty.kind() {
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
                        Expr::AssociatedFunction { ty, func }
                    }
                    DefKind::Trait => {
                        let path = Path::concat(&[
                            compile_def_id(env, parent),
                            Path::local(symbol.unwrap().to_string()),
                        ]);
                        let self_ty = generic_args.type_at(0);
                        let self_ty = crate::thir_ty::compile_type(env, &self_ty);
                        Expr::VarWithSelfTy { path, self_ty }
                    }
                    DefKind::Mod => Expr::Var(compile_def_id(env, *def_id)),
                    _ => {
                        println!("unimplemented parent_kind: {:#?}", parent_kind);
                        Expr::Message("unimplemented parent_kind".to_string())
                    }
                }
            }
            _ => {
                let error_message = "Expected a function name";
                env.tcx
                    .sess
                    .struct_span_warn(expr.span, error_message)
                    .emit();
                Expr::Message(error_message.to_string())
            }
        },
        ExprKind::NamedConst { def_id, substs, .. } => {
            let path = compile_def_id(env, *def_id);
            if substs.is_empty() {
                return Expr::Var(path);
            }
            let self_ty = substs.type_at(0);
            let self_ty = crate::thir_ty::compile_type(env, &self_ty);
            Expr::VarWithSelfTy { path, self_ty }
        }
        ExprKind::ConstParam { def_id, .. } => Expr::Var(compile_def_id(env, *def_id)),
        ExprKind::StaticRef { def_id, .. } => Expr::Var(compile_def_id(env, *def_id)),
        ExprKind::InlineAsm(_) => Expr::LocalVar("InlineAssembly".to_string()),
        ExprKind::OffsetOf { .. } => Expr::LocalVar("OffsetOf".to_string()),
        ExprKind::ThreadLocalRef(def_id) => Expr::Var(compile_def_id(env, *def_id)),
        ExprKind::Yield { value } => {
            let func = Box::new(Expr::LocalVar("yield".to_string()));
            let args = vec![compile_expr(env, thir, value)];
            Expr::Call { func, args }
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
        Stmt::Expr(Box::new(match &expr_id {
            Some(expr_id) => compile_expr(env, thir, expr_id),
            None => tt(),
        })),
        |body, stmt_id| {
            let body = Box::new(body);
            let stmt = thir.stmts.get(*stmt_id).unwrap();
            match &stmt.kind {
                StmtKind::Let {
                    pattern,
                    initializer,
                    ..
                } => {
                    let pattern = Box::new(crate::thir_pattern::compile_pattern(env, pattern));
                    let init = match initializer {
                        Some(initializer) => Box::new(compile_expr(env, thir, initializer)),
                        None => Box::new(tt()),
                    };
                    Stmt::Let {
                        is_monadic: false,
                        ty: None,
                        pattern,
                        init,
                        body,
                    }
                }
                StmtKind::Expr { expr: expr_id, .. } => {
                    let init = Box::new(compile_expr(env, thir, expr_id));
                    Stmt::Let {
                        is_monadic: false,
                        pattern: Box::new(Pattern::Wild),
                        ty: None,
                        init,
                        body,
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
