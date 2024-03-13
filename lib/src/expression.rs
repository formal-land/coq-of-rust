use crate::coq;
use crate::env::*;
use crate::path::*;
use crate::pattern::*;
use crate::render::*;
use crate::ty::*;
use core::panic;
use rustc_middle::query::plumbing::IntoQueryParam;
use std::rc::Rc;

/// Struct [FreshVars] represents a set of fresh variables
#[derive(Clone, Debug)]
pub(crate) struct FreshVars(u64);

impl FreshVars {
    pub(crate) fn new() -> Self {
        FreshVars(0)
    }

    fn next(&self) -> (String, Self) {
        (format!("α{}", self.0), FreshVars(self.0 + 1))
    }
}

/// Struct [MatchArm] represents a pattern-matching branch: [pat] is the
/// matched pattern and [body] the expression on which it is mapped
#[derive(Debug)]
pub(crate) struct MatchArm {
    pub(crate) pattern: Rc<Pattern>,
    pub(crate) body: Rc<Expr>,
}

/// [LoopControlFlow] represents the expressions responsible for
/// the flow of control in a loop
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum LoopControlFlow {
    Continue,
    Break,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum CallKind {
    /// Pure call of a function, written with a space following the syntax
    /// of Coq.
    Pure,
    /// Like [Pure] but with a result in the monad.
    Effectful,
    /// Call of a Rust closure, using the monadic operator `M.call`.
    Closure,
}

#[derive(Debug, Eq, PartialEq)]
pub(crate) struct LiteralInteger {
    pub(crate) name: String,
    pub(crate) negative_sign: bool,
    pub(crate) value: u128,
}

#[derive(Debug, Eq, PartialEq)]
pub(crate) enum Literal {
    Bool(bool),
    Integer(LiteralInteger),
    Char(char),
    String(String),
    Error,
}

/// Enum [Expr] represents the AST of rust terms.
#[derive(Debug, Eq, PartialEq)]
pub(crate) enum Expr {
    Pure(Rc<Expr>),
    LocalVar(String),
    GetConst(Path),
    GetFunction {
        func: Path,
        generic_tys: Vec<Rc<CoqType>>,
    },
    Constructor(Path),
    TraitMethod {
        trait_name: Path,
        method_name: String,
        self_and_generic_tys: Vec<(String, Rc<CoqType>)>,
    },
    AssociatedFunction {
        ty: Rc<CoqType>,
        func: String,
    },
    Literal(Rc<Literal>),
    Call {
        func: Rc<Expr>,
        args: Vec<Rc<Expr>>,
        kind: CallKind,
    },
    /// The logical operators are lazily evaluated, so the second
    /// parameter [rhs] must be in monadic form.
    LogicalOperator {
        name: String,
        lhs: Rc<Expr>,
        rhs: Rc<Expr>,
    },
    Lambda {
        args: Vec<(String, Option<Rc<CoqType>>)>,
        body: Rc<Expr>,
        is_internal: bool,
    },
    Array {
        elements: Vec<Rc<Expr>>,
        is_internal: bool,
    },
    Tuple {
        elements: Vec<Rc<Expr>>,
    },
    Let {
        is_monadic: bool,
        name: Option<String>,
        init: Rc<Expr>,
        body: Rc<Expr>,
    },
    If {
        condition: Rc<Expr>,
        success: Rc<Expr>,
        failure: Rc<Expr>,
    },
    Loop {
        body: Rc<Expr>,
    },
    Index {
        base: Rc<Expr>,
        index: Rc<Expr>,
    },
    ControlFlow(LoopControlFlow),
    StructStruct {
        path: Path,
        fields: Vec<(String, Rc<Expr>)>,
        base: Option<Rc<Expr>>,
        struct_or_variant: StructOrVariant,
    },
    StructTuple {
        path: Path,
        fields: Vec<Rc<Expr>>,
        struct_or_variant: StructOrVariant,
    },
    StructUnit {
        path: Path,
        #[allow(dead_code)]
        struct_or_variant: StructOrVariant,
    },
    Use(Rc<Expr>),
    InternalString(String),
    InternalInteger(usize),
    Return(Rc<Expr>),
    /// Useful for error messages or annotations
    Message(String),
}

impl Expr {
    pub(crate) fn tt() -> Rc<Self> {
        Rc::new(Expr::Tuple { elements: vec![] }).alloc()
    }

    pub(crate) fn local_var(name: &str) -> Rc<Expr> {
        Rc::new(Expr::LocalVar(name.to_string()))
    }

    pub(crate) fn match_simple_call(self: &Rc<Self>, name_in: &[&str]) -> Option<Rc<Expr>> {
        if let Expr::Call {
            func,
            args,
            kind: _,
        } = self.as_ref()
        {
            if let Expr::LocalVar(func) = func.as_ref() {
                if name_in.contains(&func.as_str()) && args.len() == 1 {
                    return Some(args.first().unwrap().clone());
                }
            }
        }

        None
    }

    pub(crate) fn alloc(self: Rc<Self>) -> Rc<Self> {
        Rc::new(Expr::Call {
            func: Expr::local_var("M.alloc"),
            args: vec![self],
            kind: CallKind::Effectful,
        })
    }

    pub(crate) fn read(self: &Rc<Self>) -> Rc<Self> {
        // If we read an allocated expression, we just return the expression.
        if let Some(expr) = self.clone().match_simple_call(&["M.alloc"]) {
            return expr.clone();
        }

        Rc::new(Expr::Call {
            func: Expr::local_var("M.read"),
            args: vec![self.clone()],
            kind: CallKind::Effectful,
        })
    }

    pub(crate) fn copy(self: Rc<Self>) -> Rc<Self> {
        if self.match_simple_call(&["M.alloc"]).is_some() {
            return self;
        }

        Rc::new(Expr::Call {
            func: Expr::local_var("M.copy"),
            args: vec![self],
            kind: CallKind::Effectful,
        })
    }

    /// If the body of the function is the macro call `unimplemented!()`. We do
    /// a special treatment for this case, by translating the function directly
    /// to an axiom. That is useful for mocks, where we want to state them equal
    /// to something defined in Coq at proof time. This is not wrong in the
    /// translation as we are only losing information here, not stating
    /// something wrong.
    pub(crate) fn is_unimplemented(self: &Rc<Self>) -> bool {
        *self.as_ref()
            == Expr::Call {
                func: Expr::local_var("M.never_to_any"),
                kind: CallKind::Effectful,
                args: vec![Rc::new(Expr::Call {
                    func: Rc::new(Expr::GetFunction {
                        func: Path::new(&["core", "panicking", "panic"]),
                        generic_tys: vec![],
                    }),
                    kind: CallKind::Closure,
                    args: vec![Rc::new(Expr::Call {
                        func: Expr::local_var("M.read"),
                        kind: CallKind::Effectful,
                        args: vec![Rc::new(Expr::Literal(Rc::new(Literal::String(
                            "not implemented".to_string(),
                        ))))],
                    })],
                })],
            }
    }
}

fn pure(e: Rc<Expr>) -> Rc<Expr> {
    Rc::new(Expr::Pure(e))
}

/// creates a monadic let statement with [e1] as the initializer
/// and the result of [f] as the body
fn monadic_let_in_stmt(
    fresh_vars: FreshVars,
    e1: Rc<Expr>,
    f: impl FnOnce(FreshVars, Rc<Expr>) -> (Rc<Expr>, FreshVars),
) -> (Rc<Expr>, FreshVars) {
    match e1.as_ref() {
        Expr::Pure(e) => f(fresh_vars, e.clone()),
        Expr::Let {
            is_monadic,
            name,
            init,
            body,
        } => {
            let (body, fresh_vars) = monadic_let_in_stmt(fresh_vars, body.clone(), f);
            (
                Rc::new(Expr::Let {
                    is_monadic: *is_monadic,
                    name: name.clone(),
                    init: init.clone(),
                    body,
                }),
                fresh_vars,
            )
        }
        _ => {
            let (var_name, fresh_vars) = fresh_vars.next();
            let (body, fresh_vars) = f(fresh_vars, Expr::local_var(&var_name));
            (
                Rc::new(Expr::Let {
                    is_monadic: true,
                    name: Some(var_name),
                    init: e1,
                    body,
                }),
                fresh_vars,
            )
        }
    }
}

fn monadic_let(
    fresh_vars: FreshVars,
    e1: Rc<Expr>,
    f: impl FnOnce(FreshVars, Rc<Expr>) -> (Rc<Expr>, FreshVars),
) -> (Rc<Expr>, FreshVars) {
    let (e1, fresh_vars) = mt_expression(fresh_vars, e1);
    monadic_let_in_stmt(fresh_vars, e1, f)
}

fn monadic_optional_let(
    fresh_vars: FreshVars,
    e1: Option<Rc<Expr>>,
    f: impl FnOnce(FreshVars, Option<Rc<Expr>>) -> (Rc<Expr>, FreshVars),
) -> (Rc<Expr>, FreshVars) {
    match e1 {
        None => f(fresh_vars, None),
        Some(e1) => monadic_let(fresh_vars, e1, |fresh_vars, e1| f(fresh_vars, Some(e1))),
    }
}

type DynLetFn<'a> = Box<dyn FnOnce(FreshVars, Vec<Rc<Expr>>) -> (Rc<Expr>, FreshVars) + 'a>;

fn monadic_lets(fresh_vars: FreshVars, es: Vec<Rc<Expr>>, f: DynLetFn) -> (Rc<Expr>, FreshVars) {
    match &es[..] {
        [] => f(fresh_vars, vec![]),
        [e1, es @ ..] => monadic_let(fresh_vars, e1.clone(), |fresh_vars, e1| {
            monadic_lets(
                fresh_vars,
                es.to_vec(),
                Box::new(|fresh_vars, es| f(fresh_vars, [vec![e1], es].concat())),
            )
        }),
    }
}

/// Monadic translation of an expression
///
/// The convention is to do transformation in a deep first fashion, so
/// all functions dealing with monadic translation expect that their
/// arguments already have been transformed. Not respecting this rule
/// may lead to infinite loops because of the mutual recursion between
/// the functions. In practice this means translating every sub-expression
/// before translating the expression itself.
pub(crate) fn mt_expression(fresh_vars: FreshVars, expr: Rc<Expr>) -> (Rc<Expr>, FreshVars) {
    match expr.as_ref() {
        Expr::Pure(_) => panic!("Expressions should not be monadic yet."),
        Expr::LocalVar(_) => (pure(expr), fresh_vars),
        Expr::GetConst(_) => (expr, fresh_vars),
        Expr::GetFunction { .. } => (expr, fresh_vars),
        Expr::Constructor(_) => (pure(expr), fresh_vars),
        Expr::TraitMethod {
            trait_name,
            method_name,
            self_and_generic_tys,
        } => (
            Rc::new(Expr::TraitMethod {
                trait_name: trait_name.clone(),
                method_name: method_name.clone(),
                self_and_generic_tys: self_and_generic_tys.clone(),
            }),
            fresh_vars,
        ),
        Expr::AssociatedFunction { .. } => (expr, fresh_vars),
        Expr::Literal { .. } => (pure(expr), fresh_vars),
        Expr::Call { func, args, kind } => {
            let kind = *kind;

            monadic_let(fresh_vars, func.clone(), |fresh_vars, func| {
                monadic_lets(
                    fresh_vars,
                    args.clone(),
                    Box::new(move |fresh_vars, args| {
                        (
                            {
                                let call = Rc::new(Expr::Call {
                                    func: func.clone(),
                                    args,
                                    kind,
                                });

                                match kind {
                                    CallKind::Pure => pure(call),
                                    CallKind::Effectful | CallKind::Closure => call,
                                }
                            },
                            fresh_vars,
                        )
                    }),
                )
            })
        }
        Expr::LogicalOperator { name, lhs, rhs } => {
            // We are discarding the [fresh_vars] here as it should not create
            // collisions, and it helps to keep the counters for the generated
            // names low.
            let (rhs, _) = mt_expression(fresh_vars.clone(), rhs.clone());

            monadic_let(fresh_vars, lhs.clone(), |fresh_vars, lhs| {
                (
                    Rc::new(Expr::LogicalOperator {
                        name: name.clone(),
                        lhs,
                        rhs,
                    }),
                    fresh_vars,
                )
            })
        }
        Expr::Lambda {
            args,
            body,
            is_internal,
        } => {
            let (body, _) = mt_expression(FreshVars::new(), body.clone());
            (
                pure(Rc::new(Expr::Lambda {
                    args: args.clone(),
                    body,
                    is_internal: *is_internal,
                })),
                fresh_vars,
            )
        }
        Expr::Array {
            elements,
            is_internal,
        } => monadic_lets(
            fresh_vars,
            elements.clone(),
            Box::new(|fresh_vars, elements| {
                (
                    pure(Rc::new(Expr::Array {
                        elements,
                        is_internal: *is_internal,
                    })),
                    fresh_vars,
                )
            }),
        ),
        Expr::Tuple { elements } => monadic_lets(
            fresh_vars,
            elements.clone(),
            Box::new(|fresh_vars, elements| (pure(Rc::new(Expr::Tuple { elements })), fresh_vars)),
        ),
        Expr::Let {
            is_monadic,
            name,
            init,
            body,
        } => {
            if *is_monadic {
                panic!("The let statement should not be monadic yet.")
            }
            let (init, _fresh_vars) = mt_expression(FreshVars::new(), init.clone());
            let (body, _fresh_vars) = mt_expression(FreshVars::new(), body.clone());
            let pure_init: Option<Rc<Expr>> = get_pure_from_stmt(init.clone());
            (
                match pure_init {
                    Some(pure_init) => Rc::new(Expr::Let {
                        is_monadic: false,
                        name: name.clone(),
                        init: pure_init,
                        body,
                    }),
                    None => Rc::new(Expr::Let {
                        is_monadic: true,
                        name: name.clone(),
                        init,
                        body,
                    }),
                },
                fresh_vars,
            )
        }
        Expr::If {
            condition,
            success,
            failure,
        } => monadic_let(fresh_vars, condition.clone(), |fresh_vars, condition| {
            let (success, _fresh_vars) = mt_expression(FreshVars::new(), success.clone());
            let (failure, _fresh_vars) = mt_expression(FreshVars::new(), failure.clone());
            (
                Rc::new(Expr::If {
                    condition,
                    success,
                    failure,
                }),
                fresh_vars,
            )
        }),
        Expr::Loop { body, .. } => {
            let (body, fresh_vars) = mt_expression(fresh_vars, body.clone());
            (Rc::new(Expr::Loop { body }), fresh_vars)
        }
        Expr::Index { base, index } => monadic_let(fresh_vars, base.clone(), |fresh_vars, base| {
            (
                pure(Rc::new(Expr::Index {
                    base,
                    index: index.clone(),
                })),
                fresh_vars,
            )
        }),
        // control flow expressions are responsible for side effects, so they are monadic already
        Expr::ControlFlow(lcf_expression) => {
            (Rc::new(Expr::ControlFlow(*lcf_expression)), fresh_vars)
        }
        Expr::StructStruct {
            path,
            fields,
            base,
            struct_or_variant,
        } => {
            let path = path.clone();
            let fields = fields.clone();
            let base = base.clone();
            let struct_or_variant = *struct_or_variant;
            let fields_values: Vec<Rc<Expr>> =
                fields.iter().map(|(_, field)| field.clone()).collect();

            monadic_lets(
                fresh_vars,
                fields_values,
                Box::new(move |fresh_vars, fields_values| {
                    monadic_optional_let(fresh_vars, base, |fresh_vars, base| {
                        let fields_names: Vec<String> =
                            fields.iter().map(|(name, _)| name.clone()).collect();
                        (
                            pure(Rc::new(Expr::StructStruct {
                                path,
                                fields: fields_names
                                    .iter()
                                    .zip(fields_values.iter())
                                    .map(|(name, value)| (name.clone(), value.clone()))
                                    .collect(),
                                base,
                                struct_or_variant,
                            })),
                            fresh_vars,
                        )
                    })
                }),
            )
        }
        Expr::StructTuple {
            path,
            fields,
            struct_or_variant,
        } => {
            let path = path.clone();
            let struct_or_variant = *struct_or_variant;

            monadic_lets(
                fresh_vars,
                fields.clone(),
                Box::new(move |fresh_vars, fields| {
                    (
                        pure(Rc::new(Expr::StructTuple {
                            path,
                            fields,
                            struct_or_variant,
                        })),
                        fresh_vars,
                    )
                }),
            )
        }
        Expr::StructUnit { .. } => (pure(expr), fresh_vars),
        Expr::Use(expr) => monadic_let(fresh_vars, expr.clone(), |fresh_vars, expr| {
            (pure(Rc::new(Expr::Use(expr))), fresh_vars)
        }),
        Expr::InternalString(_) => (pure(expr), fresh_vars),
        Expr::InternalInteger(_) => (pure(expr), fresh_vars),
        Expr::Return(expr) => monadic_let(fresh_vars, expr.clone(), |fresh_vars, expr| {
            (Rc::new(Expr::Return(expr)), fresh_vars)
        }),
        Expr::Message(_) => (pure(expr), fresh_vars),
    }
}

/// Get the pure part of a statement, if possible, as a statement.
fn get_pure_from_stmt(statement: Rc<Expr>) -> Option<Rc<Expr>> {
    match statement.as_ref() {
        Expr::Pure(e) => Some(e.clone()),
        Expr::Let {
            is_monadic: true, ..
        } => None,
        Expr::Let {
            is_monadic: false,
            name,
            init,
            body,
        } => get_pure_from_stmt(body.clone()).map(|body| {
            Rc::new(Expr::Let {
                is_monadic: false,
                name: name.clone(),
                init: init.clone(),
                body,
            })
        }),
        _ => None,
    }
}

pub(crate) fn apply_on_thir<'a, F, A>(
    env: &Env<'a>,
    local_def_id: impl IntoQueryParam<rustc_span::def_id::LocalDefId>,
    f: F,
) -> Result<A, String>
where
    F: FnOnce(&rustc_middle::thir::Thir<'a>, &rustc_middle::thir::ExprId) -> A,
{
    let thir = env.tcx.thir_body(local_def_id);
    let Ok((thir, expr_id)) = thir else {
        return Result::Err("thir failed to compile".to_string());
    };
    let result = std::panic::catch_unwind(panic::AssertUnwindSafe(|| thir.borrow()));

    match result {
        Ok(thir) => Result::Ok(f(&thir, &expr_id)),
        Err(error) => Result::Err(format!("thir failed to compile: {:?}", error)),
    }
}

pub(crate) fn compile_hir_id(env: &Env, hir_id: rustc_hir::hir_id::HirId) -> Rc<Expr> {
    let local_def_id = hir_id.owner.def_id;
    let result = apply_on_thir(env, local_def_id, |thir, expr_id| {
        crate::thir_expression::compile_expr(env, thir, expr_id)
    });

    match result {
        Ok(expr) => expr,
        Err(error) => Rc::new(Expr::Message(error)),
    }
}

impl LoopControlFlow {
    pub fn to_doc<'a>(self) -> Doc<'a> {
        match self {
            LoopControlFlow::Break => text("M.break"),
            LoopControlFlow::Continue => text("M.continue"),
        }
    }
}

impl Literal {
    pub(crate) fn to_doc(&self, with_paren: bool) -> Doc {
        match self {
            Literal::Bool(b) => paren(
                with_paren,
                nest([text("Value.Bool"), line(), text(format!("{b}"))]),
            ),
            Literal::Integer(LiteralInteger {
                name,
                negative_sign,
                value,
            }) => paren(
                with_paren,
                nest([
                    text("Value.Integer"),
                    line(),
                    text(format!("Integer.{name}")),
                    line(),
                    if *negative_sign {
                        text(format!("(-{value})"))
                    } else {
                        text(value.to_string())
                    },
                ]),
            ),
            Literal::Char(c) => paren(
                with_paren,
                nest([
                    text("Value.UnicodeChar"),
                    line(),
                    text((*c as u32).to_string()),
                ]),
            ),
            Literal::String(s) => string_to_doc(with_paren, s.as_str()),
            Literal::Error => text("UnsupportedLiteral"),
        }
    }
}

impl Expr {
    pub(crate) fn to_doc(&self, with_paren: bool) -> Doc {
        match self {
            Expr::Pure(expr) => paren(
                with_paren,
                nest([text("M.pure"), line(), expr.to_doc(true)]),
            ),
            Expr::LocalVar(ref name) => text(name),
            Expr::GetConst(path) => paren(
                with_paren,
                nest([text("M.get_constant"), line(), text(format!("\"{path}\""))]),
            ),
            Expr::GetFunction { func, generic_tys } => paren(
                with_paren,
                nest([
                    text("M.get_function"),
                    line(),
                    text(format!("\"{func}\"")),
                    line(),
                    list(
                        generic_tys
                            .iter()
                            .map(|generic_ty| generic_ty.to_coq().to_doc(false))
                            .collect(),
                    ),
                ]),
            ),
            Expr::Constructor(path) => path.to_doc(),
            Expr::TraitMethod {
                trait_name,
                method_name,
                self_and_generic_tys,
            } => paren(
                with_paren,
                nest([
                    text("M.get_trait_method"),
                    line(),
                    text(format!("\"{trait_name}\"")),
                    line(),
                    text(format!("\"{method_name}\"")),
                    line(),
                    list(
                        self_and_generic_tys
                            .iter()
                            .map(|(name, ty)| {
                                nest([
                                    text(format!("(* {name} *)")),
                                    line(),
                                    ty.to_coq().to_doc(false),
                                ])
                            })
                            .collect(),
                    ),
                ]),
            ),
            Expr::AssociatedFunction { ty, func } => paren(
                with_paren,
                nest([
                    text("M.get_associated_function"),
                    line(),
                    ty.to_coq().to_doc(true),
                    line(),
                    text(format!("\"{func}\"")),
                ]),
            ),
            Expr::Literal(literal) => literal.to_doc(with_paren),
            Expr::Call { func, args, kind } => paren(
                with_paren,
                match kind {
                    CallKind::Pure | CallKind::Effectful => nest([
                        func.to_doc(true),
                        concat(args.iter().map(|arg| concat([line(), arg.to_doc(true)]))),
                    ]),
                    CallKind::Closure => nest([
                        text("M.call_closure"),
                        line(),
                        func.to_doc(true),
                        line(),
                        list(args.iter().map(|arg| arg.to_doc(false)).collect()),
                    ]),
                },
            ),
            Expr::LogicalOperator { name, lhs, rhs } => paren(
                with_paren,
                nest([
                    text(name),
                    line(),
                    lhs.to_doc(true),
                    line(),
                    rhs.to_doc(true),
                ]),
            ),
            Expr::Lambda {
                args,
                body,
                is_internal,
            } => {
                if *is_internal {
                    return paren(
                        with_paren,
                        nest([
                            nest([
                                text("fun"),
                                concat(args.iter().map(|(name, _)| concat([line(), text(name)]))),
                                text(" =>"),
                            ]),
                            line(),
                            body.to_doc(false),
                        ]),
                    );
                }

                coq::Expression::just_name("M.closure")
                    .apply(&coq::Expression::Function {
                        parameters: vec![coq::Expression::just_name("γ")],
                        body: Rc::new(coq::Expression::Match {
                            scrutinees: vec![coq::Expression::just_name("γ")],
                            arms: vec![
                                (
                                    vec![coq::Expression::List {
                                        exprs: args
                                            .iter()
                                            .map(|(name, _)| coq::Expression::just_name(name))
                                            .collect(),
                                    }],
                                    coq::Expression::Code(body.to_doc(false)),
                                ),
                                (
                                    vec![coq::Expression::Wild],
                                    coq::Expression::just_name("M.impossible"),
                                ),
                            ],
                        }),
                    })
                    .to_doc(with_paren)
            }
            Expr::Array {
                elements,
                is_internal,
            } => {
                let elements_doc = list(
                    elements
                        .iter()
                        .map(|element| element.to_doc(false))
                        .collect(),
                );

                if *is_internal {
                    return elements_doc;
                }

                paren(
                    with_paren,
                    nest([text("Value.Array"), line(), elements_doc]),
                )
            }
            Expr::Tuple { elements } => paren(
                with_paren,
                nest([
                    text("Value.Tuple"),
                    line(),
                    list(
                        elements
                            .iter()
                            .map(|element| element.to_doc(false))
                            .collect(),
                    ),
                ]),
            ),
            Expr::Let {
                is_monadic,
                name,
                init,
                body,
            } => paren(
                with_paren,
                group([
                    nest([
                        nest([
                            nest([
                                text("let"),
                                optional_insert(!*is_monadic, text("*")),
                                line(),
                                text(match name {
                                    Some(name) => name,
                                    None => "_",
                                }),
                            ]),
                            text(" :="),
                        ]),
                        line(),
                        init.to_doc(false),
                        text(" in"),
                    ]),
                    hardline(),
                    body.to_doc(false),
                ]),
            ),
            Expr::If {
                condition,
                success,
                failure,
            } => paren(
                with_paren,
                group([
                    group([
                        nest([
                            text("if"),
                            line(),
                            nest([text("Value.is_true"), line(), condition.to_doc(true)]),
                        ]),
                        line(),
                        text("then"),
                    ]),
                    nest([hardline(), success.to_doc(false)]),
                    hardline(),
                    nest([text("else"), hardline(), failure.to_doc(false)]),
                ]),
            ),
            Expr::Loop { body } => paren(
                with_paren,
                nest([text("M.loop"), line(), paren(true, body.to_doc(with_paren))]),
            ),
            Expr::Index { base, index } => {
                nest([base.to_doc(true), text("["), index.to_doc(false), text("]")])
            }
            Expr::ControlFlow(lcf_expression) => lcf_expression.to_doc(),
            Expr::StructStruct {
                path,
                fields,
                base,
                struct_or_variant: _,
            } => match base {
                None => paren(
                    with_paren,
                    nest([
                        text("Value.StructRecord"),
                        line(),
                        text(format!("\"{path}\"")),
                        line(),
                        list(
                            fields
                                .iter()
                                .map(|(name, expr)| {
                                    nest([
                                        text("("),
                                        text(format!("\"{name}\"")),
                                        text(","),
                                        line(),
                                        expr.to_doc(false),
                                        text(")"),
                                    ])
                                })
                                .collect(),
                        ),
                    ]),
                ),
                Some(base) => coq::Expression::just_name("M.struct_record_update")
                    .apply_many(&[
                        coq::Expression::Code(base.to_doc(true)),
                        coq::Expression::List {
                            exprs: fields
                                .iter()
                                .map(|(name, expr)| {
                                    coq::Expression::Tuple(vec![
                                        coq::Expression::String(name.to_string()),
                                        coq::Expression::Code(expr.to_doc(false)),
                                    ])
                                })
                                .collect(),
                        },
                    ])
                    .to_doc(with_paren),
            },
            Expr::StructTuple {
                path,
                fields,
                struct_or_variant: _,
            } => coq::Expression::just_name("Value.StructTuple")
                .apply_many(&[
                    coq::Expression::String(path.to_string()),
                    coq::Expression::List {
                        exprs: fields
                            .iter()
                            .map(|expr| coq::Expression::Code(expr.to_doc(false)))
                            .collect(),
                    },
                ])
                .to_doc(with_paren),
            Expr::StructUnit {
                path,
                struct_or_variant: _,
            } => coq::Expression::just_name("Value.StructTuple")
                .apply_many(&[
                    coq::Expression::String(path.to_string()),
                    coq::Expression::List { exprs: vec![] },
                ])
                .to_doc(with_paren),
            Expr::Use(expr) => paren(with_paren, nest([text("M.use"), line(), expr.to_doc(true)])),
            Expr::InternalString(s) => text(format!("\"{s}\"")),
            Expr::InternalInteger(i) => text(i.to_string()),
            Expr::Return(value) => paren(
                with_paren,
                nest([text("M.return_"), line(), value.to_doc(true)]),
            ),
            Expr::Message(message) => text(format!("(* {message} *)")),
        }
    }
}
