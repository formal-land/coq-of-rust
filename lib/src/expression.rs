use crate::coq;
use crate::env::*;
use crate::path::*;
use crate::pattern::*;
use crate::render::*;
use crate::ty::*;
use core::panic;
use itertools::Itertools;
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
    /// We represent a boolean guard as an if-let guard with a pattern
    /// equals to the boolean [true]. Thus we do not need to distinguish
    /// between boolean guards and if-let guards in the translation. There can
    /// be a list of conditions, for guards having several conditions separated
    /// by the `&&` operator.
    pub(crate) if_let_guard: Vec<(Rc<Pattern>, Rc<Expr>)>,
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
    GetTraitMethod {
        trait_name: Path,
        self_ty: Rc<CoqType>,
        trait_tys: Vec<Rc<CoqType>>,
        method_name: String,
        generic_tys: Vec<Rc<CoqType>>,
    },
    GetAssociatedFunction {
        ty: Rc<CoqType>,
        func: String,
        generic_tys: Vec<Rc<CoqType>>,
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
        name: Option<String>,
        is_monadic: bool,
        init: Rc<Expr>,
        body: Rc<Expr>,
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
    },
    StructTuple {
        path: Path,
        fields: Vec<Rc<Expr>>,
    },
    StructUnit {
        path: Path,
    },
    Use(Rc<Expr>),
    InternalString(String),
    InternalInteger(usize),
    Return(Rc<Expr>),
    /// Useful for error messages or annotations
    Comment(String, Rc<Expr>),
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
            name,
            is_monadic,
            init,
            body,
        } => {
            let (body, fresh_vars) = monadic_let_in_stmt(fresh_vars, body.clone(), f);
            (
                Rc::new(Expr::Let {
                    name: name.clone(),
                    is_monadic: *is_monadic,
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
                    name: Some(var_name),
                    is_monadic: true,
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
        Expr::GetTraitMethod {
            trait_name,
            self_ty,
            trait_tys,
            method_name,
            generic_tys,
        } => (
            Rc::new(Expr::GetTraitMethod {
                trait_name: trait_name.clone(),
                self_ty: self_ty.clone(),
                trait_tys: trait_tys.clone(),
                method_name: method_name.clone(),
                generic_tys: generic_tys.clone(),
            }),
            fresh_vars,
        ),
        Expr::GetAssociatedFunction { .. } => (expr, fresh_vars),
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
            name,
            is_monadic,
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
                        name: name.clone(),
                        is_monadic: false,
                        init: pure_init,
                        body,
                    }),
                    None => Rc::new(Expr::Let {
                        name: name.clone(),
                        is_monadic: true,
                        init,
                        body,
                    }),
                },
                fresh_vars,
            )
        }
        Expr::Loop { body, .. } => {
            let (body, fresh_vars) = mt_expression(fresh_vars, body.clone());
            (Rc::new(Expr::Loop { body }), fresh_vars)
        }
        Expr::Index { base, index } => monadic_let(fresh_vars, base.clone(), |fresh_vars, base| {
            monadic_let(fresh_vars, index.clone(), |fresh_vars, index| {
                (Rc::new(Expr::Index { base, index }), fresh_vars)
            })
        }),
        // control flow expressions are responsible for side effects, so they are monadic already
        Expr::ControlFlow(lcf_expression) => {
            (Rc::new(Expr::ControlFlow(*lcf_expression)), fresh_vars)
        }
        Expr::StructStruct { path, fields, base } => {
            let path = path.clone();
            let fields = fields.clone();
            let base = base.clone();
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
                            })),
                            fresh_vars,
                        )
                    })
                }),
            )
        }
        Expr::StructTuple { path, fields } => {
            let path = path.clone();

            monadic_lets(
                fresh_vars,
                fields.clone(),
                Box::new(move |fresh_vars, fields| {
                    (
                        pure(Rc::new(Expr::StructTuple { path, fields })),
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
        Expr::Comment(comment, expr) => {
            let (expr, fresh_vars) = mt_expression(fresh_vars, expr.clone());

            (Rc::new(Expr::Comment(comment.clone(), expr)), fresh_vars)
        }
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
            name,
            is_monadic: false,
            init,
            body,
        } => get_pure_from_stmt(body.clone()).map(|body| {
            Rc::new(Expr::Let {
                name: name.clone(),
                is_monadic: false,
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
        let generics = env.tcx.generics_of(local_def_id);

        crate::thir_expression::compile_expr(env, generics, thir, expr_id)
    });

    match result {
        Ok(expr) => expr,
        Err(error) => Rc::new(Expr::Comment(error, Expr::tt())),
    }
}

#[derive(Debug)]
enum StringPiece {
    /// A string of ASCII characters
    AsciiString(String),
    /// A single non-ASCII character
    UnicodeChar(char),
}

/// As we can only represent purely ASCII strings in Coq, we need to cut the
/// string in pieces, alternating between ASCII strings and non-ASCII
/// characters.
fn cut_string_in_pieces_for_coq(input: &str) -> Vec<StringPiece> {
    let mut result: Vec<StringPiece> = Vec::new();
    let mut ascii_buf = String::new();

    for c in input.chars() {
        if c.is_ascii() {
            ascii_buf.push(c);
        } else {
            if !ascii_buf.is_empty() {
                result.push(StringPiece::AsciiString(ascii_buf.clone()));
                ascii_buf.clear();
            }
            result.push(StringPiece::UnicodeChar(c));
        }
    }

    if !ascii_buf.is_empty() {
        result.push(StringPiece::AsciiString(ascii_buf));
    }
    result
}

fn string_pieces_to_coq<'a>(pieces: &[StringPiece]) -> coq::Expression<'a> {
    match pieces {
        [] => coq::Expression::just_name("\"\""),
        [StringPiece::AsciiString(s), rest @ ..] => {
            let head = coq::Expression::String(str::replace(s, "\"", "\"\""));
            if rest.is_empty() {
                head
            } else {
                head.apply_many(&[coq::Expression::just_name("++"), string_pieces_to_coq(rest)])
            }
        }
        [StringPiece::UnicodeChar(c), rest @ ..] => coq::Expression::just_name("String.String")
            .apply_many(&[
                coq::Expression::String(format!("{:03}", *c as u8)),
                string_pieces_to_coq(rest),
            ]),
    }
}

fn string_to_coq(message: &str) -> coq::Expression {
    let pieces = cut_string_in_pieces_for_coq(message);
    coq::Expression::just_name("mk_str").apply(&string_pieces_to_coq(&pieces))
}

impl LoopControlFlow {
    pub fn to_coq<'a>(self) -> coq::Expression<'a> {
        match self {
            LoopControlFlow::Break => coq::Expression::just_name("M.break"),
            LoopControlFlow::Continue => coq::Expression::just_name("M.continue"),
        }
    }
}

impl Literal {
    pub(crate) fn to_coq(&self) -> coq::Expression {
        match self {
            Literal::Bool(b) => coq::Expression::just_name("Value.Bool")
                .apply(&coq::Expression::just_name(format!("{b}").as_str())),
            Literal::Integer(LiteralInteger {
                name,
                negative_sign,
                value,
            }) => coq::Expression::just_name("Value.Integer").apply_many(&[
                coq::Expression::just_name(format!("Integer.{name}").as_str()),
                if *negative_sign {
                    coq::Expression::just_name(format!("(-{value})").as_str())
                } else {
                    coq::Expression::just_name(value.to_string().as_str())
                },
            ]),
            Literal::Char(c) => coq::Expression::just_name("Value.UnicodeChar").apply(
                &coq::Expression::just_name((*c as u32).to_string().as_str()),
            ),
            Literal::String(s) => string_to_coq(s.as_str()),
            Literal::Error => coq::Expression::just_name("UnsupportedLiteral"),
        }
    }
}

impl Expr {
    pub(crate) fn to_coq(&self) -> coq::Expression {
        match self {
            Expr::Pure(expr) => coq::Expression::just_name("M.pure").apply(&expr.to_coq()),
            Expr::LocalVar(ref name) => coq::Expression::just_name(name),
            Expr::GetConst(path) => coq::Expression::just_name("M.get_constant")
                .apply(&coq::Expression::String(format!("{path}"))),
            Expr::GetFunction { func, generic_tys } => coq::Expression::just_name("M.get_function")
                .apply_many(&[
                    coq::Expression::String(format!("{func}")),
                    coq::Expression::List {
                        exprs: generic_tys
                            .iter()
                            .map(|generic_ty| generic_ty.to_coq())
                            .collect_vec(),
                    },
                ]),
            Expr::GetTraitMethod {
                trait_name,
                self_ty,
                trait_tys,
                method_name,
                generic_tys,
            } => coq::Expression::just_name("M.get_trait_method").apply_many(&[
                coq::Expression::String(format!("{trait_name}")),
                self_ty.to_coq(),
                coq::Expression::List {
                    exprs: trait_tys
                        .iter()
                        .map(|trait_ty| trait_ty.to_coq())
                        .collect_vec(),
                },
                coq::Expression::String(format!("{method_name}")),
                coq::Expression::List {
                    exprs: generic_tys.iter().map(|ty| ty.to_coq()).collect_vec(),
                },
            ]),
            Expr::GetAssociatedFunction {
                ty,
                func,
                generic_tys,
            } => coq::Expression::just_name("M.get_associated_function").apply_many(&[
                ty.to_coq(),
                coq::Expression::String(func.to_string()),
                coq::Expression::List {
                    exprs: generic_tys
                        .iter()
                        .map(|generic_ty| generic_ty.to_coq())
                        .collect(),
                },
            ]),
            Expr::Literal(literal) => literal.to_coq(),
            Expr::Call { func, args, kind } => match kind {
                CallKind::Pure | CallKind::Effectful => func
                    .to_coq()
                    .apply_many(&args.iter().map(|arg| arg.to_coq()).collect_vec()),
                CallKind::Closure => coq::Expression::just_name("M.call_closure").apply_many(&[
                    func.to_coq(),
                    coq::Expression::List {
                        exprs: args.iter().map(|arg| arg.to_coq()).collect_vec(),
                    },
                ]),
            },
            Expr::LogicalOperator { name, lhs, rhs } => {
                coq::Expression::just_name(name.as_str()).apply_many(&[lhs.to_coq(), rhs.to_coq()])
            }
            Expr::Lambda {
                args,
                body,
                is_internal,
            } => {
                if *is_internal {
                    return coq::Expression::Function {
                        parameters: args
                            .iter()
                            .map(|(name, _)| coq::Expression::just_name(name))
                            .collect_vec(),
                        body: body.to_coq().into(),
                    };
                };

                coq::Expression::just_name("M.closure").apply(&coq::Expression::Function {
                    parameters: vec![coq::Expression::just_name("γ")],
                    body: Rc::new(coq::Expression::Match {
                        scrutinees: vec![coq::Expression::just_name("γ")],
                        arms: vec![
                            (
                                vec![coq::Expression::List {
                                    exprs: args
                                        .iter()
                                        .map(|(name, _)| coq::Expression::name_pattern(name))
                                        .collect(),
                                }],
                                body.to_coq(),
                            ),
                            (
                                vec![coq::Expression::Wild],
                                coq::Expression::just_name("M.impossible"),
                            ),
                        ],
                    }),
                })
            }
            Expr::Array {
                elements,
                is_internal,
            } => {
                let elements_expression = coq::Expression::List {
                    exprs: elements
                        .iter()
                        .map(|element| element.to_coq())
                        .collect_vec(),
                };

                if *is_internal {
                    return elements_expression;
                }

                coq::Expression::just_name("Value.Array").apply(&elements_expression)
            }
            Expr::Tuple { elements } => {
                coq::Expression::just_name("Value.Tuple").apply(&coq::Expression::List {
                    exprs: elements
                        .iter()
                        .map(|element| element.to_coq())
                        .collect_vec(),
                })
            }
            Expr::Let {
                name,
                is_monadic,
                init,
                body,
            } => coq::Expression::Let {
                name: name.to_owned(),
                is_monadic: *is_monadic,
                ty: None,
                init: Rc::new(init.to_coq()),
                body: Rc::new(body.to_coq()),
            },
            Expr::Loop { body } => coq::Expression::just_name("M.loop").apply(&body.to_coq()),
            Expr::Index { base, index } => coq::Expression::just_name("M.get_array_field")
                .apply_many(&[base.to_coq(), index.to_coq()]),
            Expr::ControlFlow(lcf_expression) => lcf_expression.to_coq(),
            Expr::StructStruct { path, fields, base } => match base {
                None => coq::Expression::just_name("Value.StructRecord").apply_many(&[
                    coq::Expression::String(format!("{path}")),
                    coq::Expression::List {
                        exprs: fields
                            .iter()
                            .map(|(name, expr)| {
                                coq::Expression::Tuple(vec![
                                    coq::Expression::String(name.to_owned()),
                                    expr.to_coq(),
                                ])
                            })
                            .collect_vec(),
                    },
                ]),
                Some(base) => coq::Expression::just_name("M.struct_record_update").apply_many(&[
                    base.to_coq(),
                    coq::Expression::List {
                        exprs: fields
                            .iter()
                            .map(|(name, expr)| {
                                coq::Expression::Tuple(vec![
                                    coq::Expression::String(name.to_string()),
                                    expr.to_coq(),
                                ])
                            })
                            .collect(),
                    },
                ]),
            },
            Expr::StructTuple { path, fields } => coq::Expression::just_name("Value.StructTuple")
                .apply_many(&[
                    coq::Expression::String(path.to_string()),
                    coq::Expression::List {
                        exprs: fields.iter().map(|expr| expr.to_coq()).collect(),
                    },
                ]),
            Expr::StructUnit { path } => coq::Expression::just_name("Value.StructTuple")
                .apply_many(&[
                    coq::Expression::String(path.to_string()),
                    coq::Expression::List { exprs: vec![] },
                ]),
            Expr::Use(expr) => coq::Expression::just_name("M.use").apply(&expr.to_coq()), // gy@TODO: eliminate the `with_paren`
            Expr::InternalString(s) => coq::Expression::String(format!("{s}")),
            Expr::InternalInteger(i) => coq::Expression::just_name(i.to_string().as_str()),
            Expr::Return(value) => coq::Expression::just_name("M.return_").apply(&value.to_coq()),
            Expr::Comment(message, expr) => {
                coq::Expression::Comment(message.to_owned(), expr.to_coq().into())
            }
        }
    }

    pub(crate) fn to_doc(&self, with_paren: bool) -> Doc {
        self.to_coq().to_doc(with_paren)
    }
}
