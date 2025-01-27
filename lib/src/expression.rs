use crate::coq;
use crate::env::*;
use crate::path::*;
use crate::pattern::*;
use crate::ty::*;
use core::panic;
use itertools::Itertools;
use rustc_middle::query::plumbing::IntoQueryParam;
use serde::Serialize;
use std::rc::Rc;

/// Struct [MatchArm] represents a pattern-matching branch: [pat] is the
/// matched pattern and [body] the expression on which it is mapped
#[derive(Debug, Serialize)]
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
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
pub(crate) enum LoopControlFlow {
    Continue,
    Break,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
pub(crate) enum CallKind {
    /// Pure call of a function, written with a space following the syntax
    /// of Coq.
    Pure,
    /// Like [Pure] but with a result in the monad.
    Effectful,
    /// Call of a Rust closure, using the monadic operator `M.call`.
    Closure,
}

#[derive(Debug, Eq, PartialEq, Serialize)]
pub(crate) struct LiteralInteger {
    pub(crate) kind: String,
    pub(crate) negative_sign: bool,
    pub(crate) value: u128,
}

#[derive(Debug, Eq, PartialEq, Serialize)]
pub(crate) enum Literal {
    Bool(bool),
    Integer(LiteralInteger),
    Char(char),
    String(String),
    Error,
}

/// Enum [Expr] represents the AST of rust terms.
#[derive(Debug, Eq, PartialEq, Serialize)]
pub(crate) enum Expr {
    LocalVar(String),
    GetConst(Rc<Path>),
    GetFunction {
        func: Rc<Path>,
        generic_consts: Vec<Rc<Expr>>,
        generic_tys: Vec<Rc<CoqType>>,
    },
    GetTraitMethod {
        trait_name: Rc<Path>,
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
        is_for_match: bool,
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
        is_user: bool,
        init: Rc<Expr>,
        body: Rc<Expr>,
    },
    Match {
        scrutinee: Rc<Expr>,
        arms: Vec<Rc<Expr>>,
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
        path: Rc<Path>,
        fields: Vec<(String, Rc<Expr>)>,
        base: Option<Rc<Expr>>,
    },
    StructTuple {
        path: Rc<Path>,
        fields: Vec<Rc<Expr>>,
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
                        generic_consts: vec![],
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

    pub(crate) fn has_return(&self) -> bool {
        match self {
            Expr::LocalVar(_) => false,
            Expr::GetConst(_) => false,
            Expr::GetFunction { .. } => false,
            Expr::GetTraitMethod { .. } => false,
            Expr::GetAssociatedFunction { .. } => false,
            Expr::Literal(_) => false,
            Expr::Call {
                func,
                args,
                kind: _,
            } => func.has_return() || args.iter().any(|arg| arg.has_return()),
            Expr::LogicalOperator { name: _, lhs, rhs } => lhs.has_return() || rhs.has_return(),
            Expr::Lambda {
                args: _,
                body,
                is_for_match,
                is_internal: _,
            } => *is_for_match && body.has_return(),
            Expr::Array {
                elements,
                is_internal: _,
            } => elements.iter().any(|element| element.has_return()),
            Expr::Tuple { elements } => elements.iter().any(|element| element.has_return()),
            Expr::Let {
                is_user: _,
                name: _,
                init,
                body,
            } => init.has_return() || body.has_return(),
            Expr::Loop { body } => body.has_return(),
            Expr::Match { scrutinee, arms } => {
                scrutinee.has_return() || arms.iter().any(|arm| arm.has_return())
            }
            Expr::Index { base, index } => base.has_return() || index.has_return(),
            Expr::ControlFlow(_) => false,
            Expr::StructStruct {
                path: _,
                fields,
                base,
            } => {
                fields.iter().any(|(_, field)| field.has_return())
                    || base.iter().any(|base| base.has_return())
            }
            Expr::StructTuple { path: _, fields } => fields.iter().any(|field| field.has_return()),
            Expr::Use(expr) => expr.has_return(),
            Expr::InternalString(_) => false,
            Expr::InternalInteger(_) => false,
            Expr::Return(_) => true,
            Expr::Comment(_, expr) => expr.has_return(),
        }
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

fn string_pieces_to_coq(pieces: &[StringPiece]) -> coq::Expression {
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
    coq::Expression::just_name("Value.String").apply(&string_pieces_to_coq(&pieces))
}

impl LoopControlFlow {
    pub fn to_coq(self) -> coq::Expression {
        match self {
            LoopControlFlow::Break => coq::Expression::just_name("M.break").monadic_apply_empty(),
            LoopControlFlow::Continue => {
                coq::Expression::just_name("M.continue").monadic_apply_empty()
            }
        }
    }
}

impl Literal {
    pub(crate) fn to_coq(&self) -> coq::Expression {
        match self {
            Literal::Bool(b) => coq::Expression::just_name("Value.Bool")
                .apply(&coq::Expression::just_name(b.to_string().as_str())),
            Literal::Integer(LiteralInteger {
                kind,
                negative_sign,
                value,
            }) => coq::Expression::just_name("Value.Integer").apply_many(&[
                coq::Expression::just_name(format!("IntegerKind.{kind}").as_str()),
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

    fn to_name(&self) -> String {
        match self {
            Literal::Bool(b) => b.to_string(),
            Literal::Integer(LiteralInteger {
                kind,
                negative_sign,
                value,
            }) => {
                if *negative_sign {
                    format!("{kind}_minus_{value}")
                } else {
                    format!("{kind}_{value}")
                }
            }
            Literal::Char(c) => format!("char_{}", c),
            Literal::String(s) => format!("string_{}", s),
            Literal::Error => "error".to_string(),
        }
    }
}

impl Expr {
    pub(crate) fn to_coq(&self) -> coq::Expression {
        match self {
            Expr::LocalVar(ref name) => coq::Expression::just_name(name),
            Expr::GetConst(path) => coq::Expression::just_name("M.get_constant")
                .monadic_apply(&coq::Expression::String(path.to_string())),
            Expr::GetFunction {
                func,
                generic_consts,
                generic_tys,
            } => coq::Expression::just_name("M.get_function").monadic_apply_many(&[
                coq::Expression::String(func.to_string()),
                coq::Expression::List {
                    exprs: generic_consts
                        .iter()
                        .map(|generic_const| generic_const.to_coq())
                        .collect_vec(),
                },
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
            } => coq::Expression::just_name("M.get_trait_method").monadic_apply_many(&[
                coq::Expression::String(trait_name.to_string()),
                self_ty.to_coq(),
                coq::Expression::List {
                    exprs: trait_tys
                        .iter()
                        .map(|trait_ty| trait_ty.to_coq())
                        .collect_vec(),
                },
                coq::Expression::String(method_name.to_string()),
                coq::Expression::List {
                    exprs: generic_tys.iter().map(|ty| ty.to_coq()).collect_vec(),
                },
            ]),
            Expr::GetAssociatedFunction {
                ty,
                func,
                generic_tys,
            } => coq::Expression::just_name("M.get_associated_function").monadic_apply_many(&[
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
                CallKind::Pure => func
                    .to_coq()
                    .apply_many(&args.iter().map(|arg| arg.to_coq()).collect_vec()),
                CallKind::Effectful => func
                    .to_coq()
                    .monadic_apply_many(&args.iter().map(|arg| arg.to_coq()).collect_vec()),
                CallKind::Closure => coq::Expression::just_name("M.call_closure")
                    .monadic_apply_many(&[
                        func.to_coq(),
                        coq::Expression::List {
                            exprs: args.iter().map(|arg| arg.to_coq()).collect_vec(),
                        },
                    ]),
            },
            Expr::LogicalOperator { name, lhs, rhs } => coq::Expression::just_name(name.as_str())
                .monadic_apply_many(&[lhs.to_coq(), coq::Expression::monadic(&rhs.to_coq())]),
            Expr::Lambda {
                args,
                body,
                is_for_match: _,
                is_internal,
            } => {
                if *is_internal {
                    return coq::Expression::Function {
                        parameters: args
                            .iter()
                            .map(|(name, _)| coq::Expression::just_name(name))
                            .collect_vec(),
                        body: Rc::new(coq::Expression::monadic(&body.to_coq())),
                    };
                }

                coq::Expression::just_name("M.closure").apply(&coq::Expression::Function {
                    parameters: vec![coq::Expression::just_name("γ")],
                    body: Rc::new(coq::Expression::monadic(&coq::Expression::Match {
                        scrutinees: vec![coq::Expression::just_name("γ")],
                        arms: vec![
                            (
                                vec![coq::Expression::List {
                                    exprs: args
                                        .iter()
                                        .map(|(name, _)| coq::Expression::name_pattern(name))
                                        .collect(),
                                }],
                                coq::Expression::monadic(&body.to_coq()),
                            ),
                            (
                                vec![coq::Expression::Wild],
                                coq::Expression::just_name("M.impossible").apply(
                                    &coq::Expression::String(
                                        "wrong number of arguments".to_string(),
                                    ),
                                ),
                            ),
                        ],
                    })),
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
                is_user,
                init,
                body,
            } => coq::Expression::Let {
                name: name.to_owned(),
                is_user: *is_user,
                ty: None,
                init: Rc::new(init.to_coq()),
                body: Rc::new(body.to_coq()),
            },
            Expr::Match { scrutinee, arms } => coq::Expression::just_name("M.match_operator")
                .monadic_apply_many(&[
                    scrutinee.to_coq(),
                    coq::Expression::List {
                        exprs: arms.iter().map(|arm| arm.to_coq()).collect(),
                    },
                ]),
            Expr::Loop { body } => coq::Expression::just_name("M.loop")
                .monadic_apply(&Rc::new(coq::Expression::monadic(&body.to_coq()))),
            Expr::Index { base, index } => {
                coq::Expression::just_name("M.SubPointer.get_array_field")
                    .monadic_apply_many(&[base.to_coq(), index.to_coq()])
            }
            Expr::ControlFlow(lcf_expression) => lcf_expression.to_coq(),
            Expr::StructStruct { path, fields, base } => match base {
                None => coq::Expression::just_name("Value.StructRecord").apply_many(&[
                    coq::Expression::String(path.to_string()),
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
            Expr::Use(expr) => coq::Expression::just_name("M.use").apply(&expr.to_coq()),
            Expr::InternalString(s) => coq::Expression::String(s.to_string()),
            Expr::InternalInteger(i) => coq::Expression::just_name(i.to_string().as_str()),
            Expr::Return(value) => {
                coq::Expression::just_name("M.return_").monadic_apply(&value.to_coq())
            }
            Expr::Comment(message, expr) => {
                coq::Expression::Comment(message.to_owned(), expr.to_coq().into())
            }
        }
    }

    pub(crate) fn to_name(&self) -> String {
        match self {
            Expr::LocalVar(name) => name.clone(),
            Expr::Literal(literal) => literal.to_name(),
            _ => "expr".to_string(),
        }
    }
}
