use pretty::RcDoc;
use rustc_ast::LitKind;
use rustc_span::symbol::Symbol;

use crate::coq;

/// provides the instance of the Struct.Trait typeclass
/// for definitions of functions and constants
/// which types utilize the M monad constructor
pub(crate) fn monadic_typeclass_parameter<'a>() -> Doc<'a> {
    // TODO: check whether the name of the parameter is necessary
    text("`{H : State.Trait}")
}

/// encloses an expression in curly brackets
pub(crate) fn curly_brackets(doc: RcDoc<()>) -> RcDoc<()> {
    RcDoc::concat([RcDoc::text("{"), doc, RcDoc::text("}")])
}

/// encloses an expression in regular brackets
pub(crate) fn round_brackets(doc: RcDoc<()>) -> RcDoc<()> {
    RcDoc::concat([RcDoc::text("("), doc, RcDoc::text(")")])
}

pub(crate) fn paren(with_paren: bool, doc: RcDoc<()>) -> RcDoc<()> {
    if with_paren {
        round_brackets(doc)
    } else {
        doc
    }
}

fn round_symbol(symbol: &Symbol) -> i32 {
    let s = symbol.as_str();
    s.parse::<f64>().unwrap().round() as i32
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

fn string_pieces_to_doc<'a>(with_paren: bool, pieces: &[StringPiece]) -> RcDoc<'a, ()> {
    match pieces {
        [] => text("\"\""),
        [StringPiece::AsciiString(s), rest @ ..] => paren(
            with_paren && !rest.is_empty(),
            nest([
                text("\""),
                text(s.clone()),
                text("\""),
                if rest.is_empty() {
                    nil()
                } else {
                    concat([text(" ++"), line(), string_pieces_to_doc(false, rest)])
                },
            ]),
        ),
        [StringPiece::UnicodeChar(c), rest @ ..] => paren(
            with_paren,
            nest([
                text("String.String"),
                line(),
                text("\""),
                text(format!("{}", *c as u8)),
                text("\""),
                line(),
                string_pieces_to_doc(true, rest),
            ]),
        ),
    }
}

fn string_to_doc(with_paren: bool, text: &str) -> RcDoc<()> {
    let pieces = cut_string_in_pieces_for_coq(text);
    string_pieces_to_doc(with_paren, &pieces)
}

pub(crate) fn literal_to_doc(with_paren: bool, literal: &LitKind) -> RcDoc<()> {
    match literal {
        LitKind::Str(s, _) => string_to_doc(with_paren, s.as_str()),
        LitKind::Int(i, _) => RcDoc::text(format!("{i}")),
        LitKind::Float(f, _) => RcDoc::text(format!("{} (* {f} *)", round_symbol(f))),
        LitKind::Bool(b) => RcDoc::text(format!("{b}")),
        LitKind::Char(c) => RcDoc::text(format!("\"{c}\"%char")),
        LitKind::Byte(b) => RcDoc::text(format!("{b}")),
        LitKind::ByteStr(b, _) => RcDoc::text(format!("{b:?}")),
        LitKind::Err => RcDoc::text("Err"),
    }
}

pub type Doc<'a> = RcDoc<'a, ()>;

// Concat several documents and indent when splitting the line
pub(crate) fn nest<'a, I>(docs: I) -> Doc<'a>
where
    I: IntoIterator,
    I::Item: pretty::Pretty<'a, pretty::RcAllocator, ()>,
{
    let indent_space_offset = 2;
    RcDoc::concat(docs).nest(indent_space_offset).group()
}

// Concat several documents and do *not* indent when splitting the line
pub(crate) fn group<'a, I>(docs: I) -> Doc<'a>
where
    I: IntoIterator,
    I::Item: pretty::Pretty<'a, pretty::RcAllocator, ()>,
{
    RcDoc::concat(docs).group()
}

// Concat several documents and do nothing for the splitting (using nest or
// group is more frequent)
pub(crate) fn concat<'a, I>(docs: I) -> Doc<'a>
where
    I: IntoIterator,
    I::Item: pretty::Pretty<'a, pretty::RcAllocator, ()>,
{
    RcDoc::concat(docs)
}

pub(crate) fn text<'a, U>(message: U) -> Doc<'a>
where
    U: Into<std::borrow::Cow<'a, str>>,
{
    RcDoc::text(message)
}

pub(crate) fn nil<'a>() -> Doc<'a> {
    RcDoc::nil()
}

pub(crate) fn line<'a>() -> Doc<'a> {
    RcDoc::line()
}

pub(crate) fn hardline<'a>() -> Doc<'a> {
    RcDoc::hardline()
}

pub(crate) fn intersperse<'a, I, J>(docs: I, separator: J) -> Doc<'a>
where
    I: IntoIterator,
    I::Item: pretty::Pretty<'a, pretty::RcAllocator, ()>,
    J: IntoIterator,
    J::Item: pretty::Pretty<'a, pretty::RcAllocator, ()>,
{
    RcDoc::intersperse(docs, RcDoc::concat(separator))
}

/// locally unsets primitive projecitons
pub(crate) fn locally_unset_primitive_projections<'a>(doc: &Doc<'a>) -> Doc<'a> {
    group([
        text("Unset Primitive Projections."),
        hardline(),
        doc.clone(),
        hardline(),
        text("Global Set Primitive Projections."),
    ])
}

/// locally unsets primitive projecitons if the condition is satisfied
pub(crate) fn locally_unset_primitive_projections_if<'a>(
    condition: bool,
    doc: &Doc<'a>,
) -> Doc<'a> {
    if condition {
        locally_unset_primitive_projections(doc)
    } else {
        group([doc.clone(), hardline()])
    }
}

/// puts [doc] in a section or a module (that depends on [kind])
pub(crate) fn enclose<'a, K, U>(kind: K, name: U, doc: Doc<'a>) -> Doc<'a>
where
    U: Into<std::borrow::Cow<'a, str>> + std::marker::Copy,
    K: Into<std::borrow::Cow<'a, str>>,
{
    group([
        group([text(kind), line(), text(name), text(".")]),
        nest([hardline(), doc]),
        hardline(),
        group([text("End"), line(), text(name), text(".")]),
    ])
}

/// puts [doc] in a module of name [name]
pub(crate) fn module<'a>(name: &'a str, content: Vec<coq::TopLevelItem<'a>>) -> Doc<'a> {
    coq::Module::new(name, content).to_doc()
}

/// decides whether to enclose [doc] within a section with a context
pub(crate) fn add_context_in_section_if_necessary<'a>(
    name: &'a str,
    ty_params: &Vec<String>,
    doc: Doc<'a>,
) -> Doc<'a> {
    if ty_params.is_empty() {
        doc
    } else {
        coq::Section::new(
            name,
            &[
                coq::Context::new(&[coq::ArgSpec::new(
                    &coq::ArgDecl::Normal {
                        idents: ty_params.iter().map(|arg| arg.to_owned()).collect(),
                        ty: Some(coq::Expression::set()),
                    },
                    coq::ArgSpecKind::Implicit,
                )])
                .to_doc(),
                doc,
            ],
        )
        .to_doc()
    }
}

/// creates a definition of a typeclass corresponding
/// to a trait with the given type parameters and bounds
pub(crate) fn new_trait_typeclass_header<'a>(
    name: &str,
    ty_params: &Vec<(String, Option<Doc>)>,
    predicates: &Vec<Doc<'a>>,
    bounds: &[Doc<'a>],
    associated_types: &[(String, Vec<Doc<'a>>)],
) -> Doc<'a> {
    nest([
        text("Class "),
        text(name.to_owned()),
        line(),
        nest([
            nest([
                text("("),
                text("Self"),
                line(),
                text(":"),
                line(),
                coq::Expression::set().to_doc(false),
                text(")"),
            ]),
            bounds_sequence(bounds),
            if ty_params.is_empty() {
                nil()
            } else {
                concat([
                    line(),
                    nest([
                        text("{"),
                        concat(ty_params.iter().map(|(ty, default)| {
                            match default {
                                // @TODO: implement the translation of type parameters with default
                                Some(_default) => concat([
                                    text("(* TODO *)"),
                                    line(),
                                    text(ty.to_owned()),
                                    line(),
                                ]),
                                None => concat([text(ty.to_owned()), line()]),
                            }
                        })),
                        text(":"),
                        line(),
                        coq::Expression::set().to_doc(false),
                        text("}"),
                    ]),
                ])
            },
            if predicates.is_empty() {
                nil()
            } else {
                concat([line(), concat(predicates.clone())])
            },
        ]),
        intersperse(
            associated_types.iter().map(|(item_name, bounds)| {
                concat([
                    line(),
                    nest([
                        text("{"),
                        text(item_name.to_owned()),
                        text(" : "),
                        coq::Expression::set().to_doc(false),
                        text("}"),
                    ]),
                    bounds_sequence(bounds),
                ])
            }),
            [nil()],
        ),
        text(" :"),
        line(),
        text("Set := {"),
    ])
}

fn bounds_sequence<'a>(bounds: &[Doc<'a>]) -> Doc<'a> {
    if bounds.is_empty() {
        nil()
    } else {
        concat([line(), intersperse(bounds.to_vec(), [line()])])
    }
}

/// creates a body of a typeclass with the given items
pub(crate) fn new_typeclass_body<'a, I>(items: I) -> Doc<'a>
where
    I: IntoIterator,
    I::Item: pretty::Pretty<'a, pretty::RcAllocator, ()>,
{
    concat(items)
}

/// creates a type parameter as a field of a typeclass
pub(crate) fn typeclass_type_item<'a, U>(name: U) -> Doc<'a>
where
    U: Into<std::borrow::Cow<'a, str>> + std::marker::Copy,
{
    group([
        hardline(),
        nest([
            text(name),
            line(),
            text(":="),
            line(),
            text(name),
            text(";"),
        ]),
    ])
}

/// creates a typeclass field with the given name of the given type,
/// with the given type parameters and satisfying the given typeclass bounds
pub(crate) fn typeclass_definition_item<'a>(
    name: &'a str,
    ty_params: &'a Vec<String>,
    bounds: Vec<Doc<'a>>,
    ty: Doc<'a>,
) -> Doc<'a> {
    group([
        hardline(),
        nest([
            text(name),
            line(),
            monadic_typeclass_parameter(),
            line(),
            if ty_params.is_empty() {
                nil()
            } else {
                concat([
                    group([
                        text("{"),
                        intersperse(ty_params.iter(), [line()]),
                        text(": Set}"),
                    ]),
                    line(),
                ])
            },
            if bounds.is_empty() {
                nil()
            } else {
                concat([intersperse(bounds, [line()]), line()])
            },
            text(":"),
            line(),
            ty,
            text(";"),
        ]),
    ])
}

/// produces an instance of [Notation.Dot] or [Notation.DoubleColonType]
pub(crate) fn new_instance_header<'a, U>(
    name: U,
    trait_parameters: &[Doc<'a>],
    kind: Doc<'a>,
) -> Doc<'a>
where
    U: std::fmt::Display,
{
    nest([
        nest([
            text("Global Instance"),
            line(),
            text(format!("Method_{name}")),
            line(),
            intersperse(trait_parameters.to_owned(), [line()]),
        ]),
        line(),
        nest([
            text(": "),
            kind,
            line(),
            text(format!("\"{name}\"")),
            line(),
            text(":= {"),
        ]),
    ])
}

/// produces the body of an instance of [Notation.Dot] or [Notation.DoubleColonType]
pub(crate) fn new_instance_body<'a>(field: Doc<'a>, value: Doc<'a>) -> Doc<'a> {
    nest([field, text(" :="), line(), value, text(";")])
}

pub(crate) fn apply_argument<'a, U>(name: U, arg: Doc<'a>) -> Doc<'a>
where
    U: Into<std::borrow::Cow<'a, str>>,
{
    nest([
        text("("),
        text(name),
        line(),
        text(":="),
        line(),
        arg,
        text(")"),
    ])
}
