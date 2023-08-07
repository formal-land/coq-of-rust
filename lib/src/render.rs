use pretty::RcDoc;
use rustc_ast::LitKind;
use rustc_span::symbol::Symbol;

/// provides the instance of the Struct.Trait typeclass
/// for definitions of functions and constants
/// which types utilize the M monad constructor
pub(crate) fn monadic_typeclass_parameter<'a>() -> Doc<'a> {
    // TODO: check whether the name of the parameter is necessary
    text("`{H : State.Trait}")
}

pub(crate) fn paren(with_paren: bool, doc: RcDoc<()>) -> RcDoc<()> {
    if with_paren {
        RcDoc::concat([RcDoc::text("("), doc, RcDoc::text(")")])
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

/// locally unsets primitive projecitons if the condition is satisfied
pub(crate) fn locally_unset_primitive_projections(condition: bool, doc: Doc) -> Doc {
    group(if condition {
        [
            group([text("Unset Primitive Projections."), hardline()]),
            doc,
            group([hardline(), text("Global Set Primitive Projections.")]),
        ]
    } else {
        [nil(), doc, hardline()]
    })
}

/// puts [doc] in a section or a module (that depends on [kind])
pub(crate) fn enclose<'a, K, U>(kind: K, name: U, ty_context: &Vec<U>, doc: Doc<'a>) -> Doc<'a>
where
    U: Into<std::borrow::Cow<'a, str>> + std::marker::Copy,
    K: Into<std::borrow::Cow<'a, str>>,
{
    group([
        group([text(kind), line(), text(name), text(".")]),
        nest([
            hardline(),
            if ty_context.is_empty() {
                nil()
            } else {
                let types: Vec<Doc<'a>> = ty_context.iter().map(|&ty| text(ty)).collect();
                group([
                    nest([
                        text("Context"),
                        line(),
                        text("{"),
                        intersperse(types, [line()]),
                        line(),
                        text(": Set}."),
                    ]),
                    hardline(),
                ])
            },
            doc,
        ]),
        hardline(),
        group([text("End"), line(), text(name), text(".")]),
    ])
}

/// puts [doc] in a module of name [name]
pub(crate) fn module<'a, U>(name: U, doc: Doc<'a>) -> Doc<'a>
where
    U: Into<std::borrow::Cow<'a, str>> + std::marker::Copy,
{
    enclose("Module", name, &vec![], doc)
}

/// puts [doc] in a section of name [name] with type parameters from [ty_context]
pub(crate) fn section<'a, U>(name: U, ty_context: &Vec<U>, doc: Doc<'a>) -> Doc<'a>
where
    U: Into<std::borrow::Cow<'a, str>> + std::marker::Copy,
{
    enclose("Section", name, ty_context, doc)
}

/// decides whether to enclose [doc] within a section
pub(crate) fn add_section_if_necessary<'a, U>(name: U, ty_params: &Vec<U>, doc: Doc<'a>) -> Doc<'a>
where
    U: Into<std::borrow::Cow<'a, str>> + std::marker::Copy,
{
    if ty_params.is_empty() {
        doc
    } else {
        section(name, ty_params, doc)
    }
}

pub(crate) fn trait_typeclass<'a, U, I>(
    ty_params: &Vec<(U, Option<Doc>)>,
    types_with_bounds: &[(U, Vec<Doc<'a>>)],
    items: I,
) -> Doc<'a>
where
    I: IntoIterator,
    I::Item: pretty::Pretty<'a, pretty::RcAllocator, ()>,
    U: Into<std::borrow::Cow<'a, str>> + std::marker::Copy,
{
    group([
        nest([
            new_trait_typeclass_header(ty_params, types_with_bounds),
            new_typeclass_body(items),
        ]),
        hardline(),
        text("}."),
    ])
}

/// creates a definition of a typeclass corresponding
/// to a trait with the given type parameters and bounds
pub(crate) fn new_trait_typeclass_header<'a, U>(
    ty_params: &Vec<(U, Option<Doc>)>,
    types_with_bounds: &[(U, Vec<Doc<'a>>)],
) -> Doc<'a>
where
    U: Into<std::borrow::Cow<'a, str>> + std::marker::Copy,
{
    nest([
        text("Class Trait"),
        line(),
        nest([
            text("("),
            text("Self"),
            line(),
            text(":"),
            line(),
            text("Set"),
            text(")"),
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
                                Some(_default) => {
                                    concat([text("(* TODO *)"), line(), text(*ty), line()])
                                }
                                None => concat([text(*ty), line()]),
                            }
                        })),
                        text(":"),
                        line(),
                        text("Set"),
                        text("}"),
                    ]),
                ])
            },
        ]),
        intersperse(
            types_with_bounds.iter().map(|(item_name, bounds)| {
                concat([
                    line(),
                    nest([
                        text("{"),
                        text(*item_name),
                        text(" : "),
                        text("Set"),
                        text("}"),
                    ]),
                    concat(bounds.iter().map(|x| {
                        concat([
                            line(),
                            // @TODO: include default parameters
                            nest([
                                text("`{"),
                                x.clone(),
                                text(".Trait"),
                                line(),
                                text(*item_name),
                                text("}"),
                            ]),
                        ])
                    })),
                ])
            }),
            [nil()],
        ),
        text(" :"),
        line(),
        text("Set := {"),
    ])
}

/// creates a body of a typeclass with the given items
pub(crate) fn new_typeclass_body<'a, I>(items: I) -> Doc<'a>
where
    I: IntoIterator,
    I::Item: pretty::Pretty<'a, pretty::RcAllocator, ()>,
{
    intersperse(items, [nil()])
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

/// creates a field with the given name of a typeclass of the given type,
/// with the given type parameters and satisfying the given typeclass bounds
pub(crate) fn typeclass_definition_item<'a, U, V, W>(
    name: U,
    ty_params: &'a Vec<V>,
    bounds: Vec<W>,
    ty: Doc<'a>,
) -> Doc<'a>
where
    U: Into<std::borrow::Cow<'a, str>>,
    &'a V: pretty::Pretty<'a, pretty::RcAllocator, ()>,
    W: pretty::Pretty<'a, pretty::RcAllocator, ()>,
{
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

// produces an instance of [Notation.Dot] or [Notation.DoubleColonType]
pub(crate) fn new_instance_header<U>(name: U, kind: Doc) -> Doc
where
    U: std::fmt::Display,
{
    nest([
        nest([
            text("Global Instance"),
            line(),
            text(format!("Method_{name}")),
            line(),
            monadic_typeclass_parameter(),
            line(),
            text("`(Trait)"),
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

pub(crate) fn new_instance_body<'a>(field: Doc<'a>, value: Doc<'a>) -> Doc<'a> {
    nest([field, text(" :="), line(), value, text(";")])
}

#[allow(dead_code)]
pub(crate) fn notation_dot_instance<'a, U>(name: U) -> Doc<'a>
where
    U: Into<std::borrow::Cow<'a, str>>,
{
    nest([
        text("Notation.dot"),
        line(),
        text(":="),
        line(),
        text("@"),
        text(name),
        text(";"),
    ])
}
