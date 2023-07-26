use pretty::RcDoc;
use rustc_ast::LitKind;
use rustc_span::symbol::Symbol;

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
                        text("("),
                        intersperse(types, [line()]),
                        line(),
                        text(": Set)."),
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

pub(crate) fn module<'a, U>(name: U, doc: Doc<'a>) -> Doc<'a>
where
    U: Into<std::borrow::Cow<'a, str>> + std::marker::Copy,
{
    enclose("Module", name, &vec![], doc)
}

pub(crate) fn section<'a, U>(name: U, ty_context: &Vec<U>, doc: Doc<'a>) -> Doc<'a>
where
    U: Into<std::borrow::Cow<'a, str>> + std::marker::Copy,
{
    enclose("Section", name, ty_context, doc)
}

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
