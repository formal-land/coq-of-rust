use crate::coq;
use pretty::RcDoc;

// use crate::coq;

/// provides the instance of the Struct.Trait typeclass
/// for definitions of functions and constants
/// which types utilize the M monad constructor
// pub(crate) fn monadic_typeclass_parameter<'a>() -> Doc<'a> {
//     coq::ArgDecl::monadic_typeclass_parameter().to_doc()
// }

/// Insert a Doc block when the predicate(usually is_empty()) doesn't satisfy.
pub(crate) fn optional_insert(when_not: bool, insert_doc: RcDoc<()>) -> RcDoc<()> {
    if when_not {
        nil()
    } else {
        insert_doc
    }
}

/// Insert a Vec block when the predicate(usually is_empty()) doesn't satisfy.
#[allow(dead_code)]
pub(crate) fn optional_insert_vec<T>(when_not: bool, insert_vec: Vec<T>) -> Vec<T> {
    if when_not {
        vec![]
    } else {
        insert_vec
    }
}

/// Insert a Doc block 'insert_doc' if the predicate isn't satisfied. Otherwise, insert the `with_doc` content.
pub(crate) fn optional_insert_with<'a>(
    when_not: bool,
    with_doc: RcDoc<'a>,
    insert_doc: RcDoc<'a>,
) -> RcDoc<'a> {
    if !when_not {
        insert_doc
    } else {
        with_doc
    }
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

fn string_pieces_to_coq<'a>(_with_paren: bool, pieces: &[StringPiece]) -> coq::Expression<'a> {
    match pieces {
        [] => coq::Expression::just_name("\"\""),
        [StringPiece::AsciiString(s), rest @ ..] => {
            let head = coq::Expression::just_name(
                format!("\"{}\"", str::replace(s, "\"", "\"\"")).as_str(),
            );
            if rest.is_empty() {
                head
            } else {
                head.apply_many(&[
                    coq::Expression::just_name("++"),
                    string_pieces_to_coq(false, rest),
                ])
            }
        }
        [StringPiece::UnicodeChar(c), rest @ ..] => coq::Expression::just_name("String.String")
            .apply_many(&[
                coq::Expression::just_name(format!("\"{:03}\"", *c as u8).as_str()),
                string_pieces_to_coq(true, rest),
            ]),
    }
}

pub(crate) fn string_to_coq(message: &str) -> coq::Expression {
    let pieces = cut_string_in_pieces_for_coq(message);
    coq::Expression::just_name("mk_str").apply(&string_pieces_to_coq(true, &pieces))
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

/// puts [doc] in a section or a module (that depends on [kind])
pub(crate) fn enclose<'a, K>(kind: K, name: String, indent: bool, doc: Doc<'a>) -> Doc<'a>
where
    K: Into<std::borrow::Cow<'a, str>>,
{
    group([
        nest([text(kind), text(" "), text(name.clone()), text(".")]),
        (if indent { nest } else { group })([hardline(), doc]),
        hardline(),
        nest([text("End "), text(name), text(".")]),
    ])
}

pub(crate) fn list<'a, Item>(docs: Vec<Item>) -> Doc<'a>
where
    Item: pretty::Pretty<'a, pretty::RcAllocator, ()>,
{
    if docs.is_empty() {
        return text("[]");
    }

    group([
        nest([text("["), line(), intersperse(docs, [text(";"), line()])]),
        line(),
        text("]"),
    ])
}

pub(crate) fn capitalize(s: &str) -> String {
    let mut chars = s.chars();
    match chars.next() {
        None => String::new(),
        Some(f) => f.to_uppercase().collect::<String>() + chars.as_str(),
    }
}
