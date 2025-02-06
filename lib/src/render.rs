use pretty::{DocAllocator, DocBuilder};

/// Insert a Doc block when the predicate(usually is_empty()) doesn't satisfy.
pub(crate) fn optional_insert<'a, D>(
    ψ: &'a D,
    when_not: bool,
    insert_doc: DocBuilder<'a, D>,
) -> DocBuilder<'a, D>
where
    D: DocAllocator<'a>,
    D::Doc: Clone,
{
    if when_not {
        ψ.nil()
    } else {
        insert_doc
    }
}

/// Insert a Doc block 'insert_doc' if the predicate isn't satisfied. Otherwise, insert the `with_doc` content.
pub(crate) fn optional_insert_with<'a, D>(
    when_not: bool,
    with_doc: DocBuilder<'a, D>,
    insert_doc: DocBuilder<'a, D>,
) -> DocBuilder<'a, D>
where
    D: DocAllocator<'a>,
    D::Doc: Clone,
{
    if !when_not {
        insert_doc
    } else {
        with_doc
    }
}

/// encloses an expression in curly brackets
pub(crate) fn curly_brackets<'a, D>(ψ: &'a D, doc: DocBuilder<'a, D>) -> DocBuilder<'a, D>
where
    D: DocAllocator<'a>,
    D::Doc: Clone,
{
    ψ.concat([ψ.text("{"), doc, ψ.text("}")])
}

/// encloses an expression in regular brackets
pub(crate) fn round_brackets<'a, D>(ψ: &'a D, doc: DocBuilder<'a, D>) -> DocBuilder<'a, D>
where
    D: DocAllocator<'a>,
    D::Doc: Clone,
{
    ψ.concat([ψ.text("("), doc, ψ.text(")")])
}

pub(crate) fn paren<'a, D>(ψ: &'a D, with_paren: bool, doc: DocBuilder<'a, D>) -> DocBuilder<'a, D>
where
    D: DocAllocator<'a>,
    D::Doc: Clone,
{
    if with_paren {
        round_brackets(ψ, doc)
    } else {
        doc
    }
}

// Concat several documents and indent when splitting the line
pub(crate) fn nest<'a, D, I>(ψ: &'a D, docs: I) -> DocBuilder<'a, D>
where
    D: DocAllocator<'a>,
    D::Doc: Clone,
    I: IntoIterator<Item = DocBuilder<'a, D>>,
{
    let indent_space_offset = 2;
    ψ.concat(docs).nest(indent_space_offset).group()
}

// Concat several documents and do *not* indent when splitting the line
pub(crate) fn group<'a, D, I>(ψ: &'a D, docs: I) -> DocBuilder<'a, D>
where
    D: DocAllocator<'a>,
    D::Doc: Clone,
    I: IntoIterator<Item = DocBuilder<'a, D>>,
{
    ψ.concat(docs).group()
}

/// puts [doc] in a section or a module (that depends on [kind])
pub(crate) fn enclose<'a, D, K>(
    ψ: &'a D,
    kind: K,
    name: String,
    indent: bool,
    doc: DocBuilder<'a, D>,
) -> DocBuilder<'a, D>
where
    D: DocAllocator<'a>,
    D::Doc: Clone,
    K: Into<std::borrow::Cow<'a, str>>,
{
    group(
        ψ,
        [
            nest(
                ψ,
                [ψ.text(kind), ψ.text(" "), ψ.text(name.clone()), ψ.text(".")],
            ),
            if indent {
                nest(ψ, [ψ.hardline(), doc])
            } else {
                group(ψ, [ψ.hardline(), doc])
            },
            ψ.hardline(),
            nest(ψ, [ψ.text("End "), ψ.text(name), ψ.text(".")]),
        ],
    )
}

pub(crate) fn list<'a, D>(ψ: &'a D, docs: Vec<DocBuilder<'a, D>>) -> DocBuilder<'a, D>
where
    D: DocAllocator<'a>,
    D::Doc: Clone,
{
    if docs.is_empty() {
        return ψ.text("[]");
    }

    group(
        ψ,
        [
            nest(
                ψ,
                [
                    ψ.text("["),
                    ψ.line(),
                    ψ.intersperse(docs, ψ.concat([ψ.text(";"), ψ.line()])),
                ],
            ),
            ψ.line(),
            ψ.text("]"),
        ],
    )
}

pub(crate) fn capitalize(s: &str) -> String {
    let mut chars = s.chars();
    match chars.next() {
        None => String::new(),
        Some(f) => f.to_uppercase().collect::<String>() + chars.as_str(),
    }
}
