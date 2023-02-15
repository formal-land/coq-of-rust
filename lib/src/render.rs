extern crate rustc_ast;
extern crate rustc_span;

use pretty::RcDoc;

pub(crate) fn paren(with_paren: bool, doc: RcDoc<()>) -> RcDoc<()> {
    if with_paren {
        RcDoc::concat([RcDoc::text("("), doc, RcDoc::text(")")])
    } else {
        doc
    }
}

pub(crate) fn bracket(doc: RcDoc<()>) -> RcDoc<()> {
    return RcDoc::concat([RcDoc::text("["), doc, RcDoc::text("]")]);
}

fn round_symbol(symbol: &rustc_span::symbol::Symbol) -> i32 {
    let s = symbol.as_str();
    s.parse::<f64>().unwrap().round() as i32
}

pub(crate) fn literal_to_doc(literal: &rustc_ast::LitKind) -> RcDoc<()> {
    match literal {
        rustc_ast::LitKind::Str(s, _) => RcDoc::text(format!("{s:?}")),
        rustc_ast::LitKind::Int(i, _) => RcDoc::text(format!("{i}")),
        rustc_ast::LitKind::Float(f, _) => RcDoc::text(format!("{} (* {f} *)", round_symbol(f))),
        rustc_ast::LitKind::Bool(b) => RcDoc::text(format!("{b}")),
        rustc_ast::LitKind::Char(c) => RcDoc::text(format!("{c}")),
        rustc_ast::LitKind::Byte(b) => RcDoc::text(format!("{b}")),
        rustc_ast::LitKind::ByteStr(b, _) => RcDoc::text(format!("{b:?}")),
        rustc_ast::LitKind::Err => RcDoc::text("Err"),
    }
}

pub(crate) fn indent(doc: RcDoc<()>) -> RcDoc<()> {
    let indent_space_offset = 2;
    doc.nest(indent_space_offset)
}
