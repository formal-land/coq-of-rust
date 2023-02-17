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

pub(crate) fn bracket(doc: RcDoc<()>) -> RcDoc<()> {
    return RcDoc::concat([RcDoc::text("["), doc, RcDoc::text("]")]);
}

fn round_symbol(symbol: &Symbol) -> i32 {
    let s = symbol.as_str();
    s.parse::<f64>().unwrap().round() as i32
}

pub(crate) fn literal_to_doc(literal: &LitKind) -> RcDoc<()> {
    match literal {
        LitKind::Str(s, _) => RcDoc::text(format!("{s:?}")),
        LitKind::Int(i, _) => RcDoc::text(format!("{i}")),
        LitKind::Float(f, _) => RcDoc::text(format!("{} (* {f} *)", round_symbol(f))),
        LitKind::Bool(b) => RcDoc::text(format!("{b}")),
        LitKind::Char(c) => RcDoc::text(format!("{c}")),
        LitKind::Byte(b) => RcDoc::text(format!("{b}")),
        LitKind::ByteStr(b, _) => RcDoc::text(format!("{b:?}")),
        LitKind::Err => RcDoc::text("Err"),
    }
}

pub(crate) fn indent(doc: RcDoc<()>) -> RcDoc<()> {
    let indent_space_offset = 2;
    doc.nest(indent_space_offset)
}
