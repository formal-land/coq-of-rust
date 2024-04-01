use rustc_middle::ty::TyCtxt;

/// The environment used for the translation steps, holding various state
/// information
pub(crate) struct Env<'a> {
    pub(crate) tcx: TyCtxt<'a>,
    pub(crate) axiomatize: bool,
}

/// emits a warning with the given messages
pub(crate) fn emit_warning_with_note(
    env: &Env,
    span: &rustc_span::Span,
    warning_msg: &str,
    note_msg: &Option<&str>,
) {
    let warn = env
        .tcx
        .sess
        .struct_span_warn(*span, warning_msg.to_string());
    match note_msg {
        Some(note) => warn.note(note.to_owned()).emit(),
        None => warn.emit(),
    }
}
