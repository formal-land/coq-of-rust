use std::fs::File;
use std::io::Write;

use rustc_driver::{Callbacks, Compilation};
use rustc_interface::{interface::Compiler, Queries};

use crate::options::Options;

use crate::top_level::*;

pub struct ToCoq {
    opts: Options,
}

impl ToCoq {
    pub fn new(opts: Options) -> Self {
        ToCoq { opts }
    }
}

impl Callbacks for ToCoq {
    fn after_expansion<'tcx>(
        &mut self,
        compiler: &Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        let axiomatize = self.opts.axiomatize;
        queries.global_ctxt().unwrap();

        let (crate_name, coq_output) = queries.global_ctxt().unwrap().enter(|ctxt| {
            let current_crate_name = ctxt.crate_name(rustc_hir::def_id::LOCAL_CRATE);
            (
                current_crate_name.to_string(),
                top_level_to_coq(&ctxt, TopLevelOptions { axiomatize }),
            )
        });
        let mut file = File::create(format!("{crate_name}.v")).unwrap();
        file.write_all(coq_output.as_bytes()).unwrap();

        compiler.session().abort_if_errors();

        if self.opts.in_cargo {
            Compilation::Continue
        } else {
            Compilation::Stop
        }
    }
}
