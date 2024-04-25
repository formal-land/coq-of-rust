use crate::options::Options;
use crate::top_level::*;
use rustc_driver::{Callbacks, Compilation};
use rustc_interface::{interface::Compiler, Queries};
use std::fs::File;
use std::io::Write;

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

        let (_crate_name, coq_output) = queries.global_ctxt().unwrap().enter(|ctxt| {
            let current_crate_name = ctxt.crate_name(rustc_hir::def_id::LOCAL_CRATE);
            let current_crate_name_string = current_crate_name.to_string();

            eprintln!("Compiling crate {current_crate_name_string:}");

            (
                current_crate_name_string.clone(),
                top_level_to_coq(&ctxt, TopLevelOptions { axiomatize }),
            )
        });

        for (file_name, coq_output) in coq_output {
            let coq_file_name = file_name.replace(".rs", ".v");
            let mut file = File::create(coq_file_name).unwrap();

            file.write_all(coq_output.as_bytes()).unwrap();
        }

        compiler.sess.abort_if_errors();

        if self.opts.in_cargo {
            Compilation::Continue
        } else {
            Compilation::Stop
        }
    }
}
