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
        queries.global_ctxt().unwrap();

        let output = queries
            .global_ctxt()
            .unwrap()
            .enter(|ctxt| top_level_to_coq(&ctxt));
        let mut file = File::create(&self.opts.output_file).unwrap();
        file.write_all(output.as_bytes()).unwrap();

        compiler.session().abort_if_errors();

        if self.opts.in_cargo {
            Compilation::Continue
        } else {
            Compilation::Stop
        }
    }
}
