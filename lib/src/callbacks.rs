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

fn get_index_coq_file_content(file_names: Vec<String>) -> String {
    let mut index_content = String::new();

    for file_name in file_names {
        index_content.push_str(&format!(
            "Require Export {}.\n",
            file_name.replace(".rs", "").replace('/', "."),
        ));
    }

    index_content
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
            let current_crate_name_string = current_crate_name.to_string();

            println!("Compiling crate {current_crate_name_string:}");

            (
                current_crate_name_string.clone(),
                top_level_to_coq(&ctxt, TopLevelOptions { axiomatize }),
            )
        });

        for (file_name, coq_output) in coq_output.clone() {
            let coq_file_name = file_name.replace(".rs", ".v");
            println!("Writing to {coq_file_name:}");

            // We exclude this specific file as it is triggered by the `thread_local!` macro
            // but is not a file part of the current crate being translated.
            if coq_file_name.contains("library/std/src/sys/common/thread_local/fast_local.v") {
                println!("Skipping {coq_file_name:}");
                continue;
            }

            let mut file = File::create(coq_file_name).unwrap();
            file.write_all(coq_output.as_bytes()).unwrap();
        }

        let mut file = File::create(format!("{crate_name}.v")).unwrap();
        let index_content = get_index_coq_file_content(coq_output.keys().cloned().collect());

        file.write_all(index_content.as_bytes()).unwrap();

        compiler.sess.dcx().abort_if_errors();

        if self.opts.in_cargo {
            Compilation::Continue
        } else {
            Compilation::Stop
        }
    }
}
