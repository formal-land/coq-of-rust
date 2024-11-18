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
        let crate::options::Options {
            axiomatize,
            with_json,
            ..
        } = self.opts;

        queries.global_ctxt().unwrap();

        let (crate_name, translation) = queries.global_ctxt().unwrap().enter(|ctxt| {
            let current_crate_name = ctxt.crate_name(rustc_hir::def_id::LOCAL_CRATE);
            let current_crate_name_string = current_crate_name.to_string();

            println!("Compiling crate {current_crate_name_string:}");

            (
                current_crate_name_string.clone(),
                translate_top_level(&ctxt, TopLevelOptions { axiomatize }),
            )
        });

        let mut file = File::create(format!("{crate_name}.v")).unwrap();
        let index_content = get_index_coq_file_content(translation.keys().cloned().collect());

        file.write_all(index_content.as_bytes()).unwrap();

        for (file_name, (coq_translation, json_translation)) in translation {
            let coq_file_name = file_name.replace(".rs", ".v");
            println!("Writing to {coq_file_name:}");

            let file = File::create(coq_file_name.clone());

            // For some of the files we cannot create the output as the path is not accessible,
            // especially for files corresponding to part of the standard library that appear
            // sometimes in the translation.
            if file.is_err() {
                println!("Failed to create {coq_file_name:}");
                continue;
            }

            file.unwrap().write_all(coq_translation.as_bytes()).unwrap();

            if with_json {
                let json_file_name = file_name.replace(".rs", ".json");
                let mut file = File::create(json_file_name).unwrap();
                file.write_all(json_translation.as_bytes()).unwrap();
            }
        }

        compiler.sess.dcx().abort_if_errors();

        if self.opts.in_cargo {
            Compilation::Continue
        } else {
            Compilation::Stop
        }
    }
}
