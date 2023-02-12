// NOTE: For the example to compile, you will need to first run the following:
//   rustup component add rustc-dev llvm-tools-preview

// version: 1.62.0-nightly (7c4b47696 2022-04-30)

extern crate rustc_ast;
extern crate rustc_ast_pretty;
extern crate rustc_error_codes;
extern crate rustc_errors;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;

use crate::top_level::*;
use rustc_errors::registry;
use rustc_session::config::{self, CheckCfg};
use rustc_span::source_map;
use std::path::PathBuf;
use std::{fs, path, process, str};
use walkdir::WalkDir;

pub const LINE_WIDTH: usize = 80;

fn change_to_coq_extension(path: &path::Path) -> PathBuf {
    let mut new_path = path.to_path_buf();
    new_path.set_extension("v");
    return new_path;
}
pub fn run(src_folder: &path::Path) {
    let basic_folder_name = "coq_translation";
    let unique_folder_name = format!(
        "{}/{}/",
        basic_folder_name,
        src_folder.file_name().unwrap().to_str().unwrap(),
    );
    let dst_folder = path::Path::new(&unique_folder_name);
    if src_folder.is_file() {
        let contents = fs::read_to_string(src_folder).unwrap();
        let translation = create_translation_to_coq(
            src_folder
                .file_name()
                .unwrap()
                .to_str()
                .unwrap()
                .to_string(),
            contents,
        );

        let write_to_path = dst_folder.join(
            change_to_coq_extension(src_folder)
                .file_name()
                .unwrap()
                .to_str()
                .unwrap()
                .to_string(),
        );
        if !write_to_path.exists() {
            fs::create_dir_all(&dst_folder).unwrap();
        }
        fs::write(write_to_path, translation).unwrap();
    } else {
        for entry in WalkDir::new(src_folder) {
            let entry = entry.unwrap();
            let src_path = entry.path();

            // calculate the relative path from the source to the destination directory
            let relative_path = src_path.strip_prefix(src_folder).unwrap();
            let dst_path = dst_folder.join(relative_path);

            // if the entry is a directory, create it in the destination directory
            if src_path.is_dir() {
                fs::create_dir_all(&dst_path).unwrap();
            } else {
                // if the entry is a file, create a Coq version of it and write it to the destination directory
                let contents = fs::read_to_string(src_path).unwrap();
                let translation = create_translation_to_coq(
                    src_path.file_name().unwrap().to_str().unwrap().to_string(),
                    contents,
                );
                fs::write(
                    dst_folder.join(change_to_coq_extension(relative_path)),
                    translation,
                )
                .unwrap();
            }
        }
    }
}

fn create_translation_to_coq(input_file_name: String, contents: String) -> String {
    let filename = input_file_name.clone();
    let out = process::Command::new("rustc")
        .arg("--print=sysroot")
        .current_dir(".")
        .output()
        .unwrap();
    let sysroot = str::from_utf8(&out.stdout).unwrap().trim();
    let config = rustc_interface::Config {
        opts: config::Options {
            maybe_sysroot: Some(path::PathBuf::from(sysroot)),
            ..config::Options::default()
        },
        input: config::Input::Str {
            name: source_map::FileName::Custom(input_file_name),
            input: contents.to_string(),
        },
        crate_cfg: rustc_hash::FxHashSet::default(),
        crate_check_cfg: CheckCfg::default(),
        input_path: None,
        output_dir: None,
        output_file: None,
        file_loader: None,
        lint_caps: rustc_hash::FxHashMap::default(),
        parse_sess_created: None,
        register_lints: None,
        override_queries: None,
        make_codegen_backend: None,
        registry: registry::Registry::new(rustc_error_codes::DIAGNOSTICS),
    };
    let now = std::time::Instant::now();
    let result = rustc_interface::run_compiler(config, |compiler| {
        compiler.enter(|queries| {
            queries.global_ctxt().unwrap().take().enter(|tcx| {
                let top_level = compile_top_level(tcx);
                let top_level_str = top_level.to_pretty(LINE_WIDTH).to_string();
                top_level_str
            })
        })
    });
    println!(
        "{} ms have passed to translate: {}",
        now.elapsed().as_millis(),
        filename
    );
    return result;
}
