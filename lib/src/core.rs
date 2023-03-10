use crate::top_level::*;
use rustc_errors::registry;
use rustc_session::config::{self, CheckCfg};
use std::path::PathBuf;
use std::{fs, path, process, str};
use walkdir::WalkDir;

pub const LINE_WIDTH: usize = 80;

fn change_to_coq_extension(path: &path::Path) -> PathBuf {
    let mut new_path = path.to_path_buf();
    new_path.set_extension("v");
    new_path
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
        let translation = create_translation_to_coq(PathBuf::from(src_folder));

        let write_to_path = dst_folder.join(
            change_to_coq_extension(src_folder)
                .file_name()
                .unwrap()
                .to_str()
                .unwrap(),
        );
        if !write_to_path.exists() {
            fs::create_dir_all(dst_folder).unwrap();
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
                let translation = create_translation_to_coq(PathBuf::from(src_path));
                fs::write(
                    dst_folder.join(change_to_coq_extension(relative_path)),
                    translation,
                )
                .unwrap();
            }
        }
    }
}

fn create_translation_to_coq(input_file_name: PathBuf) -> String {
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
        input: config::Input::File(input_file_name),
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
    println!("Starting to translate {filename:?}...");
    let now = std::time::Instant::now();
    let result = rustc_interface::run_compiler(config, |compiler| {
        compiler.enter(|queries| {
            queries.global_ctxt().unwrap().enter(|tcx| {
                let top_level = compile_top_level(tcx);
                top_level.to_pretty(LINE_WIDTH)
            })
        })
    });
    println!(
        "{} ms have passed to translate: {:?}",
        now.elapsed().as_millis(),
        filename
    );
    result
}
