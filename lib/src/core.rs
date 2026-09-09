use crate::top_level::*;
use std::path::PathBuf;
use std::{fs, path, process, str};
use walkdir::WalkDir;

/// CLI options
pub struct CliOptions {
    pub path: path::PathBuf,
    pub output: path::PathBuf,
    pub axiomatize: bool,
}

pub const LINE_WIDTH: usize = 80;

fn change_to_rocq_extension(path: &path::Path) -> PathBuf {
    let mut new_path = path.to_path_buf();
    new_path.set_extension("v");
    new_path
}

/// Write the content to a file only if it changed. This optimization is useful
/// in order not to force the `make` command to rebuild files that did not
/// change.
fn write_if_changed<P: AsRef<path::Path>, C: AsRef<[u8]>>(
    path: P,
    new_content: C,
) -> std::io::Result<()> {
    let path = path.as_ref();
    let new_content = new_content.as_ref();

    // If the file does not exist, or if the content is different, write the new
    // content to the file.
    if !path.exists() || new_content != fs::read(path)? {
        fs::write(path, new_content)?;
    }

    Ok(())
}

pub fn run(opts: CliOptions) {
    let src_path = &opts.path;
    let src_folder = if src_path.is_file() {
        src_path.parent().unwrap()
    } else {
        src_path
    };
    let basic_folder_name = opts.output.to_str().unwrap();
    let unique_folder_name = format!("{}/{}/", basic_folder_name, src_folder.to_str().unwrap(),);
    let dst_folder = path::Path::new(&unique_folder_name);
    if src_path.is_file() {
        let translation = create_translation_to_rocq(&opts);

        let path_to_write = dst_folder.join(
            change_to_rocq_extension(src_path)
                .file_name()
                .unwrap()
                .to_str()
                .unwrap(),
        );
        if !path_to_write.exists() {
            fs::create_dir_all(dst_folder).unwrap();
        }
        write_if_changed(path_to_write, translation).unwrap();
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
                // filter out files not ending with .rs
                if src_path
                    .extension()
                    .is_none_or(|extension| extension != "rs")
                {
                    continue;
                }
                // if the entry is a file, create a Rocq version of it and write it to the destination directory
                let translation = create_translation_to_rocq(&opts);
                write_if_changed(
                    dst_folder.join(change_to_rocq_extension(relative_path)),
                    translation,
                )
                .unwrap();
            }
        }
    }
}

fn create_translation_to_rocq(opts: &CliOptions) -> String {
    let input_file_name: PathBuf = PathBuf::from(&opts.path);
    let filename = input_file_name.clone();
    let out = process::Command::new("rustc")
        .arg("--print=sysroot")
        .current_dir(".")
        .output()
        .unwrap();
    let sysroot = str::from_utf8(&out.stdout).unwrap().trim();

    println!("Starting to translate {filename:?}...");

    let now = std::time::Instant::now();

    struct TranslateSingleFile {
        axiomatize: bool,
        translation: Option<std::collections::HashMap<String, (String, String)>>,
    }

    impl rustc_driver::Callbacks for TranslateSingleFile {
        fn after_expansion<'tcx>(
            &mut self,
            _compiler: &rustc_interface::interface::Compiler,
            tcx: rustc_middle::ty::TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            self.translation = Some(translate_top_level(
                &tcx,
                TopLevelOptions {
                    axiomatize: self.axiomatize,
                    separate_runtime_file: false,
                    runtime_module_prefix: None,
                },
            ));
            rustc_driver::Compilation::Stop
        }
    }

    let mut callbacks = TranslateSingleFile {
        axiomatize: opts.axiomatize,
        translation: None,
    };
    let args = vec![
        "rustc".to_string(),
        filename.to_string_lossy().to_string(),
        "--test".to_string(),
        format!("--sysroot={sysroot}"),
    ];

    rustc_driver::run_compiler(&args, &mut callbacks);
    let translation = callbacks.translation.unwrap_or_default();

    println!(
        "{} ms have passed to translate: {:?}",
        now.elapsed().as_millis(),
        filename
    );

    match translation.iter().next() {
        Some((_, (rocq_translation, _json_translation))) => rocq_translation.clone(),
        None => {
            eprintln!("No result from the compiler");

            "".to_string()
        }
    }
}
