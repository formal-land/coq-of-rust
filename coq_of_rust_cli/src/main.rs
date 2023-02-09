use std::path::Path;

extern crate coq_of_rust_lib;

fn main() {
    let src_folder = Path::new("examples-from-rust-book");

    coq_of_rust_lib::coq_of_rust::coq_of_rust::run(src_folder);
}
