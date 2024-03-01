#![feature(rustc_private)]
#![feature(internal_output_capture)]
#![feature(backtrace_frames)]

extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_ast_pretty;
extern crate rustc_driver;
extern crate rustc_error_codes;
extern crate rustc_errors;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_hir_analysis;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_type_ir;

pub mod callbacks;
pub mod configuration;
pub mod coq;
pub mod core;
pub mod env;
pub mod expression;
pub mod header;
pub mod options;
pub mod path;
pub mod pattern;
pub mod render;
pub mod reorder;
pub mod thir_expression;
pub mod thir_pattern;
pub mod thir_ty;
pub mod top_level;
pub mod ty;
pub mod utils;
