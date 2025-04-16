#![allow(dead_code)] // TODO: remove when we settle on implementation details and publicly export
#![no_std]

extern crate alloc;

mod rescue;
mod util;

pub use rescue::*;
