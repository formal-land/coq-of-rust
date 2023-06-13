#!/bin/sh

cd ../ink/crates/env
touch src/lib.rs
time cargo coq-of-rust
cd ../../..
mv ink/Crate.v CoqOfRust/ink/Env.v
