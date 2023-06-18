#!/bin/sh

cd ../ink/crates/env
touch src/lib.rs
time cargo coq-of-rust
cd ../../..
mv ink/ink_env.v CoqOfRust/ink/
