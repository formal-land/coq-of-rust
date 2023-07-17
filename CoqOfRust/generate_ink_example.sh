#!/bin/bash

cd ../ink
# We do a "touch" to make sure that the compilation is restarted
touch crates/*/src/lib.rs
time cargo coq-of-rust --axiomatize
# Removing these files as they are too long
rm ink_codegen.v ink_ir.v ink_metadata.v
mv *.v ../CoqOfRust/ink/

cd integration-tests/erc20
touch lib.rs
time cargo coq-of-rust
mv erc20.v ../../../CoqOfRust/ink/
