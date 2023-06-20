#!/bin/sh

cd ../ink/crates/env
# We do a "touch" to make sure that the compilation is restarted
touch src/lib.rs
time cargo coq-of-rust
cd ../../../CoqOfRust
mv ../ink/ink_env.v ink/

cd ../ink/integration-tests/erc20
touch lib.rs
time cargo coq-of-rust
cd ../../../CoqOfRust
mv ../ink/integration-tests/erc20/erc20.v ink/
