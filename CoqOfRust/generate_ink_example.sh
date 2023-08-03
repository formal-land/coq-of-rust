#!/bin/bash -x

CONFIG_FILE="$PWD/../coq-of-rust-config.json"
cd ../ink

# Translate the Ink libraries
# We do a "touch" to make sure that the compilation is restarted
touch crates/*/src/lib.rs
time cargo coq-of-rust --axiomatize --configuration-file $CONFIG_FILE
# Removing these files as they are too long
rm ink_codegen.v ink_ir.v ink_metadata.v
mv *.v ../CoqOfRust/ink/

# Translate the ERC20 example
cd integration-tests/erc20
touch lib.rs
time cargo coq-of-rust --configuration-file $CONFIG_FILE
mv erc20.v ../../../CoqOfRust/ink/

# Apply manual changes to the translations
cd ../../../CoqOfRust/ink/
python update_after_translation.py
