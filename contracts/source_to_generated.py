import os
import re
import shutil

source_dir = 'source'
generated_dir = 'generated'

# Create the target directory if it doesn't exist
if not os.path.exists(generated_dir):
    os.makedirs(generated_dir)

# List all files in the source directory
for filename in os.listdir(source_dir):
    # Check if the file is a Rust file
    if filename.endswith('.rs'):
        contract_name = os.path.splitext(filename)[0]
        source_file = os.path.join(source_dir, filename)
        target_dir = os.path.join(generated_dir, contract_name)
        target_file = os.path.join(target_dir, 'src', 'lib.rs')

        # Create subdirectory in the target directory if it doesn't exist
        os.makedirs(os.path.dirname(target_file), exist_ok=True)

        # Copy the source file
        shutil.copy2(source_file, target_file)
        print(f"Copied {source_file} to {target_file}")

        # Add the `Cargo.toml` file
        cargo_file = os.path.join('template', 'Cargo.toml')
        shutil.copy2(cargo_file, os.path.join(target_dir, 'Cargo.toml'))
        print(f"Copied {cargo_file} to {target_dir}")

        # Substitute the crate name in the `Cargo.toml` file
        with open(os.path.join(target_dir, 'Cargo.toml'), 'r+') as f:
            content = f.read()
            f.seek(0)
            f.write(content.replace('template', contract_name))
            f.truncate()

        # Add the `storage.rs` file
        storage_file = os.path.join('template', 'src', 'storage.rs')
        shutil.copy2(storage_file, os.path.join(
            target_dir, 'src', 'storage.rs'))
        print(f"Copied {storage_file} to {target_dir}")

        # Make the substitutions to fix the Rust contract's file
        with open(target_file, 'r+') as f:
            content = f.read()

            first_line = '#![cfg_attr(not(feature = "std"), no_std, no_main)]'
            content = content.replace(
                first_line,
                '#[macro_use]\nmod storage;'
            )

            content = content.replace(
                'use ink::storage::Mapping;',
                'use crate::storage::*; use crate::storage::Balance; use crate::storage::Error; \
                use crate::storage::Environment;',
            )

            content = content.replace(
                'Self::env()',
                'Self::init_env()',
            )

            content = content.replace(
                'ink::env::Error',
                'crate::storage::Error',
            )

            content = content.replace(
                'ink::env::',
                'crate::storage::',
            )

            content = content.replace(
                'ink::prelude::string',
                'crate::storage::string',
            )

            storage_name = "DefaultName"
            namesearch = re.search(
                    r"(\[ink\(storage\)]\s*\#\[derive\([^)]*\)]\s*)pub struct (\w+)",
                    content,
                )
            if namesearch:
              storage_name = namesearch.group(2)
            else:
              namesearch = re.search(  # Case for flipper
                    r"(\[ink\(storage\)]\s*)pub struct (\w+)",
                    content,
                )
              if namesearch: 
                storage_name = namesearch.group(2)

            print("Storage name: ", storage_name)
            content = content.replace(
                '#[ink(storage)]',
                'impl_storage!(%s);' % storage_name,
            )

            content = content.replace(
                'scale::Encode',
                'crate::storage::Encode'
            )

            content = content.replace(
                'scale::Decode',
                'crate::storage::Decode'
            )

            content = content.replace(
              'use ink::{',
              'use crate::storage::{'
            )

            content = content.replace(
              'prelude::',
              ''
            )

            content = content.replace(
              'primitives::',
              ''
            )

            macros_to_comment = [
                '#[ink::contract]',
                '#[ink::scale_derive(Encode, Decode, TypeInfo)]',
                '#[ink(constructor)]',
                '#[ink(event)]',
                '#[ink(message)]',
                '#[ink(storage)]',
                '#[ink(topic)]',
                '#[ink::trait_definition]',
                '#[ink(message, selector = 0xF23A6E61)]',
                '#[ink(message, selector = 0xBC197C81)]',
                '#[ink(message, selector = 0xBC197C81)]'
            ]
            for macro in macros_to_comment:
                content = content.replace(macro, '// ' + macro)
            f.seek(0)
            f.write(content)
            f.truncate()
