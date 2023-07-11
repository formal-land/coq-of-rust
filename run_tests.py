""""
Run the snapshot tests for the project by translating all the example files.

Note that we only generate the output files. We do not check them, this can be
done using the `git diff` command.
"""

import os
import subprocess
import sys


test_folder = "examples"

# For each file recursively in the test folder
rs_files = []
for root, _dirs, files in os.walk(test_folder):
    rs_files += [
        os.path.join(root, file) for file in files if os.path.splitext(file)[1] == ".rs"
    ]

for index, file in enumerate(rs_files):
    print()
    print(f"Translating file {index + 1}/{len(rs_files)}: {file}")
    base = os.path.splitext(file)[0]
    # Translate the file, and save the error output if any
    command = (
        "cargo run --quiet --bin coq-of-rust -- translate --path "
        + file
        + " "
        + os.environ.get("COQ_OF_RUST_MORE_OPTS", "")
        + " 2> "
        + os.path.join("coq_translation", base + ".err")
    )
    print(command)

    try:
        subprocess.run(command, shell=True, check=True)
    except subprocess.CalledProcessError as e:
        print(f"Error occurred: {e}")
        sys.exit(1)
    except KeyboardInterrupt:
        print("Ctrl-C pressed, interrupting the script.")
        sys.exit(1)
