""""
Run the snapshot tests for the project by translating all the example files.

Note that we only generate the output files. We do not check them, this can be
done using the `git diff` command.
"""

import os
import subprocess
import sys
import multiprocessing as mp


test_folder = "examples"

# For each file recursively in the test folder
rs_files = []
for root, _dirs, files in os.walk(test_folder):
    rs_files += [
        os.path.join(root, file) for file in files if os.path.splitext(file)[1] == ".rs"
    ]


def compile_with_option(file: str, output_path: str, is_axiomatized: bool):
    base = os.path.splitext(file)[0]
    os.makedirs(os.path.dirname(output_path), exist_ok=True)

    # Translate the file, and save the error output if any
    command = (
        "cargo run --quiet --bin coq-of-rust -- translate --path "
        + file
        + " "
        + ("--axiomatize " if is_axiomatized else "")
        + "--output-path " + output_path
        + " 2> "
        + os.path.join(output_path, base + ".err")
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


def compile(index, file):
    print()
    print(f"Translating file {index + 1}/{len(rs_files)}: {file}")
    compile_with_option(file, "CoqOfRust/examples/default/", False)
    compile_with_option(file, "CoqOfRust/examples/axiomatized/", True)


# run in parallel
pool = mp.Pool(processes=(1 if os.environ.get(
    "RUN_TESTS_SINGLE_PROCESS") else None))
pool.starmap(compile, enumerate(rs_files))
