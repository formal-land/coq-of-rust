""""
Run the snapshot tests for the project by translating all the example files.

Note that we only generate the output files. We do not check them, this can be
done using the `git diff` command.
"""

import os
import subprocess
import sys


test_folder = "examples"


def get_output_path() -> str:
    opts = sys.argv[1:]
    if not opts:
        return "coq_translation"

    it = iter(opts)
    while True:
        try:
            arg = next(it)
            if arg == "--output-path":
                return next(it)
        except StopIteration:
            break
    return "coq_translation"


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
    os.makedirs(
        os.path.dirname(os.path.join(get_output_path(), base + ".err")), exist_ok=True
    )
    # Translate the file, and save the error output if any
    command = (
        "cargo run --quiet --bin coq-of-rust -- translate --path "
        + file
        + " "
        + " ".join(sys.argv[1:])
        + " 2> "
        + os.path.join(get_output_path(), base + ".err")
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
