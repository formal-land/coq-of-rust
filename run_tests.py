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
    os.makedirs(
        os.path.dirname(os.path.join(output_path, base + ".err")), exist_ok=True
    )
    # Translate the file, and save the error output if any
    command = (
        "cargo run --quiet --bin coq-of-rust -- translate --path "
        + file
        + " "
        + ("--axiomatize --axiomatize-public " if is_axiomatized else "")
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


def update_erc_20():
    file_name = "CoqOfRust/examples/default/examples/ink_contracts/erc20.v"
    with open(file_name, "r") as f:
        content = f.read()

    content = content.replace(
        "Module  Mapping.",
        """Require Import CoqOfRust.examples.default.examples.ink_contracts.Lib.

Module Mapping := Mapping.

(* Module  Mapping. (*""",
    )
    content = content.replace(
        "End Impl_erc20_Mapping_t_K_V.",
        "End Impl_erc20_Mapping_t_K_V. *)",
    )

    content = content.replace(
        """Definition init_env : M erc20.Env.t :=
    M.function_body
      (let* α0 := core.panicking.panic (mk_str "not implemented") in
      let* α1 : M.Val never.t := M.alloc α0 in
      never_to_any α1).""",
        """Definition init_env : M erc20.Env.t :=
    M.read_env."""
    )

    with open(file_name, "w") as f:
        f.write(content)


# update files for last changes
update_erc_20()
