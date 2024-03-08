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
    let* α0 : ref str.t := M.read (mk_str "not implemented") in
    let* α1 : never.t := M.call (core.panicking.panic α0) in
    never_to_any α1.""",
        """Definition init_env : M erc20.Env.t :=
    let* env : erc20.Env.t * ref (list erc20.Event.t) := M.read_env in
    M.pure (fst env)."""
    )

    content = content.replace(
        """Definition emit_event (self : ref Self) (_event : erc20.Event.t) : M unit :=
    let* self := M.alloc self in
    let* _event := M.alloc _event in
    let* α0 : ref str.t := M.read (mk_str "not implemented") in
    let* α1 : never.t := M.call (core.panicking.panic α0) in
    never_to_any α1.""",
        """Definition emit_event
      (self : ref Self)
      (event : erc20.Event.t)
      : M unit :=
    let* env : erc20.Env.t * ref (list erc20.Event.t) := M.read_env in
    let ref_events := snd env in
    let* events := M.read ref_events in
    M.write ref_events (event :: events)."""
    )

    with open(file_name, "w") as f:
        f.write(content)


def update_erc_721():
    file_name = "CoqOfRust/examples/default/examples/ink_contracts/erc721.v"
    with open(file_name, "r") as f:
        content = f.read()

    content = content.replace(
        "Module  Mapping.",
        """Require Import CoqOfRust.examples.default.examples.ink_contracts.Lib.

Module Mapping := Mapping.

(* Module  Mapping. (*""",
    )
    content = content.replace(
        "End Impl_erc721_Mapping_t_K_V.",
        "End Impl_erc721_Mapping_t_K_V. *)",
    )

    with open(file_name, "w") as f:
        f.write(content)


def update_payment_channel():
    file_name = "CoqOfRust/examples/default/examples/ink_contracts/payment_channel.v"
    with open(file_name, "r") as f:
        content = f.read()

    content = content.replace(
        """(output
      :
      mut_ref
        (payment_channel.HashOutput.Type_
          (Self := H)
          (Trait := ltac:(refine _))))""",
        """(output
      :
      mut_ref
        (payment_channel.HashOutput.Type_
          (Self := H)
          (Trait := ltac:(refine ℋ_0.(CryptoHash.ℒ_0)))))""",
    )

    with open(file_name, "w") as f:
        f.write(content)


def update_payment_channel_axiomatized():
    file_name = "CoqOfRust/examples/axiomatized/examples/ink_contracts/payment_channel.v"
    with open(file_name, "r") as f:
        content = f.read()

    content = content.replace(
        """forall {H T : Set} {ℋ_0 : payment_channel.CryptoHash.Trait H},
    (ref T) ->
      (mut_ref
        (payment_channel.HashOutput.Type_
          (Self := H)
          (Trait := ltac:(refine _))))
      ->
      M unit""",
        """forall {H T : Set} {ℋ_0 : payment_channel.CryptoHash.Trait H},
    (ref T) ->
      (mut_ref
        (payment_channel.HashOutput.Type_
          (Self := H)
          (Trait := ℋ_0.(CryptoHash.ℒ_0))))
      ->
      M unit""",
    )

    with open(file_name, "w") as f:
        f.write(content)


# update files for last changes
update_erc_20()
update_erc_721()
update_payment_channel()
update_payment_channel_axiomatized()
