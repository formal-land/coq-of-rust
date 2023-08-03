"""
In this file we apply a list of manual updates to the translated Rust files.
"""
import re


def sub_exactly_n(pattern, replacement, text, times) -> str:
    regex_flags = re.MULTILINE | re.DOTALL
    matches = list(re.finditer(pattern, text, regex_flags))
    if len(matches) == times:
        return re.sub(
            pattern=pattern,
            repl=replacement,
            string=text,
            flags=regex_flags,
        )
    else:
        raise ValueError(
            f"Pattern {pattern} not found exactly {times} times in text")


def sub_exactly_once(pattern, replacement, text) -> str:
    return sub_exactly_n(pattern, replacement, text, 1)


def update_ink_primitives():
    file_name = "ink_primitives.v"
    with open(file_name, "r") as f:
        content = f.read()
    content = \
        sub_exactly_once(
            r"Definition Hash := @Hash\.t\.\n\nModule Visitor\..*Definition Visitor := @Visitor\.t\.",
            "Definition Hash := @Hash.t.",
            content,
        )
    content = \
        sub_exactly_once(
            "Definition MessageResult",
            "Definition MessageResult (T : Set)",
            content,
        )
    content = \
        sub_exactly_once(
            "Definition ConstructorResult",
            "Definition ConstructorResult (T : Set)",
            content,
        )
    with open(file_name, "w") as f:
        f.write(content)


def update_storage():
    file_name = "ink_storage.v"
    with open(file_name, "r") as f:
        content = f.read()
    content = \
        sub_exactly_n(
            ": Set := @",
            ":= @",
            content,
            5,
        )
    with open(file_name, "w") as f:
        f.write(content)


def update_storage_traits():
    file_name = "ink_storage_traits.v"
    with open(file_name, "r") as f:
        content = f.read()
    pattern = "Require Import CoqOfRust.CoqOfRust."
    content = \
        sub_exactly_once(
            pattern,
            pattern + """
Require CoqOfRust.ink.ink_metadata.
Require CoqOfRust.ink.ink_primitives.
Require CoqOfRust.ink.parity_scale_codec.""",
            content,
        )
    content = \
        sub_exactly_n(
            "Global Instance Method_key",
            "(* Global Instance Method_key",
            content,
            2,
        )
    content = \
        sub_exactly_n(
            "End StorageKey.",
            "*) End StorageKey.",
            content,
            2,
        )
    with open(file_name, "w") as f:
        f.write(content)


update_ink_primitives()
update_storage()
update_storage_traits()
