(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Import Root.std.prelude.rust_2015.

Definition main (_ : unit) : unit :=
  let raw_str := "Escapes don't work here: \\x3F \\u{211D}" in
  _crate.io._print
    (_crate.fmt.ImplArguments.new_v1
      [ ""; "\n" ]
      [ _crate.fmt.ImplArgumentV1.new_display raw_str ]) ;;
  tt ;;
  let quotes := "And then I said: \"There is no escape!\"" in
  _crate.io._print
    (_crate.fmt.ImplArguments.new_v1
      [ ""; "\n" ]
      [ _crate.fmt.ImplArgumentV1.new_display quotes ]) ;;
  tt ;;
  let longer_delimiter := "A string with \"# in it. And even \"##!" in
  _crate.io._print
    (_crate.fmt.ImplArguments.new_v1
      [ ""; "\n" ]
      [ _crate.fmt.ImplArgumentV1.new_display longer_delimiter ]) ;;
  tt ;;
  tt.
