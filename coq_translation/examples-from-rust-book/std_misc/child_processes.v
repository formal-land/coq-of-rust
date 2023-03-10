(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Import Root.std.prelude.rust_2015.

Module Command := std.process.Command.
Definition Command := Command.t.

Definition main (_ : unit) : unit :=
  let output :=
    method
      "unwrap_or_else"
      (method "output" (method "arg" (ImplCommand.new "rustc") "--version"))
      (fun e =>
        _crate.rt.panic_fmt
          (_crate.fmt.ImplArguments.new_v1
            [ "failed to execute process: " ]
            [ _crate.fmt.ImplArgumentV1.new_display e ])) in
  if (method "success" (NamedField.get (name := "status") output) : bool) then
    let s :=
      ImplString.from_utf8_lossy (NamedField.get (name := "stdout") output) in
    _crate.io._print
      (_crate.fmt.ImplArguments.new_v1
        [ "rustc succeeded and stdout was:\n" ]
        [ _crate.fmt.ImplArgumentV1.new_display s ]) ;;
    tt ;;
    tt
  else
    let s :=
      ImplString.from_utf8_lossy (NamedField.get (name := "stderr") output) in
    _crate.io._print
      (_crate.fmt.ImplArguments.new_v1
        [ "rustc failed and stderr was:\n" ]
        [ _crate.fmt.ImplArgumentV1.new_display s ]) ;;
    tt ;;
    tt.
