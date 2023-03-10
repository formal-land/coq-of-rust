(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Import Root.std.prelude.rust_2015.

Module File := std.fs.File.
Definition File := File.t.

Module io := std.io.

Module BufRead := std.io.BufRead.

Module Path := std.path.Path.
Definition Path := Path.t.

Definition main (_ : unit) : unit :=
  if (let_if Ok (lines) := read_lines "./hosts" : bool) then
    match into_iter lines with
    | iter =>
      loop
        match next iter with
        | None => Break
        | Some {| Some.0 := line; |} =>
          if (let_if Ok (ip) := line : bool) then
            _crate.io._print
              (_crate.fmt.ImplArguments.new_v1
                [ ""; "\n" ]
                [ _crate.fmt.ImplArgumentV1.new_display ip ]) ;;
            tt ;;
            tt
          else
            tt
        end ;;
        tt
        from
        for
    end
  else
    tt.

Definition read_lines
    {P : Set}
    `{AsRef.Class Path P}
    (filename : P)
    : io.Result :=
  let file :=
    match branch (ImplFile.open filename) with
    | Break {| Break.0 := residual; |} => Return (from_residual residual)
    | Continue {| Continue.0 := val; |} => val
    end in
  Ok (method "lines" (io.ImplBufReader.new file)).
