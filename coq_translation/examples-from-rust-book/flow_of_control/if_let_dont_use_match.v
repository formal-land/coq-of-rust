(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Import Root.std.prelude.rust_2015.

Definition main (_ : unit) : unit :=
  let optional := Some 7 in
  match optional with
  | Some (i) =>
    _crate.io._print
      (_crate.fmt.ImplArguments.new_v1
        [ "This is a really long string and `"; "`\n" ]
        [ _crate.fmt.ImplArgumentV1.new_debug i ]) ;;
    tt ;;
    tt
  | _ => tt
  end ;;
  tt.
