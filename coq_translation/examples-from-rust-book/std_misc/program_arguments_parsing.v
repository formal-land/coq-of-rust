(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Import Root.std.prelude.rust_2015.

Module env := std.env.

Definition increase (number : i32) : unit :=
  _crate.io._print
    (_crate.fmt.ImplArguments.new_v1
      [ ""; "\n" ]
      [ _crate.fmt.ImplArgumentV1.new_display (add number 1) ]) ;;
  tt ;;
  tt.

Definition decrease (number : i32) : unit :=
  _crate.io._print
    (_crate.fmt.ImplArguments.new_v1
      [ ""; "\n" ]
      [ _crate.fmt.ImplArgumentV1.new_display (sub number 1) ]) ;;
  tt ;;
  tt.

Definition help (_ : unit) : unit :=
  _crate.io._print
    (_crate.fmt.ImplArguments.new_v1
      [
        "usage:\nmatch_args <string>\n    Check whether given string is the answer.\nmatch_args {increase|decrease} <integer>\n    Increase or decrease given integer by one.\n"
      ]
      [  ]) ;;
  tt ;;
  tt.

Definition main (_ : unit) : unit :=
  let args := method "collect" (env.args tt) in
  match method "len" args with
  | Int(1, Unsuffixed) =>
    _crate.io._print
      (_crate.fmt.ImplArguments.new_v1
        [ "My name is 'match_args'. Try passing some arguments!\n" ]
        [  ]) ;;
    tt ;;
    tt
  | Int(2, Unsuffixed) =>
    match method "parse" args[1] with
    | Ok (Int(42, Unsuffixed)) =>
      _crate.io._print
        (_crate.fmt.ImplArguments.new_v1 [ "This is the answer!\n" ] [  ]) ;;
      tt
    | _ =>
      _crate.io._print
        (_crate.fmt.ImplArguments.new_v1
          [ "This is not the answer.\n" ]
          [  ]) ;;
      tt
    end
  | Int(3, Unsuffixed) =>
    let cmd := args[1] in
    let num := args[2] in
    let number :=
      match method "parse" num with
      | Ok (n) => n
      | Err (_) =>
        _crate.io._eprint
          (_crate.fmt.ImplArguments.new_v1
            [ "error: second argument not an integer\n" ]
            [  ]) ;;
        tt ;;
        help tt ;;
        Return tt ;;
        tt
      end in
    match cmd[{|  |}] with
    | Str("increase", Cooked) => increase number
    | Str("decrease", Cooked) => decrease number
    | _ =>
      _crate.io._eprint
        (_crate.fmt.ImplArguments.new_v1 [ "error: invalid command\n" ] [  ]) ;;
      tt ;;
      help tt ;;
      tt
    end
  | _ =>
    help tt ;;
    tt
  end.
