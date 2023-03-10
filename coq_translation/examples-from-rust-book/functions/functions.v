(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Import Root.std.prelude.rust_2015.

Definition main (_ : unit) : unit :=
  fizzbuzz_to 100 ;;
  tt.

Definition is_divisible_by (lhs : u32) (rhs : u32) : bool :=
  if (eqb rhs 0 : bool) then
    Return false ;;
    tt
  else
    tt ;;
  eqb (rem lhs rhs) 0.

Definition fizzbuzz (n : u32) :  :=
  if (is_divisible_by n 15 : bool) then
    _crate.io._print (_crate.fmt.ImplArguments.new_v1 [ "fizzbuzz\n" ] [  ]) ;;
    tt ;;
    tt
  else
    if (is_divisible_by n 3 : bool) then
      _crate.io._print (_crate.fmt.ImplArguments.new_v1 [ "fizz\n" ] [  ]) ;;
      tt ;;
      tt
    else
      if (is_divisible_by n 5 : bool) then
        _crate.io._print (_crate.fmt.ImplArguments.new_v1 [ "buzz\n" ] [  ]) ;;
        tt ;;
        tt
      else
        _crate.io._print
          (_crate.fmt.ImplArguments.new_v1
            [ ""; "\n" ]
            [ _crate.fmt.ImplArgumentV1.new_display n ]) ;;
        tt ;;
        tt.

Definition fizzbuzz_to (n : u32) : unit :=
  match into_iter (range_inclusive_new 1 n) with
  | iter =>
    loop
      match next iter with
      | None => Break
      | Some {| Some.0 := n; |} =>
        fizzbuzz n ;;
        tt
      end ;;
      tt
      from
      for
  end.
