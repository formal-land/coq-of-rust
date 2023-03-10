(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Import Root.std.prelude.rust_2015.

Definition main (_ : unit) : unit :=
  _crate.io._print
    (_crate.fmt.ImplArguments.new_v1
      [ "1 + 2 = "; "\n" ]
      [ _crate.fmt.ImplArgumentV1.new_display (add 1 2) ]) ;;
  tt ;;
  _crate.io._print
    (_crate.fmt.ImplArguments.new_v1
      [ "1 - 2 = "; "\n" ]
      [ _crate.fmt.ImplArgumentV1.new_display (sub 1 2) ]) ;;
  tt ;;
  _crate.io._print
    (_crate.fmt.ImplArguments.new_v1
      [ "true AND false is "; "\n" ]
      [ _crate.fmt.ImplArgumentV1.new_display (andb true false) ]) ;;
  tt ;;
  _crate.io._print
    (_crate.fmt.ImplArguments.new_v1
      [ "true OR false is "; "\n" ]
      [ _crate.fmt.ImplArgumentV1.new_display (or true false) ]) ;;
  tt ;;
  _crate.io._print
    (_crate.fmt.ImplArguments.new_v1
      [ "NOT true is "; "\n" ]
      [ _crate.fmt.ImplArgumentV1.new_display (not true) ]) ;;
  tt ;;
  _crate.io._print
    (_crate.fmt.ImplArguments.new_v1_formatted
      [ "0011 AND 0101 is "; "\n" ]
      [ _crate.fmt.ImplArgumentV1.new_binary (bit_and 3 5) ]
      [
        {|
          _crate.fmt.rt.v1.Argument.position := 0;
          _crate.fmt.rt.v1.Argument.format :=
            {|
              _crate.fmt.rt.v1.FormatSpec.fill :=  ;
              _crate.fmt.rt.v1.FormatSpec.align :=
                _crate.fmt.rt.v1.Alignment.Unknown;
              _crate.fmt.rt.v1.FormatSpec.flags := 8;
              _crate.fmt.rt.v1.FormatSpec.precision :=
                _crate.fmt.rt.v1.Count.Implied;
              _crate.fmt.rt.v1.FormatSpec.width := _crate.fmt.rt.v1.Count.Is 4;
            |};
        |}
      ]
      (_crate.fmt.ImplUnsafeArg.new tt)) ;;
  tt ;;
  _crate.io._print
    (_crate.fmt.ImplArguments.new_v1_formatted
      [ "0011 OR 0101 is "; "\n" ]
      [ _crate.fmt.ImplArgumentV1.new_binary (bit_or 3 5) ]
      [
        {|
          _crate.fmt.rt.v1.Argument.position := 0;
          _crate.fmt.rt.v1.Argument.format :=
            {|
              _crate.fmt.rt.v1.FormatSpec.fill :=  ;
              _crate.fmt.rt.v1.FormatSpec.align :=
                _crate.fmt.rt.v1.Alignment.Unknown;
              _crate.fmt.rt.v1.FormatSpec.flags := 8;
              _crate.fmt.rt.v1.FormatSpec.precision :=
                _crate.fmt.rt.v1.Count.Implied;
              _crate.fmt.rt.v1.FormatSpec.width := _crate.fmt.rt.v1.Count.Is 4;
            |};
        |}
      ]
      (_crate.fmt.ImplUnsafeArg.new tt)) ;;
  tt ;;
  _crate.io._print
    (_crate.fmt.ImplArguments.new_v1_formatted
      [ "0011 XOR 0101 is "; "\n" ]
      [ _crate.fmt.ImplArgumentV1.new_binary (bit_xor 3 5) ]
      [
        {|
          _crate.fmt.rt.v1.Argument.position := 0;
          _crate.fmt.rt.v1.Argument.format :=
            {|
              _crate.fmt.rt.v1.FormatSpec.fill :=  ;
              _crate.fmt.rt.v1.FormatSpec.align :=
                _crate.fmt.rt.v1.Alignment.Unknown;
              _crate.fmt.rt.v1.FormatSpec.flags := 8;
              _crate.fmt.rt.v1.FormatSpec.precision :=
                _crate.fmt.rt.v1.Count.Implied;
              _crate.fmt.rt.v1.FormatSpec.width := _crate.fmt.rt.v1.Count.Is 4;
            |};
        |}
      ]
      (_crate.fmt.ImplUnsafeArg.new tt)) ;;
  tt ;;
  _crate.io._print
    (_crate.fmt.ImplArguments.new_v1
      [ "1 << 5 is "; "\n" ]
      [ _crate.fmt.ImplArgumentV1.new_display (shl 1 5) ]) ;;
  tt ;;
  _crate.io._print
    (_crate.fmt.ImplArguments.new_v1
      [ "0x80 >> 2 is 0x"; "\n" ]
      [ _crate.fmt.ImplArgumentV1.new_lower_hex (shr 128 2) ]) ;;
  tt ;;
  _crate.io._print
    (_crate.fmt.ImplArguments.new_v1
      [ "One million is written as "; "\n" ]
      [ _crate.fmt.ImplArgumentV1.new_display 1000000 ]) ;;
  tt ;;
  tt.
