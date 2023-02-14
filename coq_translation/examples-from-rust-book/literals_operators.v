Definition main :=
  _crate.io._print (new_v1 ["1 + 2 = ";"\n"] [new_display (add 1 2)]) ;;
  tt ;;
  _crate.io._print (new_v1 ["1 - 2 = ";"\n"] [new_display (sub 1 2)]) ;;
  tt ;;
  _crate.io._print (new_v1 ["true AND false is ";"\n"] [new_display (and true false)]) ;;
  tt ;;
  _crate.io._print (new_v1 ["true OR false is ";"\n"] [new_display (or true false)]) ;;
  tt ;;
  _crate.io._print (new_v1 ["NOT true is ";"\n"] [new_display (not true)]) ;;
  tt ;;
  _crate.io._print (new_v1_formatted ["0011 AND 0101 is ";"\n"] [new_binary (bit_and 3 5)] [struct _crate.fmt.rt.v1.Argument {position := 0;format := struct _crate.fmt.rt.v1.FormatSpec {fill :=  ;align := _crate.fmt.rt.v1.Alignment.Unknown;flags := 8;precision := _crate.fmt.rt.v1.Count.Implied;width := _crate.fmt.rt.v1.Count.Is 4} } ] (new )) ;;
  tt ;;
  _crate.io._print (new_v1_formatted ["0011 OR 0101 is ";"\n"] [new_binary (bit_and 3 5)] [struct _crate.fmt.rt.v1.Argument {position := 0;format := struct _crate.fmt.rt.v1.FormatSpec {fill :=  ;align := _crate.fmt.rt.v1.Alignment.Unknown;flags := 8;precision := _crate.fmt.rt.v1.Count.Implied;width := _crate.fmt.rt.v1.Count.Is 4} } ] (new )) ;;
  tt ;;
  _crate.io._print (new_v1_formatted ["0011 XOR 0101 is ";"\n"] [new_binary (bit_xor 3 5)] [struct _crate.fmt.rt.v1.Argument {position := 0;format := struct _crate.fmt.rt.v1.FormatSpec {fill :=  ;align := _crate.fmt.rt.v1.Alignment.Unknown;flags := 8;precision := _crate.fmt.rt.v1.Count.Implied;width := _crate.fmt.rt.v1.Count.Is 4} } ] (new )) ;;
  tt ;;
  _crate.io._print (new_v1 ["1 << 5 is ";"\n"] [new_display (shl 1 5)]) ;;
  tt ;;
  _crate.io._print (new_v1 ["0x80 >> 2 is 0x";"\n"] [new_lower_hex (shr 128 2)]) ;;
  tt ;;
  _crate.io._print (new_v1 ["One million is written as ";"\n"] [new_display 1000000]) ;;
  tt ;;
  tt.