Definition main :=
  $crate.io._print (new_v1 ["1 + 2 = ";"\n"] [new_display (add 1 2)]) ;;
  tt ;;
  $crate.io._print (new_v1 ["1 - 2 = ";"\n"] [new_display (sub 1 2)]) ;;
  tt ;;
  $crate.io._print (new_v1 ["true AND false is ";"\n"] [new_display (Binary true false)]) ;;
  tt ;;
  $crate.io._print (new_v1 ["true OR false is ";"\n"] [new_display (Binary true false)]) ;;
  tt ;;
  $crate.io._print (new_v1 ["NOT true is ";"\n"] [new_display (unary true)]) ;;
  tt ;;
  $crate.io._print (new_v1_formatted ["0011 AND 0101 is ";"\n"] [new_binary (Binary 3 5)] [struct $crate.fmt.rt.v1.Argument {position := 0;format := struct $crate.fmt.rt.v1.FormatSpec {fill :=  ;align := $crate.fmt.rt.v1.Alignment.Unknown;flags := 8;precision := $crate.fmt.rt.v1.Count.Implied;width := $crate.fmt.rt.v1.Count.Is 4} } ] (new )) ;;
  tt ;;
  $crate.io._print (new_v1_formatted ["0011 OR 0101 is ";"\n"] [new_binary (Binary 3 5)] [struct $crate.fmt.rt.v1.Argument {position := 0;format := struct $crate.fmt.rt.v1.FormatSpec {fill :=  ;align := $crate.fmt.rt.v1.Alignment.Unknown;flags := 8;precision := $crate.fmt.rt.v1.Count.Implied;width := $crate.fmt.rt.v1.Count.Is 4} } ] (new )) ;;
  tt ;;
  $crate.io._print (new_v1_formatted ["0011 XOR 0101 is ";"\n"] [new_binary (Binary 3 5)] [struct $crate.fmt.rt.v1.Argument {position := 0;format := struct $crate.fmt.rt.v1.FormatSpec {fill :=  ;align := $crate.fmt.rt.v1.Alignment.Unknown;flags := 8;precision := $crate.fmt.rt.v1.Count.Implied;width := $crate.fmt.rt.v1.Count.Is 4} } ] (new )) ;;
  tt ;;
  $crate.io._print (new_v1 ["1 << 5 is ";"\n"] [new_display (Binary 1 5)]) ;;
  tt ;;
  $crate.io._print (new_v1 ["0x80 >> 2 is 0x";"\n"] [new_lower_hex (Binary 128 2)]) ;;
  tt ;;
  $crate.io._print (new_v1 ["One million is written as ";"\n"] [new_display 1000000]) ;;
  tt ;;
  tt.