Definition analyze_slice :=
  _crate.io._print (new_v1 ["first element of the slice: ";"\n"] [new_display slice[0]]) ;;
  tt ;;
  _crate.io._print (new_v1 ["the slice has ";" elements\n"] [new_display (slice )]) ;;
  tt ;;
  tt.

Definition main :=
  let xs := [1;2;3;4;5] in
  let ys := repeat 0 in
  _crate.io._print (new_v1 ["first element of the array: ";"\n"] [new_display xs[0]]) ;;
  tt ;;
  _crate.io._print (new_v1 ["second element of the array: ";"\n"] [new_display xs[1]]) ;;
  tt ;;
  _crate.io._print (new_v1 ["number of elements in array: ";"\n"] [new_display (xs )]) ;;
  tt ;;
  _crate.io._print (new_v1 ["array occupies ";" bytes\n"] [new_display (mem.size_of_val xs)]) ;;
  tt ;;
  _crate.io._print (new_v1 ["borrow the whole array as a slice\n"] []) ;;
  tt ;;
  analyze_slice xs ;;
  _crate.io._print (new_v1 ["borrow a section of the array as a slice\n"] []) ;;
  tt ;;
  analyze_slice ys[struct Range {start := 1;end := 4} ] ;;
  let empty_array := [] in
  match (empty_array, []) with
  | (left_val, right_val) =>
    if not (eq (deref left_val) (deref right_val)) then
      let kind := _crate.panicking.AssertKind.Eq in
      _crate.panicking.assert_failed kind (deref left_val) (deref right_val) _crate.option.Option.None ;;
      tt
    else
      tt
  end ;;
  match (empty_array, [][struct RangeFull {} ]) with
  | (left_val, right_val) =>
    if not (eq (deref left_val) (deref right_val)) then
      let kind := _crate.panicking.AssertKind.Eq in
      _crate.panicking.assert_failed kind (deref left_val) (deref right_val) _crate.option.Option.None ;;
      tt
    else
      tt
  end ;;
  match into_iter (struct Range {start := 0;end := add (xs ) 1} ) with
  | iter =>
    loop match next iter with
    | None [] => Break
    | Some [0 : i] =>
      match xs i with
      | Some (xval) =>
        _crate.io._print (new_v1 ["";": ";"\n"] [new_display i;new_display xval]) ;;
        tt
      | None =>
        _crate.io._print (new_v1 ["Slow down! ";" is too far!\n"] [new_display i]) ;;
        tt
      end
    end ;;
    tt from for
  end.