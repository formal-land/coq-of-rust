Error Enum.

Definition inspect :=
  match event with
  | WebEvent.PageLoad =>
    $crate.io._print (new_v1 ["page loaded\n"] []) ;;
    tt
  | WebEvent.PageUnload =>
    $crate.io._print (new_v1 ["page unloaded\n"] []) ;;
    tt
  | WebEvent.KeyPress (c) =>
    $crate.io._print (new_v1 ["pressed '";"'.\n"] [new_display c]) ;;
    tt
  | WebEvent.Paste (s) =>
    $crate.io._print (new_v1 ["pasted \"";"\".\n"] [new_display s]) ;;
    tt
  | WebEvent.Click [x : x,y : y] =>
    $crate.io._print (new_v1 ["clicked at x=";", y=";".\n"] [new_display x;new_display y]) ;;
    tt ;;
    tt
  end.

Definition main :=
  let pressed := WebEvent.KeyPress x in
  let pasted := WebEvent.Paste ("my text" ) in
  let click := struct WebEvent.Click {x := 20;y := 80}  in
  let load := WebEvent.PageLoad in
  let unload := WebEvent.PageUnload in
  inspect pressed ;;
  inspect pasted ;;
  inspect click ;;
  inspect load ;;
  inspect unload ;;
  tt.