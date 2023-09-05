(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Module WebEvent.
  Module Click.
    Unset Primitive Projections.
    Record t : Set := {
      x : i64;
      y : i64;
    }.
    Global Set Primitive Projections.
  End Click.
  
  Inductive t : Set :=
  | PageLoad
  | PageUnload
  | KeyPress (_ : char)
  | Paste (_ : alloc.string.String)
  | Click (_ : Click.t).
End WebEvent.
Definition WebEvent := WebEvent.t.

Definition inspect
    `{H' : State.Trait}
    (event : enums.WebEvent)
    : M (H := H') unit :=
  match event with
  | enums.WebEvent.PageLoad =>
    let* _ :=
      let* α0 :=
        format_arguments::["new_const"]
          (addr_of
            [
              "page loaded, r" ++
                String.String "233" ("f" ++ String.String "233" "
")
            ]) in
      std.io.stdio._print α0 in
    Pure tt
  | enums.WebEvent.PageUnload =>
    let* _ :=
      let* α0 :=
        format_arguments::["new_const"] (addr_of [ "page unloaded
" ]) in
      std.io.stdio._print α0 in
    Pure tt
  | enums.WebEvent.KeyPress c =>
    let* _ :=
      let* α0 := format_argument::["new_display"] (addr_of c) in
      let* α1 :=
        format_arguments::["new_v1"]
          (addr_of [ "pressed '"; "'.
" ])
          (addr_of [ α0 ]) in
      std.io.stdio._print α1 in
    Pure tt
  | enums.WebEvent.Paste s =>
    let* _ :=
      let* α0 := format_argument::["new_display"] (addr_of s) in
      let* α1 :=
        format_arguments::["new_v1"]
          (addr_of [ "pasted ""; "".
" ])
          (addr_of [ α0 ]) in
      std.io.stdio._print α1 in
    Pure tt
  |
      enums.WebEvent.Click
      {| enums.WebEvent.Click.x := x; enums.WebEvent.Click.y := y;
      |}
      =>
    let* _ :=
      let* _ :=
        let* α0 := format_argument::["new_display"] (addr_of x) in
        let* α1 := format_argument::["new_display"] (addr_of y) in
        let* α2 :=
          format_arguments::["new_v1"]
            (addr_of [ "clicked at x="; ", y="; ".
" ])
            (addr_of [ α0; α1 ]) in
        std.io.stdio._print α2 in
      Pure tt in
    Pure tt
  end.

(* #[allow(dead_code)] - function was ignored by the compiler *)
Definition main `{H' : State.Trait} : M (H := H') unit :=
  let pressed := enums.WebEvent.KeyPress "x"%char in
  let* pasted :=
    let* α0 := "my text".["to_owned"] in
    Pure (enums.WebEvent.Paste α0) in
  let click :=
    enums.WebEvent.Click
      {|
      enums.WebEvent.Click.x := 20;
      enums.WebEvent.Click.y := 80;
    |} in
  let load := enums.WebEvent.PageLoad in
  let unload := enums.WebEvent.PageUnload in
  let* _ := enums.inspect pressed in
  let* _ := enums.inspect pasted in
  let* _ := enums.inspect click in
  let* _ := enums.inspect load in
  let* _ := enums.inspect unload in
  Pure tt.