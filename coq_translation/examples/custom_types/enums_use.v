(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Module Status.
  Inductive t : Set :=
  | Rich
  | Poor.
End Status.
Definition Status := Status.t.

Module Work.
  Inductive t : Set :=
  | Civilian
  | Soldier.
End Work.
Definition Work := Work.t.

(* #[allow(dead_code)] - function was ignored by the compiler *)
Definition main `{H' : State.Trait} : M (H := H') unit :=
  let status := enums_use.Status.Poor in
  let work := enums_use.Work.Civilian in
  let* _ :=
    match status with
    | enums_use.Status.Rich =>
      let* _ :=
        let* α0 :=
          format_arguments::["new_const"]
            (addr_of [ "The rich have lots of money!
" ]) in
        std.io.stdio._print α0 in
      Pure tt
    | enums_use.Status.Poor =>
      let* _ :=
        let* α0 :=
          format_arguments::["new_const"]
            (addr_of [ "The poor have no money...
" ]) in
        std.io.stdio._print α0 in
      Pure tt
    end in
  match work with
  | enums_use.Work.Civilian =>
    let* _ :=
      let* α0 :=
        format_arguments::["new_const"] (addr_of [ "Civilians work!
" ]) in
      std.io.stdio._print α0 in
    Pure tt
  | enums_use.Work.Soldier =>
    let* _ :=
      let* α0 :=
        format_arguments::["new_const"] (addr_of [ "Soldiers fight!
" ]) in
      std.io.stdio._print α0 in
    Pure tt
  end.