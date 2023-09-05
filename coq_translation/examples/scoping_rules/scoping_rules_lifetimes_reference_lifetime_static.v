(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Definition NUM `{H' : State.Trait} : i32 := run (Pure 18).

Definition coerce_static
    `{H' : State.Trait}
    (arg : ref i32)
    : M (H := H') (ref i32) :=
  Pure (addr_of scoping_rules_lifetimes_reference_lifetime_static.NUM).

(* #[allow(dead_code)] - function was ignored by the compiler *)
Definition main `{H' : State.Trait} : M (H := H') unit :=
  let* _ :=
    let static_string := "I'm in read-only memory" in
    let* _ :=
      let* _ :=
        let* α0 := format_argument::["new_display"] (addr_of static_string) in
        let* α1 :=
          format_arguments::["new_v1"]
            (addr_of [ "static_string: "; "
" ])
            (addr_of [ α0 ]) in
        std.io.stdio._print α1 in
      Pure tt in
    Pure tt in
  let* _ :=
    let lifetime_num := 9 in
    let* coerced_static :=
      scoping_rules_lifetimes_reference_lifetime_static.coerce_static
        (addr_of lifetime_num) in
    let* _ :=
      let* _ :=
        let* α0 := format_argument::["new_display"] (addr_of coerced_static) in
        let* α1 :=
          format_arguments::["new_v1"]
            (addr_of [ "coerced_static: "; "
" ])
            (addr_of [ α0 ]) in
        std.io.stdio._print α1 in
      Pure tt in
    Pure tt in
  let* _ :=
    let* _ :=
      let* α0 :=
        format_argument::["new_display"]
          (addr_of scoping_rules_lifetimes_reference_lifetime_static.NUM) in
      let* α1 :=
        format_arguments::["new_v1"]
          (addr_of [ "NUM: "; " stays accessible!
" ])
          (addr_of [ α0 ]) in
      std.io.stdio._print α1 in
    Pure tt in
  Pure tt.