(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

(* #[allow(dead_code)] - function was ignored by the compiler *)
Definition main `{H' : State.Trait} : M (H := H') unit :=
  let* _ :=
    let* _ :=
      let* α0 :=
        diverging_functions_example_sum_odd_numbers.main.sum_odd_numbers 9 in
      let* α1 := format_argument::["new_display"] (addr_of α0) in
      let* α2 :=
        format_arguments::["new_v1"]
          (addr_of [ "Sum of odd numbers up to 9 (excluding): "; "
" ])
          (addr_of [ α1 ]) in
      std.io.stdio._print α2 in
    Pure tt in
  Pure tt.

Definition sum_odd_numbers
    `{H' : State.Trait}
    (up_to : u32)
    : M (H := H') u32 :=
  let acc := 0 in
  let* _ :=
    let* α0 :=
      {| std.ops.Range.start := 0; std.ops.Range._end := up_to;
        |}.["into_iter"] in
    match α0 with
    | iter =>
      loop
        (let* _ :=
          let* α0 := (addr_of iter).["next"] in
          match α0 with
          | core.option.Option.None  => Break
          | core.option.Option.Some i =>
            let* addition :=
              let* α0 := i.["rem"] 2 in
              let* α1 := α0.["eq"] 1 in
              match α1 with
              | true => Pure i
              | false => Continue
              end in
            let* _ := acc.["add_assign"] addition in
            Pure tt
          end in
        Pure tt)
    end in
  Pure acc.