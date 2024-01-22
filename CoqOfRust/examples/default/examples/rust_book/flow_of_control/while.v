(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

(*
fn main() {
    // A counter variable
    let mut n = 1;

    // Loop while `n` is less than 101
    while n < 101 {
        if n % 15 == 0 {
            println!("fizzbuzz");
        } else if n % 3 == 0 {
            println!("fizz");
        } else if n % 5 == 0 {
            println!("buzz");
        } else {
            println!("{}", n);
        }

        // Increment counter
        n += 1;
    }
}
*)
(* #[allow(dead_code)] - function was ignored by the compiler *)
Definition main : M unit :=
  let* n : M.Val i32.t := M.alloc ((Integer.of_Z 1) : i32.t) in
  let* α0 : M.Val unit :=
    M.loop
      (let* α0 : i32.t := M.read n in
      let* α1 : M.Val bool.t :=
        M.alloc (BinOp.Pure.lt α0 ((Integer.of_Z 101) : i32.t)) in
      let* α2 : bool.t := M.read (use α1) in
      if α2 then
        let* _ : M.Val unit :=
          let* α0 : i32.t := M.read n in
          let* α1 : i32.t := BinOp.Panic.rem α0 ((Integer.of_Z 15) : i32.t) in
          let* α2 : M.Val bool.t :=
            M.alloc (BinOp.Pure.eq α1 ((Integer.of_Z 0) : i32.t)) in
          let* α3 : bool.t := M.read (use α2) in
          if α3 then
            let* _ : M.Val unit :=
              let* _ : M.Val unit :=
                let* α0 : ref str.t := M.read (mk_str "fizzbuzz
") in
                let* α1 : M.Val (array (ref str.t)) := M.alloc [ α0 ] in
                let* α2 : core.fmt.Arguments.t :=
                  M.call
                    (core.fmt.Arguments.t::["new_const"]
                      (pointer_coercion "Unsize" (borrow α1))) in
                let* α3 : unit := M.call (std.io.stdio._print α2) in
                M.alloc α3 in
              M.alloc tt in
            M.alloc tt
          else
            let* α0 : i32.t := M.read n in
            let* α1 : i32.t := BinOp.Panic.rem α0 ((Integer.of_Z 3) : i32.t) in
            let* α2 : M.Val bool.t :=
              M.alloc (BinOp.Pure.eq α1 ((Integer.of_Z 0) : i32.t)) in
            let* α3 : bool.t := M.read (use α2) in
            if α3 then
              let* _ : M.Val unit :=
                let* _ : M.Val unit :=
                  let* α0 : ref str.t := M.read (mk_str "fizz
") in
                  let* α1 : M.Val (array (ref str.t)) := M.alloc [ α0 ] in
                  let* α2 : core.fmt.Arguments.t :=
                    M.call
                      (core.fmt.Arguments.t::["new_const"]
                        (pointer_coercion "Unsize" (borrow α1))) in
                  let* α3 : unit := M.call (std.io.stdio._print α2) in
                  M.alloc α3 in
                M.alloc tt in
              M.alloc tt
            else
              let* α0 : i32.t := M.read n in
              let* α1 : i32.t :=
                BinOp.Panic.rem α0 ((Integer.of_Z 5) : i32.t) in
              let* α2 : M.Val bool.t :=
                M.alloc (BinOp.Pure.eq α1 ((Integer.of_Z 0) : i32.t)) in
              let* α3 : bool.t := M.read (use α2) in
              if α3 then
                let* _ : M.Val unit :=
                  let* _ : M.Val unit :=
                    let* α0 : ref str.t := M.read (mk_str "buzz
") in
                    let* α1 : M.Val (array (ref str.t)) := M.alloc [ α0 ] in
                    let* α2 : core.fmt.Arguments.t :=
                      M.call
                        (core.fmt.Arguments.t::["new_const"]
                          (pointer_coercion "Unsize" (borrow α1))) in
                    let* α3 : unit := M.call (std.io.stdio._print α2) in
                    M.alloc α3 in
                  M.alloc tt in
                M.alloc tt
              else
                let* _ : M.Val unit :=
                  let* _ : M.Val unit :=
                    let* α0 : ref str.t := M.read (mk_str "") in
                    let* α1 : ref str.t := M.read (mk_str "
") in
                    let* α2 : M.Val (array (ref str.t)) := M.alloc [ α0; α1 ] in
                    let* α3 : core.fmt.rt.Argument.t :=
                      M.call
                        (core.fmt.rt.Argument.t::["new_display"] (borrow n)) in
                    let* α4 : M.Val (array core.fmt.rt.Argument.t) :=
                      M.alloc [ α3 ] in
                    let* α5 : core.fmt.Arguments.t :=
                      M.call
                        (core.fmt.Arguments.t::["new_v1"]
                          (pointer_coercion "Unsize" (borrow α2))
                          (pointer_coercion "Unsize" (borrow α4))) in
                    let* α6 : unit := M.call (std.io.stdio._print α5) in
                    M.alloc α6 in
                  M.alloc tt in
                M.alloc tt in
        let* _ : M.Val unit :=
          let β : M.Val i32.t := n in
          let* α0 := M.read β in
          let* α1 := BinOp.Panic.add α0 ((Integer.of_Z 1) : i32.t) in
          assign β α1 in
        M.alloc tt
      else
        let* _ : M.Val unit :=
          let* α0 : M.Val never.t := M.break in
          let* α1 := M.read α0 in
          let* α2 : unit := never_to_any α1 in
          M.alloc α2 in
        let* α0 : M.Val unit := M.alloc tt in
        let* α1 := M.read α0 in
        let* α2 : unit := never_to_any α1 in
        M.alloc α2) in
  M.read α0.