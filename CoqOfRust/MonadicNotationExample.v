Require Import CoqOfRust.CoqOfRust.

(* An example of the new monadic notation *)
Module MonadicNotationExample.

  (* Example of a Rust program *)
  (*
    fn test() -> u32 {
      let x = 5u32;

      let y = {
        let x_squared = x * x;
        let x_cube = x_squared * x;
        x_cube + x_squared + x
      };

      y + 2
    }
  *)

  (* Translation result with explicit names for intermediate results *)
  Definition test : M u32.t :=
    let* x : M.Val u32.t := M.alloc ((Integer.of_Z 5) : u32.t) in
    let* y : M.Val u32.t :=
      let* x_squared : M.Val u32.t :=
        let* α0 : u32.t := M.read x in
        let* α1 : u32.t := M.read x in
        let* α2 : u32.t := BinOp.Panic.mul α0 α1 in
        M.alloc α2 in
      let* x_cube : M.Val u32.t :=
        let* α0 : u32.t := M.read x_squared in
        let* α1 : u32.t := M.read x in
        let* α2 : u32.t := BinOp.Panic.mul α0 α1 in
        M.alloc α2 in
      let* α0 : u32.t := M.read x_cube in
      let* α1 : u32.t := M.read x_squared in
      let* α2 : u32.t := BinOp.Panic.add α0 α1 in
      let* α3 : u32.t := M.read x in
      let* α4 : u32.t := BinOp.Panic.add α2 α3 in
      let* α0 : M.Val u32.t := M.alloc α4 in
      M.copy α0 in
    let* α0 : u32.t := M.read y in
    let* α1 : u32.t := BinOp.Panic.add α0 ((Integer.of_Z 2) : u32.t) in
    let* α0 : M.Val u32.t := M.alloc α1 in
    M.read α0.

  (* Representation without explicit names for intermediate results
     using [M.run] markers and [M.monadic] tactic *)
  Definition test_new : M u32.t :=
    ltac:(monadic (
      M.read (|
        let x : M.Val u32.t := M.alloc (| (Integer.of_Z 5) : u32.t |) in
        let y : M.Val u32.t :=
          M.copy (|
            let x_squared : M.Val u32.t :=
              M.alloc (| BinOp.Panic.mul (| M.read (| x |), M.read (| x |) |)
              |) in
            let x_cube : M.Val u32.t :=
              M.alloc (|
                BinOp.Panic.mul (| M.read (| x_squared |), M.read (| x |) |)
              |) in
            M.alloc (|
              BinOp.Panic.add (|
                BinOp.Panic.add (| M.read (| x_cube |), M.read (| x_squared |) |),
                M.read (| x |)
              |)
            |)
          |) in
        M.alloc (| BinOp.Panic.add (| M.read (| y |), (Integer.of_Z 2) : u32.t |)
        |)
      |)
    )).

  (* Run to see the transltion result *)
  (* Print test_new. *)

End MonadicNotationExample.