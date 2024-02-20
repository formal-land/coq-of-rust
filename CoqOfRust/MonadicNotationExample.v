Require Import CoqOfRust.CoqOfRust.

(* An example of the new monadic notation *)
Module MonadicNotationExample.

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
  Definition test : M u32.t :=
    ltac:(M.monadic (
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

  (*
  fn test_match(x: u32, boolean: bool) -> u32 {
      let y = match x {
          1 => 2,
          3 => 6,
          5 => 10,
          7 => 14,
          _ => 0,
      };

      let binary = match boolean {
          false => 0,
          true => 1,
      };

      x + y * binary
  }
  *)
  Definition test_match (x : u32.t) (boolean : bool.t) : M u32.t :=
    ltac:(M.monadic (
      let x := M.alloc (| x |) in
      let boolean := M.alloc (| boolean |) in
      M.read (|
        let y : M.Val u32.t :=
          M.copy (|
            ltac: (M.monadic_match_operator x
              [
                fun (γ : M.Val u32.t) =>
                  (M.alloc (| (Integer.of_Z 2) : u32.t |)) : M.Val u32.t;
                fun (γ : M.Val u32.t) =>
                  (M.alloc (| (Integer.of_Z 6) : u32.t |)) : M.Val u32.t;
                fun (γ : M.Val u32.t) =>
                  (M.alloc (| (Integer.of_Z 10) : u32.t |)) : M.Val u32.t;
                fun (γ : M.Val u32.t) =>
                  (M.alloc (| (Integer.of_Z 14) : u32.t |)) : M.Val u32.t;
                fun (γ : M.Val u32.t) =>
                  (M.alloc (| (Integer.of_Z 0) : u32.t |)) : M.Val u32.t
              ])
          |) in
        let binary : M.Val u32.t :=
          M.copy (|
          ltac: (M.monadic_match_operator boolean
              [
                fun (γ : M.Val u32.t) =>
                  (M.alloc (| (Integer.of_Z 0) : u32.t |)) : M.Val u32.t;
                fun (γ : M.Val u32.t) =>
                  (M.alloc (| (Integer.of_Z 1) : u32.t |)) : M.Val u32.t
              ])
          |) in
        M.alloc (|
          BinOp.Panic.add (|
            M.read (| x |),
            BinOp.Panic.mul (| M.read (| y |), M.read (| binary |) |)
          |)
        |)
      |)
    )).

End MonadicNotationExample.