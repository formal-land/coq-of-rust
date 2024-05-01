(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Module num.
  Module int_log10.
    (*
    pub const fn u8(val: u8) -> u32 {
        let val = val as u32;
    
        // For better performance, avoid branches by assembling the solution
        // in the bits above the low 8 bits.
    
        // Adding c1 to val gives 10 in the top bits for val < 10, 11 for val >= 10
        const C1: u32 = 0b11_00000000 - 10; // 758
        // Adding c2 to val gives 01 in the top bits for val < 100, 10 for val >= 100
        const C2: u32 = 0b10_00000000 - 100; // 412
    
        // Value of top bits:
        //            +c1  +c2  1&2
        //     0..=9   10   01   00 = 0
        //   10..=99   11   01   01 = 1
        // 100..=255   11   10   10 = 2
        ((val + C1) & (val + C2)) >> 8
    }
    *)
    Definition u8 (τ : list Ty.t) (α : list Value.t) : M :=
      match τ, α with
      | [], [ val ] =>
        ltac:(M.monadic
          (let val := M.alloc (| val |) in
          M.read (|
            let val := M.alloc (| M.rust_cast (M.read (| val |)) |) in
            M.alloc (|
              BinOp.Panic.shr (|
                BinOp.Pure.bit_and
                  (BinOp.Panic.add (|
                    Integer.U32,
                    M.read (| val |),
                    M.read (| M.get_constant (| "core::num::int_log10::u8::C1" |) |)
                  |))
                  (BinOp.Panic.add (|
                    Integer.U32,
                    M.read (| val |),
                    M.read (| M.get_constant (| "core::num::int_log10::u8::C2" |) |)
                  |)),
                Value.Integer 8
              |)
            |)
          |)))
      | _, _ => M.impossible
      end.
    
    Module u8.
      Definition value_C1 : Value.t :=
        M.run
          ltac:(M.monadic
            (M.alloc (| BinOp.Panic.sub (| Integer.U32, Value.Integer 768, Value.Integer 10 |) |))).
      
      Definition value_C2 : Value.t :=
        M.run
          ltac:(M.monadic
            (M.alloc (|
              BinOp.Panic.sub (| Integer.U32, Value.Integer 512, Value.Integer 100 |)
            |))).
    End u8.
    
    (*
    const fn less_than_5(val: u32) -> u32 {
        // Similar to u8, when adding one of these constants to val,
        // we get two possible bit patterns above the low 17 bits,
        // depending on whether val is below or above the threshold.
        const C1: u32 = 0b011_00000000000000000 - 10; // 393206
        const C2: u32 = 0b100_00000000000000000 - 100; // 524188
        const C3: u32 = 0b111_00000000000000000 - 1000; // 916504
        const C4: u32 = 0b100_00000000000000000 - 10000; // 514288
    
        // Value of top bits:
        //                +c1  +c2  1&2  +c3  +c4  3&4   ^
        //         0..=9  010  011  010  110  011  010  000 = 0
        //       10..=99  011  011  011  110  011  010  001 = 1
        //     100..=999  011  100  000  110  011  010  010 = 2
        //   1000..=9999  011  100  000  111  011  011  011 = 3
        // 10000..=99999  011  100  000  111  100  100  100 = 4
        (((val + C1) & (val + C2)) ^ ((val + C3) & (val + C4))) >> 17
    }
    *)
    Definition less_than_5 (τ : list Ty.t) (α : list Value.t) : M :=
      match τ, α with
      | [], [ val ] =>
        ltac:(M.monadic
          (let val := M.alloc (| val |) in
          BinOp.Panic.shr (|
            BinOp.Pure.bit_xor
              (BinOp.Pure.bit_and
                (BinOp.Panic.add (|
                  Integer.U32,
                  M.read (| val |),
                  M.read (| M.get_constant (| "core::num::int_log10::less_than_5::C1" |) |)
                |))
                (BinOp.Panic.add (|
                  Integer.U32,
                  M.read (| val |),
                  M.read (| M.get_constant (| "core::num::int_log10::less_than_5::C2" |) |)
                |)))
              (BinOp.Pure.bit_and
                (BinOp.Panic.add (|
                  Integer.U32,
                  M.read (| val |),
                  M.read (| M.get_constant (| "core::num::int_log10::less_than_5::C3" |) |)
                |))
                (BinOp.Panic.add (|
                  Integer.U32,
                  M.read (| val |),
                  M.read (| M.get_constant (| "core::num::int_log10::less_than_5::C4" |) |)
                |))),
            Value.Integer 17
          |)))
      | _, _ => M.impossible
      end.
    
    Module less_than_5.
      Definition value_C1 : Value.t :=
        M.run
          ltac:(M.monadic
            (M.alloc (|
              BinOp.Panic.sub (| Integer.U32, Value.Integer 393216, Value.Integer 10 |)
            |))).
      
      Definition value_C2 : Value.t :=
        M.run
          ltac:(M.monadic
            (M.alloc (|
              BinOp.Panic.sub (| Integer.U32, Value.Integer 524288, Value.Integer 100 |)
            |))).
      
      Definition value_C3 : Value.t :=
        M.run
          ltac:(M.monadic
            (M.alloc (|
              BinOp.Panic.sub (| Integer.U32, Value.Integer 917504, Value.Integer 1000 |)
            |))).
      
      Definition value_C4 : Value.t :=
        M.run
          ltac:(M.monadic
            (M.alloc (|
              BinOp.Panic.sub (| Integer.U32, Value.Integer 524288, Value.Integer 10000 |)
            |))).
    End less_than_5.
    
    (*
    pub const fn u16(val: u16) -> u32 {
        less_than_5(val as u32)
    }
    *)
    Definition u16 (τ : list Ty.t) (α : list Value.t) : M :=
      match τ, α with
      | [], [ val ] =>
        ltac:(M.monadic
          (let val := M.alloc (| val |) in
          M.call_closure (|
            M.get_function (| "core::num::int_log10::less_than_5", [] |),
            [ M.rust_cast (M.read (| val |)) ]
          |)))
      | _, _ => M.impossible
      end.
    
    (*
    pub const fn u32(mut val: u32) -> u32 {
        let mut log = 0;
        if val >= 100_000 {
            val /= 100_000;
            log += 5;
        }
        log + less_than_5(val)
    }
    *)
    Definition u32 (τ : list Ty.t) (α : list Value.t) : M :=
      match τ, α with
      | [], [ val ] =>
        ltac:(M.monadic
          (let val := M.alloc (| val |) in
          M.read (|
            let log := M.alloc (| Value.Integer 0 |) in
            let _ :=
              M.match_operator (|
                M.alloc (| Value.Tuple [] |),
                [
                  fun γ =>
                    ltac:(M.monadic
                      (let γ :=
                        M.use
                          (M.alloc (| BinOp.Pure.ge (M.read (| val |)) (Value.Integer 100000) |)) in
                      let _ := M.is_constant_or_break_match (| M.read (| γ |), Value.Bool true |) in
                      let _ :=
                        let β := val in
                        M.write (|
                          β,
                          BinOp.Panic.div (| Integer.U32, M.read (| β |), Value.Integer 100000 |)
                        |) in
                      let _ :=
                        let β := log in
                        M.write (|
                          β,
                          BinOp.Panic.add (| Integer.U32, M.read (| β |), Value.Integer 5 |)
                        |) in
                      M.alloc (| Value.Tuple [] |)));
                  fun γ => ltac:(M.monadic (M.alloc (| Value.Tuple [] |)))
                ]
              |) in
            M.alloc (|
              BinOp.Panic.add (|
                Integer.U32,
                M.read (| log |),
                M.call_closure (|
                  M.get_function (| "core::num::int_log10::less_than_5", [] |),
                  [ M.read (| val |) ]
                |)
              |)
            |)
          |)))
      | _, _ => M.impossible
      end.
    
    (*
    pub const fn u64(mut val: u64) -> u32 {
        let mut log = 0;
        if val >= 10_000_000_000 {
            val /= 10_000_000_000;
            log += 10;
        }
        if val >= 100_000 {
            val /= 100_000;
            log += 5;
        }
        log + less_than_5(val as u32)
    }
    *)
    Definition u64 (τ : list Ty.t) (α : list Value.t) : M :=
      match τ, α with
      | [], [ val ] =>
        ltac:(M.monadic
          (let val := M.alloc (| val |) in
          M.read (|
            let log := M.alloc (| Value.Integer 0 |) in
            let _ :=
              M.match_operator (|
                M.alloc (| Value.Tuple [] |),
                [
                  fun γ =>
                    ltac:(M.monadic
                      (let γ :=
                        M.use
                          (M.alloc (|
                            BinOp.Pure.ge (M.read (| val |)) (Value.Integer 10000000000)
                          |)) in
                      let _ := M.is_constant_or_break_match (| M.read (| γ |), Value.Bool true |) in
                      let _ :=
                        let β := val in
                        M.write (|
                          β,
                          BinOp.Panic.div (|
                            Integer.U64,
                            M.read (| β |),
                            Value.Integer 10000000000
                          |)
                        |) in
                      let _ :=
                        let β := log in
                        M.write (|
                          β,
                          BinOp.Panic.add (| Integer.U32, M.read (| β |), Value.Integer 10 |)
                        |) in
                      M.alloc (| Value.Tuple [] |)));
                  fun γ => ltac:(M.monadic (M.alloc (| Value.Tuple [] |)))
                ]
              |) in
            let _ :=
              M.match_operator (|
                M.alloc (| Value.Tuple [] |),
                [
                  fun γ =>
                    ltac:(M.monadic
                      (let γ :=
                        M.use
                          (M.alloc (| BinOp.Pure.ge (M.read (| val |)) (Value.Integer 100000) |)) in
                      let _ := M.is_constant_or_break_match (| M.read (| γ |), Value.Bool true |) in
                      let _ :=
                        let β := val in
                        M.write (|
                          β,
                          BinOp.Panic.div (| Integer.U64, M.read (| β |), Value.Integer 100000 |)
                        |) in
                      let _ :=
                        let β := log in
                        M.write (|
                          β,
                          BinOp.Panic.add (| Integer.U32, M.read (| β |), Value.Integer 5 |)
                        |) in
                      M.alloc (| Value.Tuple [] |)));
                  fun γ => ltac:(M.monadic (M.alloc (| Value.Tuple [] |)))
                ]
              |) in
            M.alloc (|
              BinOp.Panic.add (|
                Integer.U32,
                M.read (| log |),
                M.call_closure (|
                  M.get_function (| "core::num::int_log10::less_than_5", [] |),
                  [ M.rust_cast (M.read (| val |)) ]
                |)
              |)
            |)
          |)))
      | _, _ => M.impossible
      end.
    
    (*
    pub const fn u128(mut val: u128) -> u32 {
        let mut log = 0;
        if val >= 100_000_000_000_000_000_000_000_000_000_000 {
            val /= 100_000_000_000_000_000_000_000_000_000_000;
            log += 32;
            return log + u32(val as u32);
        }
        if val >= 10_000_000_000_000_000 {
            val /= 10_000_000_000_000_000;
            log += 16;
        }
        log + u64(val as u64)
    }
    *)
    Definition u128 (τ : list Ty.t) (α : list Value.t) : M :=
      match τ, α with
      | [], [ val ] =>
        ltac:(M.monadic
          (let val := M.alloc (| val |) in
          M.catch_return (|
            ltac:(M.monadic
              (M.read (|
                let log := M.alloc (| Value.Integer 0 |) in
                let _ :=
                  M.match_operator (|
                    M.alloc (| Value.Tuple [] |),
                    [
                      fun γ =>
                        ltac:(M.monadic
                          (let γ :=
                            M.use
                              (M.alloc (|
                                BinOp.Pure.ge
                                  (M.read (| val |))
                                  (Value.Integer 100000000000000000000000000000000)
                              |)) in
                          let _ :=
                            M.is_constant_or_break_match (| M.read (| γ |), Value.Bool true |) in
                          M.alloc (|
                            M.never_to_any (|
                              M.read (|
                                let _ :=
                                  let β := val in
                                  M.write (|
                                    β,
                                    BinOp.Panic.div (|
                                      Integer.U128,
                                      M.read (| β |),
                                      Value.Integer 100000000000000000000000000000000
                                    |)
                                  |) in
                                let _ :=
                                  let β := log in
                                  M.write (|
                                    β,
                                    BinOp.Panic.add (|
                                      Integer.U32,
                                      M.read (| β |),
                                      Value.Integer 32
                                    |)
                                  |) in
                                M.return_ (|
                                  BinOp.Panic.add (|
                                    Integer.U32,
                                    M.read (| log |),
                                    M.call_closure (|
                                      M.get_function (| "core::num::int_log10::u32", [] |),
                                      [ M.rust_cast (M.read (| val |)) ]
                                    |)
                                  |)
                                |)
                              |)
                            |)
                          |)));
                      fun γ => ltac:(M.monadic (M.alloc (| Value.Tuple [] |)))
                    ]
                  |) in
                let _ :=
                  M.match_operator (|
                    M.alloc (| Value.Tuple [] |),
                    [
                      fun γ =>
                        ltac:(M.monadic
                          (let γ :=
                            M.use
                              (M.alloc (|
                                BinOp.Pure.ge (M.read (| val |)) (Value.Integer 10000000000000000)
                              |)) in
                          let _ :=
                            M.is_constant_or_break_match (| M.read (| γ |), Value.Bool true |) in
                          let _ :=
                            let β := val in
                            M.write (|
                              β,
                              BinOp.Panic.div (|
                                Integer.U128,
                                M.read (| β |),
                                Value.Integer 10000000000000000
                              |)
                            |) in
                          let _ :=
                            let β := log in
                            M.write (|
                              β,
                              BinOp.Panic.add (| Integer.U32, M.read (| β |), Value.Integer 16 |)
                            |) in
                          M.alloc (| Value.Tuple [] |)));
                      fun γ => ltac:(M.monadic (M.alloc (| Value.Tuple [] |)))
                    ]
                  |) in
                M.alloc (|
                  BinOp.Panic.add (|
                    Integer.U32,
                    M.read (| log |),
                    M.call_closure (|
                      M.get_function (| "core::num::int_log10::u64", [] |),
                      [ M.rust_cast (M.read (| val |)) ]
                    |)
                  |)
                |)
              |)))
          |)))
      | _, _ => M.impossible
      end.
    
    (*
    pub const fn usize(val: usize) -> u32 {
        u64(val as _)
    }
    *)
    Definition usize (τ : list Ty.t) (α : list Value.t) : M :=
      match τ, α with
      | [], [ val ] =>
        ltac:(M.monadic
          (let val := M.alloc (| val |) in
          M.call_closure (|
            M.get_function (| "core::num::int_log10::u64", [] |),
            [ M.rust_cast (M.read (| val |)) ]
          |)))
      | _, _ => M.impossible
      end.
    
    (*
    pub const fn i8(val: i8) -> u32 {
        u8(val as u8)
    }
    *)
    Definition i8 (τ : list Ty.t) (α : list Value.t) : M :=
      match τ, α with
      | [], [ val ] =>
        ltac:(M.monadic
          (let val := M.alloc (| val |) in
          M.call_closure (|
            M.get_function (| "core::num::int_log10::u8", [] |),
            [ M.rust_cast (M.read (| val |)) ]
          |)))
      | _, _ => M.impossible
      end.
    
    (*
    pub const fn i16(val: i16) -> u32 {
        u16(val as u16)
    }
    *)
    Definition i16 (τ : list Ty.t) (α : list Value.t) : M :=
      match τ, α with
      | [], [ val ] =>
        ltac:(M.monadic
          (let val := M.alloc (| val |) in
          M.call_closure (|
            M.get_function (| "core::num::int_log10::u16", [] |),
            [ M.rust_cast (M.read (| val |)) ]
          |)))
      | _, _ => M.impossible
      end.
    
    (*
    pub const fn i32(val: i32) -> u32 {
        u32(val as u32)
    }
    *)
    Definition i32 (τ : list Ty.t) (α : list Value.t) : M :=
      match τ, α with
      | [], [ val ] =>
        ltac:(M.monadic
          (let val := M.alloc (| val |) in
          M.call_closure (|
            M.get_function (| "core::num::int_log10::u32", [] |),
            [ M.rust_cast (M.read (| val |)) ]
          |)))
      | _, _ => M.impossible
      end.
    
    (*
    pub const fn i64(val: i64) -> u32 {
        u64(val as u64)
    }
    *)
    Definition i64 (τ : list Ty.t) (α : list Value.t) : M :=
      match τ, α with
      | [], [ val ] =>
        ltac:(M.monadic
          (let val := M.alloc (| val |) in
          M.call_closure (|
            M.get_function (| "core::num::int_log10::u64", [] |),
            [ M.rust_cast (M.read (| val |)) ]
          |)))
      | _, _ => M.impossible
      end.
    
    (*
    pub const fn i128(val: i128) -> u32 {
        u128(val as u128)
    }
    *)
    Definition i128 (τ : list Ty.t) (α : list Value.t) : M :=
      match τ, α with
      | [], [ val ] =>
        ltac:(M.monadic
          (let val := M.alloc (| val |) in
          M.call_closure (|
            M.get_function (| "core::num::int_log10::u128", [] |),
            [ M.rust_cast (M.read (| val |)) ]
          |)))
      | _, _ => M.impossible
      end.
    
    (*
    pub const fn panic_for_nonpositive_argument() -> ! {
        panic!("argument of integer logarithm must be positive")
    }
    *)
    Definition panic_for_nonpositive_argument (τ : list Ty.t) (α : list Value.t) : M :=
      match τ, α with
      | [], [] =>
        ltac:(M.monadic
          (M.call_closure (|
            M.get_function (| "core::panicking::panic_fmt", [] |),
            [
              M.call_closure (|
                M.get_associated_function (| Ty.path "core::fmt::Arguments", "new_const", [] |),
                [
                  (* Unsize *)
                  M.pointer_coercion
                    (M.alloc (|
                      Value.Array
                        [ M.read (| Value.String "argument of integer logarithm must be positive" |)
                        ]
                    |))
                ]
              |)
            ]
          |)))
      | _, _ => M.impossible
      end.
  End int_log10.
End num.