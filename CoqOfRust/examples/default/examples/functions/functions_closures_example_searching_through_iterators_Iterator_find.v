(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

(*
fn main() {
    let vec1 = vec![1, 2, 3];
    let vec2 = vec![4, 5, 6];

    // `iter()` for vecs yields `&i32`.
    let mut iter = vec1.iter();
    // `into_iter()` for vecs yields `i32`.
    let mut into_iter = vec2.into_iter();

    // `iter()` for vecs yields `&i32`, and we want to reference one of its
    // items, so we have to destructure `&&i32` to `i32`
    println!("Find 2 in vec1: {:?}", iter.find(|&&x| x == 2));
    // `into_iter()` for vecs yields `i32`, and we want to reference one of
    // its items, so we have to destructure `&i32` to `i32`
    println!("Find 2 in vec2: {:?}", into_iter.find(|&x| x == 2));

    let array1 = [1, 2, 3];
    let array2 = [4, 5, 6];

    // `iter()` for arrays yields `&i32`
    println!("Find 2 in array1: {:?}", array1.iter().find(|&&x| x == 2));
    // `into_iter()` for arrays yields `i32`
    println!(
        "Find 2 in array2: {:?}",
        array2.into_iter().find(|&x| *x == 2)
    );
}
*)
(* #[allow(dead_code)] - function was ignored by the compiler *)
Definition main : M unit :=
  let* vec1 : M.Val (alloc.vec.Vec.t i32.t alloc.alloc.Global.t) :=
    let* α0 : M.Val i32.t := M.alloc (Integer.of_Z 1) in
    let* α1 : M.Val i32.t := M.alloc (Integer.of_Z 2) in
    let* α2 : M.Val i32.t := M.alloc (Integer.of_Z 3) in
    let* α3 : M.Val (array i32.t) := M.alloc [ α0; α1; α2 ] in
    let* α4 : M.Val (alloc.boxed.Box.t (array i32.t) alloc.alloc.Global.t) :=
      (alloc.boxed.Box _ alloc.boxed.Box.Default.A)::["new"] α3 in
    let* α5 : alloc.boxed.Box.t (slice i32.t) alloc.alloc.Global.t :=
      M.read (pointer_coercion "Unsize" α4) in
    let* α6 : alloc.vec.Vec.t i32.t alloc.alloc.Global.t :=
      (slice i32.t)::["into_vec"] α5 in
    M.alloc α6 in
  let* vec2 : M.Val (alloc.vec.Vec.t i32.t alloc.alloc.Global.t) :=
    let* α0 : M.Val i32.t := M.alloc (Integer.of_Z 4) in
    let* α1 : M.Val i32.t := M.alloc (Integer.of_Z 5) in
    let* α2 : M.Val i32.t := M.alloc (Integer.of_Z 6) in
    let* α3 : M.Val (array i32.t) := M.alloc [ α0; α1; α2 ] in
    let* α4 : M.Val (alloc.boxed.Box.t (array i32.t) alloc.alloc.Global.t) :=
      (alloc.boxed.Box _ alloc.boxed.Box.Default.A)::["new"] α3 in
    let* α5 : alloc.boxed.Box.t (slice i32.t) alloc.alloc.Global.t :=
      M.read (pointer_coercion "Unsize" α4) in
    let* α6 : alloc.vec.Vec.t i32.t alloc.alloc.Global.t :=
      (slice i32.t)::["into_vec"] α5 in
    M.alloc α6 in
  let* iter : M.Val (core.slice.iter.Iter.t i32.t) :=
    let* α0 : ref (slice i32.t) :=
      (core.ops.deref.Deref.deref
          (Self := alloc.vec.Vec.t i32.t alloc.alloc.Global.t)
          (Trait := ltac:(refine _)))
        (borrow vec1) in
    let* α1 : core.slice.iter.Iter.t i32.t := (slice i32.t)::["iter"] α0 in
    M.alloc α1 in
  let* into_iter :
      M.Val (alloc.vec.into_iter.IntoIter.t i32.t alloc.alloc.Global.t) :=
    let* α0 : alloc.vec.Vec.t i32.t alloc.alloc.Global.t := M.read vec2 in
    let* α1 : alloc.vec.into_iter.IntoIter.t i32.t alloc.alloc.Global.t :=
      (core.iter.traits.collect.IntoIterator.into_iter
          (Self := alloc.vec.Vec.t i32.t alloc.alloc.Global.t)
          (Trait := ltac:(refine _)))
        α0 in
    M.alloc α1 in
  let* _ : M.Val unit :=
    let* _ : M.Val unit :=
      let* α0 : M.Val (array (ref str.t)) :=
        M.alloc [ mk_str "Find 2 in vec1: "; mk_str "
" ] in
      let* α1 : M.Val (ref (array (ref str.t))) := M.alloc (borrow α0) in
      let* α2 : ref (slice (ref str.t)) :=
        M.read (pointer_coercion "Unsize" α1) in
      let* α3 : type not implemented :=
        M.read
          (let* α0 : i32.t := M.read x in
          M.alloc (BinOp.Pure.eq α0 (Integer.of_Z 2))) in
      let* α4 : core.option.Option.t (ref i32.t) :=
        (core.iter.traits.iterator.Iterator.find
            (Self := core.slice.iter.Iter.t i32.t)
            (Trait := ltac:(refine _)))
          (borrow_mut iter)
          α3 in
      let* α5 : M.Val (core.option.Option.t (ref i32.t)) := M.alloc α4 in
      let* α6 : core.fmt.rt.Argument.t :=
        core.fmt.rt.Argument.t::["new_debug"] (borrow α5) in
      let* α7 : M.Val core.fmt.rt.Argument.t := M.alloc α6 in
      let* α8 : M.Val (array core.fmt.rt.Argument.t) := M.alloc [ α7 ] in
      let* α9 : M.Val (ref (array core.fmt.rt.Argument.t)) :=
        M.alloc (borrow α8) in
      let* α10 : ref (slice core.fmt.rt.Argument.t) :=
        M.read (pointer_coercion "Unsize" α9) in
      let* α11 : core.fmt.Arguments.t :=
        core.fmt.Arguments.t::["new_v1"] α2 α10 in
      let* α12 : unit := std.io.stdio._print α11 in
      M.alloc α12 in
    M.alloc tt in
  let* _ : M.Val unit :=
    let* _ : M.Val unit :=
      let* α0 : M.Val (array (ref str.t)) :=
        M.alloc [ mk_str "Find 2 in vec2: "; mk_str "
" ] in
      let* α1 : M.Val (ref (array (ref str.t))) := M.alloc (borrow α0) in
      let* α2 : ref (slice (ref str.t)) :=
        M.read (pointer_coercion "Unsize" α1) in
      let* α3 : type not implemented :=
        M.read
          (let* α0 : i32.t := M.read x in
          M.alloc (BinOp.Pure.eq α0 (Integer.of_Z 2))) in
      let* α4 : core.option.Option.t i32.t :=
        (core.iter.traits.iterator.Iterator.find
            (Self := alloc.vec.into_iter.IntoIter.t i32.t alloc.alloc.Global.t)
            (Trait := ltac:(refine _)))
          (borrow_mut into_iter)
          α3 in
      let* α5 : M.Val (core.option.Option.t i32.t) := M.alloc α4 in
      let* α6 : core.fmt.rt.Argument.t :=
        core.fmt.rt.Argument.t::["new_debug"] (borrow α5) in
      let* α7 : M.Val core.fmt.rt.Argument.t := M.alloc α6 in
      let* α8 : M.Val (array core.fmt.rt.Argument.t) := M.alloc [ α7 ] in
      let* α9 : M.Val (ref (array core.fmt.rt.Argument.t)) :=
        M.alloc (borrow α8) in
      let* α10 : ref (slice core.fmt.rt.Argument.t) :=
        M.read (pointer_coercion "Unsize" α9) in
      let* α11 : core.fmt.Arguments.t :=
        core.fmt.Arguments.t::["new_v1"] α2 α10 in
      let* α12 : unit := std.io.stdio._print α11 in
      M.alloc α12 in
    M.alloc tt in
  let* array1 : M.Val (array i32.t) :=
    let* α0 : M.Val i32.t := M.alloc (Integer.of_Z 1) in
    let* α1 : M.Val i32.t := M.alloc (Integer.of_Z 2) in
    let* α2 : M.Val i32.t := M.alloc (Integer.of_Z 3) in
    M.alloc [ α0; α1; α2 ] in
  let* array2 : M.Val (array i32.t) :=
    let* α0 : M.Val i32.t := M.alloc (Integer.of_Z 4) in
    let* α1 : M.Val i32.t := M.alloc (Integer.of_Z 5) in
    let* α2 : M.Val i32.t := M.alloc (Integer.of_Z 6) in
    M.alloc [ α0; α1; α2 ] in
  let* _ : M.Val unit :=
    let* _ : M.Val unit :=
      let* α0 : M.Val (array (ref str.t)) :=
        M.alloc [ mk_str "Find 2 in array1: "; mk_str "
" ] in
      let* α1 : M.Val (ref (array (ref str.t))) := M.alloc (borrow α0) in
      let* α2 : ref (slice (ref str.t)) :=
        M.read (pointer_coercion "Unsize" α1) in
      let* α3 : M.Val (ref (array i32.t)) := M.alloc (borrow array1) in
      let* α4 : ref (slice i32.t) := M.read (pointer_coercion "Unsize" α3) in
      let* α5 : core.slice.iter.Iter.t i32.t := (slice i32.t)::["iter"] α4 in
      let* α6 : M.Val (core.slice.iter.Iter.t i32.t) := M.alloc α5 in
      let* α7 : type not implemented :=
        M.read
          (let* α0 : i32.t := M.read x in
          M.alloc (BinOp.Pure.eq α0 (Integer.of_Z 2))) in
      let* α8 : core.option.Option.t (ref i32.t) :=
        (core.iter.traits.iterator.Iterator.find
            (Self := core.slice.iter.Iter.t i32.t)
            (Trait := ltac:(refine _)))
          (borrow_mut α6)
          α7 in
      let* α9 : M.Val (core.option.Option.t (ref i32.t)) := M.alloc α8 in
      let* α10 : core.fmt.rt.Argument.t :=
        core.fmt.rt.Argument.t::["new_debug"] (borrow α9) in
      let* α11 : M.Val core.fmt.rt.Argument.t := M.alloc α10 in
      let* α12 : M.Val (array core.fmt.rt.Argument.t) := M.alloc [ α11 ] in
      let* α13 : M.Val (ref (array core.fmt.rt.Argument.t)) :=
        M.alloc (borrow α12) in
      let* α14 : ref (slice core.fmt.rt.Argument.t) :=
        M.read (pointer_coercion "Unsize" α13) in
      let* α15 : core.fmt.Arguments.t :=
        core.fmt.Arguments.t::["new_v1"] α2 α14 in
      let* α16 : unit := std.io.stdio._print α15 in
      M.alloc α16 in
    M.alloc tt in
  let* _ : M.Val unit :=
    let* _ : M.Val unit :=
      let* α0 : M.Val (array (ref str.t)) :=
        M.alloc [ mk_str "Find 2 in array2: "; mk_str "
" ] in
      let* α1 : M.Val (ref (array (ref str.t))) := M.alloc (borrow α0) in
      let* α2 : ref (slice (ref str.t)) :=
        M.read (pointer_coercion "Unsize" α1) in
      let* α3 : core.slice.iter.Iter.t i32.t :=
        (core.iter.traits.collect.IntoIterator.into_iter
            (Self := ref (array i32.t))
            (Trait := ltac:(refine _)))
          (borrow array2) in
      let* α4 : M.Val (core.slice.iter.Iter.t i32.t) := M.alloc α3 in
      let* α5 : type not implemented :=
        M.read
          (let* α0 : ref i32.t := M.read x in
          let* α1 : i32.t := M.read (deref α0) in
          M.alloc (BinOp.Pure.eq α1 (Integer.of_Z 2))) in
      let* α6 : core.option.Option.t (ref i32.t) :=
        (core.iter.traits.iterator.Iterator.find
            (Self := core.slice.iter.Iter.t i32.t)
            (Trait := ltac:(refine _)))
          (borrow_mut α4)
          α5 in
      let* α7 : M.Val (core.option.Option.t (ref i32.t)) := M.alloc α6 in
      let* α8 : core.fmt.rt.Argument.t :=
        core.fmt.rt.Argument.t::["new_debug"] (borrow α7) in
      let* α9 : M.Val core.fmt.rt.Argument.t := M.alloc α8 in
      let* α10 : M.Val (array core.fmt.rt.Argument.t) := M.alloc [ α9 ] in
      let* α11 : M.Val (ref (array core.fmt.rt.Argument.t)) :=
        M.alloc (borrow α10) in
      let* α12 : ref (slice core.fmt.rt.Argument.t) :=
        M.read (pointer_coercion "Unsize" α11) in
      let* α13 : core.fmt.Arguments.t :=
        core.fmt.Arguments.t::["new_v1"] α2 α12 in
      let* α14 : unit := std.io.stdio._print α13 in
      M.alloc α14 in
    M.alloc tt in
  let* α0 : M.Val unit := M.alloc tt in
  M.read α0.