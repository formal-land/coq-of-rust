(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

(*
fn main() {
    let some_vector = vec![1, 2, 3, 4];

    let pointer = some_vector.as_ptr();
    let length = some_vector.len();

    unsafe {
        let my_slice: &[u32] = slice::from_raw_parts(pointer, length);

        assert_eq!(some_vector.as_slice(), my_slice);
    }
}
*)
(* #[allow(dead_code)] - function was ignored by the compiler *)
Definition main : M unit :=
  let* some_vector : M.Val (alloc.vec.Vec.t u32.t alloc.alloc.Global.t) :=
    let* α0 : M.Val (array u32.t) :=
      M.alloc
        [
          (Integer.of_Z 1) : u32.t;
          (Integer.of_Z 2) : u32.t;
          (Integer.of_Z 3) : u32.t;
          (Integer.of_Z 4) : u32.t
        ] in
    let* α1 : M.Val (alloc.boxed.Box.t (array u32.t) alloc.alloc.Global.t) :=
      M.call ((alloc.boxed.Box.t _ alloc.boxed.Box.Default.A)::["new"] α0) in
    let* α2 : alloc.boxed.Box.t (array u32.t) alloc.alloc.Global.t :=
      M.read α1 in
    let* α3 : alloc.vec.Vec.t u32.t alloc.alloc.Global.t :=
      M.call ((slice u32.t)::["into_vec"] (pointer_coercion "Unsize" α2)) in
    M.alloc α3 in
  let* pointer : M.Val (ref u32.t) :=
    let* α0 : ref u32.t :=
      M.call
        ((alloc.vec.Vec.t u32.t alloc.alloc.Global.t)::["as_ptr"]
          (borrow some_vector)) in
    M.alloc α0 in
  let* length : M.Val usize.t :=
    let* α0 : usize.t :=
      M.call
        ((alloc.vec.Vec.t u32.t alloc.alloc.Global.t)::["len"]
          (borrow some_vector)) in
    M.alloc α0 in
  let* my_slice : M.Val (ref (slice u32.t)) :=
    let* α0 : ref u32.t := M.read pointer in
    let* α1 : usize.t := M.read length in
    let* α2 : ref (slice u32.t) :=
      M.call (core.slice.raw.from_raw_parts α0 α1) in
    M.alloc α2 in
  let* _ : M.Val unit :=
    let* α0 : ref (slice u32.t) :=
      M.call
        ((alloc.vec.Vec.t u32.t alloc.alloc.Global.t)::["as_slice"]
          (borrow some_vector)) in
    let* α1 : M.Val (ref (slice u32.t)) := M.alloc α0 in
    let* α2 : M.Val ((ref (ref (slice u32.t))) * (ref (ref (slice u32.t)))) :=
      M.alloc (borrow α1, borrow my_slice) in
    match_operator
      α2
      [
        fun γ =>
          (let* α0 := M.read γ in
          match α0 with
          | (_, _) =>
            let γ0_0 := Tuple.Access.left γ in
            let γ0_1 := Tuple.Access.right γ in
            let* left_val := M.copy γ0_0 in
            let* right_val := M.copy γ0_1 in
            let* α0 :
                (ref (ref (slice u32.t))) ->
                  (ref (ref (slice u32.t))) ->
                  M bool.t :=
              ltac:(M.get_method (fun ℐ =>
                core.cmp.PartialEq.eq
                  (Self := ref (slice u32.t))
                  (Rhs := ref (slice u32.t))
                  (Trait := ℐ))) in
            let* α1 : ref (ref (slice u32.t)) := M.read left_val in
            let* α2 : ref (ref (slice u32.t)) := M.read right_val in
            let* α3 : bool.t := M.call (α0 α1 α2) in
            let* α4 : M.Val bool.t := M.alloc (UnOp.not α3) in
            let* α5 : bool.t := M.read (use α4) in
            if α5 then
              let* kind : M.Val core.panicking.AssertKind.t :=
                M.alloc core.panicking.AssertKind.Eq in
              let* α0 : core.panicking.AssertKind.t := M.read kind in
              let* α1 : ref (ref (slice u32.t)) := M.read left_val in
              let* α2 : ref (ref (slice u32.t)) := M.read right_val in
              let* α3 : never.t :=
                M.call
                  (core.panicking.assert_failed
                    α0
                    α1
                    α2
                    core.option.Option.None) in
              let* α0 : M.Val never.t := M.alloc α3 in
              let* α1 := M.read α0 in
              let* α2 : unit := never_to_any α1 in
              M.alloc α2
            else
              M.alloc tt
          end) :
          M (M.Val unit)
      ] in
  let* α0 : M.Val unit := M.alloc tt in
  M.read α0.