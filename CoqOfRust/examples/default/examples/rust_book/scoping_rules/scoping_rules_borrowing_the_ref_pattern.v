(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Module  Point.
Section Point.
  Record t : Set := {
    x : i32.t;
    y : i32.t;
  }.
  
  Definition Get_x :=
    Ref.map (fun α => Some α.(x)) (fun β α => Some (α <| x := β |>)).
  Definition Get_y :=
    Ref.map (fun α => Some α.(y)) (fun β α => Some (α <| y := β |>)).
End Point.
End Point.

Module  Impl_core_clone_Clone_for_scoping_rules_borrowing_the_ref_pattern_Point_t.
Section Impl_core_clone_Clone_for_scoping_rules_borrowing_the_ref_pattern_Point_t.
  Definition Self : Set := scoping_rules_borrowing_the_ref_pattern.Point.t.
  
  (*
  Clone
  *)
  Definition clone
      (self : ref Self)
      : M scoping_rules_borrowing_the_ref_pattern.Point.t :=
    let* self := M.alloc self in
    let* α0 : M.Val scoping_rules_borrowing_the_ref_pattern.Point.t :=
      match_operator
        (DeclaredButUndefinedVariable
          (A := core.clone.AssertParamIsClone.t i32.t))
        [
          fun γ =>
            (let* α0 : ref scoping_rules_borrowing_the_ref_pattern.Point.t :=
              M.read self in
            M.pure (deref α0)) :
            M (M.Val scoping_rules_borrowing_the_ref_pattern.Point.t)
        ] in
    M.read α0.
  
  Global Instance AssociatedFunction_clone :
    Notations.DoubleColon Self "clone" := {
    Notations.double_colon := clone;
  }.
  
  Global Instance ℐ : core.clone.Clone.Required.Trait Self := {
    core.clone.Clone.clone := clone;
    core.clone.Clone.clone_from := Datatypes.None;
  }.
End Impl_core_clone_Clone_for_scoping_rules_borrowing_the_ref_pattern_Point_t.
End Impl_core_clone_Clone_for_scoping_rules_borrowing_the_ref_pattern_Point_t.

Module  Impl_core_marker_Copy_for_scoping_rules_borrowing_the_ref_pattern_Point_t.
Section Impl_core_marker_Copy_for_scoping_rules_borrowing_the_ref_pattern_Point_t.
  Definition Self : Set := scoping_rules_borrowing_the_ref_pattern.Point.t.
  
  Global Instance ℐ : core.marker.Copy.Trait Self := {
  }.
End Impl_core_marker_Copy_for_scoping_rules_borrowing_the_ref_pattern_Point_t.
End Impl_core_marker_Copy_for_scoping_rules_borrowing_the_ref_pattern_Point_t.

(*
fn main() {
    let c = 'Q';

    // A `ref` borrow on the left side of an assignment is equivalent to
    // an `&` borrow on the right side.
    let ref ref_c1 = c;
    let ref_c2 = &c;

    println!("ref_c1 equals ref_c2: {}", *ref_c1 == *ref_c2);

    let point = Point { x: 0, y: 0 };

    // `ref` is also valid when destructuring a struct.
    let _copy_of_x = {
        // `ref_to_x` is a reference to the `x` field of `point`.
        let Point {
            x: ref ref_to_x,
            y: _,
        } = point;

        // Return a copy of the `x` field of `point`.
        *ref_to_x
    };

    // A mutable copy of `point`
    let mut mutable_point = point;

    {
        // `ref` can be paired with `mut` to take mutable references.
        let Point {
            x: _,
            y: ref mut mut_ref_to_y,
        } = mutable_point;

        // Mutate the `y` field of `mutable_point` via a mutable reference.
        *mut_ref_to_y = 1;
    }

    println!("point is ({}, {})", point.x, point.y);
    println!(
        "mutable_point is ({}, {})",
        mutable_point.x, mutable_point.y
    );

    // A mutable tuple that includes a pointer
    let mut mutable_tuple = (Box::new(5u32), 3u32);

    {
        // Destructure `mutable_tuple` to change the value of `last`.
        let (_, ref mut last) = mutable_tuple;
        *last = 2u32;
    }

    println!("tuple is {:?}", mutable_tuple);
}
*)
(* #[allow(dead_code)] - function was ignored by the compiler *)
Definition main : M unit :=
  let* c : M.Val char.t := M.alloc "Q"%char in
  let* α0 : M.Val unit :=
    match_operator
      c
      [
        fun γ =>
          (let* ref_c1 := M.alloc (borrow γ) in
          let* ref_c2 : M.Val (ref char.t) := M.alloc (borrow c) in
          let* _ : M.Val unit :=
            let* _ : M.Val unit :=
              let* α0 : ref str.t := M.read (mk_str "ref_c1 equals ref_c2: ") in
              let* α1 : ref str.t := M.read (mk_str "
") in
              let* α2 : M.Val (array (ref str.t)) := M.alloc [ α0; α1 ] in
              let* α3 : ref char.t := M.read ref_c1 in
              let* α4 : char.t := M.read (deref α3) in
              let* α5 : ref char.t := M.read ref_c2 in
              let* α6 : char.t := M.read (deref α5) in
              let* α7 : M.Val bool.t := M.alloc (BinOp.Pure.eq α4 α6) in
              let* α8 : core.fmt.rt.Argument.t :=
                M.call (core.fmt.rt.Argument.t::["new_display"] (borrow α7)) in
              let* α9 : M.Val (array core.fmt.rt.Argument.t) :=
                M.alloc [ α8 ] in
              let* α10 : core.fmt.Arguments.t :=
                M.call
                  (core.fmt.Arguments.t::["new_v1"]
                    (pointer_coercion "Unsize" (borrow α2))
                    (pointer_coercion "Unsize" (borrow α9))) in
              let* α11 : unit := M.call (std.io.stdio._print α10) in
              M.alloc α11 in
            M.alloc tt in
          let* point : M.Val scoping_rules_borrowing_the_ref_pattern.Point.t :=
            M.alloc
              {|
                scoping_rules_borrowing_the_ref_pattern.Point.x :=
                  (Integer.of_Z 0) : i32.t;
                scoping_rules_borrowing_the_ref_pattern.Point.y :=
                  (Integer.of_Z 0) : i32.t;
              |} in
          let* _copy_of_x : M.Val i32.t :=
            let* α0 : M.Val i32.t :=
              match_operator
                point
                [
                  fun γ =>
                    (let* α0 := M.read γ in
                    match α0 with
                    |
                        {|
                          scoping_rules_borrowing_the_ref_pattern.Point.x := _;
                          scoping_rules_borrowing_the_ref_pattern.Point.y := _;
                        |}
                        =>
                      let γ0_0 :=
                        scoping_rules_borrowing_the_ref_pattern.Point.Get_x γ in
                      let γ0_1 :=
                        scoping_rules_borrowing_the_ref_pattern.Point.Get_y γ in
                      let* ref_to_x := M.alloc (borrow γ0_0) in
                      let* α0 : ref i32.t := M.read ref_to_x in
                      M.pure (deref α0)
                    end) :
                    M (M.Val i32.t)
                ] in
            M.copy α0 in
          let* mutable_point :
              M.Val scoping_rules_borrowing_the_ref_pattern.Point.t :=
            M.copy point in
          let* _ : M.Val unit :=
            match_operator
              mutable_point
              [
                fun γ =>
                  (let* α0 := M.read γ in
                  match α0 with
                  |
                      {|
                        scoping_rules_borrowing_the_ref_pattern.Point.x := _;
                        scoping_rules_borrowing_the_ref_pattern.Point.y := _;
                      |}
                      =>
                    let γ0_0 :=
                      scoping_rules_borrowing_the_ref_pattern.Point.Get_x γ in
                    let γ0_1 :=
                      scoping_rules_borrowing_the_ref_pattern.Point.Get_y γ in
                    let* mut_ref_to_y := M.alloc (borrow_mut γ0_1) in
                    let* _ : M.Val unit :=
                      let* α0 : mut_ref i32.t := M.read mut_ref_to_y in
                      assign (deref α0) ((Integer.of_Z 1) : i32.t) in
                    M.alloc tt
                  end) :
                  M (M.Val unit)
              ] in
          let* _ : M.Val unit :=
            let* _ : M.Val unit :=
              let* α0 : ref str.t := M.read (mk_str "point is (") in
              let* α1 : ref str.t := M.read (mk_str ", ") in
              let* α2 : ref str.t := M.read (mk_str ")
") in
              let* α3 : M.Val (array (ref str.t)) := M.alloc [ α0; α1; α2 ] in
              let* α4 : core.fmt.rt.Argument.t :=
                M.call
                  (core.fmt.rt.Argument.t::["new_display"]
                    (borrow
                      (scoping_rules_borrowing_the_ref_pattern.Point.Get_x
                        point))) in
              let* α5 : core.fmt.rt.Argument.t :=
                M.call
                  (core.fmt.rt.Argument.t::["new_display"]
                    (borrow
                      (scoping_rules_borrowing_the_ref_pattern.Point.Get_y
                        point))) in
              let* α6 : M.Val (array core.fmt.rt.Argument.t) :=
                M.alloc [ α4; α5 ] in
              let* α7 : core.fmt.Arguments.t :=
                M.call
                  (core.fmt.Arguments.t::["new_v1"]
                    (pointer_coercion "Unsize" (borrow α3))
                    (pointer_coercion "Unsize" (borrow α6))) in
              let* α8 : unit := M.call (std.io.stdio._print α7) in
              M.alloc α8 in
            M.alloc tt in
          let* _ : M.Val unit :=
            let* _ : M.Val unit :=
              let* α0 : ref str.t := M.read (mk_str "mutable_point is (") in
              let* α1 : ref str.t := M.read (mk_str ", ") in
              let* α2 : ref str.t := M.read (mk_str ")
") in
              let* α3 : M.Val (array (ref str.t)) := M.alloc [ α0; α1; α2 ] in
              let* α4 : core.fmt.rt.Argument.t :=
                M.call
                  (core.fmt.rt.Argument.t::["new_display"]
                    (borrow
                      (scoping_rules_borrowing_the_ref_pattern.Point.Get_x
                        mutable_point))) in
              let* α5 : core.fmt.rt.Argument.t :=
                M.call
                  (core.fmt.rt.Argument.t::["new_display"]
                    (borrow
                      (scoping_rules_borrowing_the_ref_pattern.Point.Get_y
                        mutable_point))) in
              let* α6 : M.Val (array core.fmt.rt.Argument.t) :=
                M.alloc [ α4; α5 ] in
              let* α7 : core.fmt.Arguments.t :=
                M.call
                  (core.fmt.Arguments.t::["new_v1"]
                    (pointer_coercion "Unsize" (borrow α3))
                    (pointer_coercion "Unsize" (borrow α6))) in
              let* α8 : unit := M.call (std.io.stdio._print α7) in
              M.alloc α8 in
            M.alloc tt in
          let* mutable_tuple :
              M.Val ((alloc.boxed.Box.t u32.t alloc.alloc.Global.t) * u32.t) :=
            let* α0 : alloc.boxed.Box.t u32.t alloc.alloc.Global.t :=
              M.call
                ((alloc.boxed.Box.t u32.t alloc.alloc.Global.t)::["new"]
                  ((Integer.of_Z 5) : u32.t)) in
            M.alloc (α0, (Integer.of_Z 3) : u32.t) in
          let* _ : M.Val unit :=
            match_operator
              mutable_tuple
              [
                fun γ =>
                  (let* α0 := M.read γ in
                  match α0 with
                  | (_, _) =>
                    let γ0_0 := Tuple.Access.left γ in
                    let γ0_1 := Tuple.Access.right γ in
                    let* last := M.alloc (borrow_mut γ0_1) in
                    let* _ : M.Val unit :=
                      let* α0 : mut_ref u32.t := M.read last in
                      assign (deref α0) ((Integer.of_Z 2) : u32.t) in
                    M.alloc tt
                  end) :
                  M (M.Val unit)
              ] in
          let* _ : M.Val unit :=
            let* _ : M.Val unit :=
              let* α0 : ref str.t := M.read (mk_str "tuple is ") in
              let* α1 : ref str.t := M.read (mk_str "
") in
              let* α2 : M.Val (array (ref str.t)) := M.alloc [ α0; α1 ] in
              let* α3 : core.fmt.rt.Argument.t :=
                M.call
                  (core.fmt.rt.Argument.t::["new_debug"]
                    (borrow mutable_tuple)) in
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
          M.alloc tt) :
          M (M.Val unit)
      ] in
  M.read α0.