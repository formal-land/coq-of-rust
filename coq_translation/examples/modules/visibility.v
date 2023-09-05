(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Module my_mod.
  Definition private_function `{H' : State.Trait} : M (H := H') unit :=
    let* _ :=
      let* _ :=
        let* α0 :=
          format_arguments::["new_const"]
            (addr_of [ "called `my_mod::private_function()`
" ]) in
        std.io.stdio._print α0 in
      Pure tt in
    Pure tt.
  
  Definition function `{H' : State.Trait} : M (H := H') unit :=
    let* _ :=
      let* _ :=
        let* α0 :=
          format_arguments::["new_const"]
            (addr_of [ "called `my_mod::function()`
" ]) in
        std.io.stdio._print α0 in
      Pure tt in
    Pure tt.
  
  Definition indirect_access `{H' : State.Trait} : M (H := H') unit :=
    let* _ :=
      let* _ :=
        let* α0 :=
          format_arguments::["new_const"]
            (addr_of [ "called `my_mod::indirect_access()`, that
> " ]) in
        std.io.stdio._print α0 in
      Pure tt in
    let* _ := visibility.my_mod.private_function in
    Pure tt.
  
  Module nested.
    Definition function `{H' : State.Trait} : M (H := H') unit :=
      let* _ :=
        let* _ :=
          let* α0 :=
            format_arguments::["new_const"]
              (addr_of [ "called `my_mod::nested::function()`
" ]) in
          std.io.stdio._print α0 in
        Pure tt in
      Pure tt.
    
    (* #[allow(dead_code)] - function was ignored by the compiler *)
    Definition private_function `{H' : State.Trait} : M (H := H') unit :=
      let* _ :=
        let* _ :=
          let* α0 :=
            format_arguments::["new_const"]
              (addr_of [ "called `my_mod::nested::private_function()`
" ]) in
          std.io.stdio._print α0 in
        Pure tt in
      Pure tt.
    
    Definition public_function_in_my_mod
        `{H' : State.Trait}
        : M (H := H') unit :=
      let* _ :=
        let* _ :=
          let* α0 :=
            format_arguments::["new_const"]
              (addr_of
                [
                  "called `my_mod::nested::public_function_in_my_mod()`, that
> "
                ]) in
          std.io.stdio._print α0 in
        Pure tt in
      let* _ := visibility.my_mod.nested.public_function_in_nested in
      Pure tt.
    
    Definition public_function_in_nested
        `{H' : State.Trait}
        : M (H := H') unit :=
      let* _ :=
        let* _ :=
          let* α0 :=
            format_arguments::["new_const"]
              (addr_of
                [ "called `my_mod::nested::public_function_in_nested()`
" ]) in
          std.io.stdio._print α0 in
        Pure tt in
      Pure tt.
    
    Definition public_function_in_super_mod
        `{H' : State.Trait}
        : M (H := H') unit :=
      let* _ :=
        let* _ :=
          let* α0 :=
            format_arguments::["new_const"]
              (addr_of
                [ "called `my_mod::nested::public_function_in_super_mod()`
"
                ]) in
          std.io.stdio._print α0 in
        Pure tt in
      Pure tt.
  End nested.
  
  Definition call_public_function_in_my_mod
      `{H' : State.Trait}
      : M (H := H') unit :=
    let* _ :=
      let* _ :=
        let* α0 :=
          format_arguments::["new_const"]
            (addr_of
              [ "called `my_mod::call_public_function_in_my_mod()`, that
> "
              ]) in
        std.io.stdio._print α0 in
      Pure tt in
    let* _ := visibility.my_mod.nested.public_function_in_my_mod in
    let* _ :=
      let* _ :=
        let* α0 := format_arguments::["new_const"] (addr_of [ "> " ]) in
        std.io.stdio._print α0 in
      Pure tt in
    let* _ := visibility.my_mod.nested.public_function_in_super_mod in
    Pure tt.
  
  Definition public_function_in_crate `{H' : State.Trait} : M (H := H') unit :=
    let* _ :=
      let* _ :=
        let* α0 :=
          format_arguments::["new_const"]
            (addr_of [ "called `my_mod::public_function_in_crate()`
" ]) in
        std.io.stdio._print α0 in
      Pure tt in
    Pure tt.
  
  Module private_nested.
    (* #[allow(dead_code)] - function was ignored by the compiler *)
    Definition function `{H' : State.Trait} : M (H := H') unit :=
      let* _ :=
        let* _ :=
          let* α0 :=
            format_arguments::["new_const"]
              (addr_of [ "called `my_mod::private_nested::function()`
" ]) in
          std.io.stdio._print α0 in
        Pure tt in
      Pure tt.
    
    (* #[allow(dead_code)] - function was ignored by the compiler *)
    Definition restricted_function `{H' : State.Trait} : M (H := H') unit :=
      let* _ :=
        let* _ :=
          let* α0 :=
            format_arguments::["new_const"]
              (addr_of
                [ "called `my_mod::private_nested::restricted_function()`
"
                ]) in
          std.io.stdio._print α0 in
        Pure tt in
      Pure tt.
  End private_nested.
End my_mod.

Definition private_function `{H' : State.Trait} : M (H := H') unit :=
  let* _ :=
    let* _ :=
      let* α0 :=
        format_arguments::["new_const"]
          (addr_of [ "called `my_mod::private_function()`
" ]) in
      std.io.stdio._print α0 in
    Pure tt in
  Pure tt.

Definition function `{H' : State.Trait} : M (H := H') unit :=
  let* _ :=
    let* _ :=
      let* α0 :=
        format_arguments::["new_const"]
          (addr_of [ "called `my_mod::function()`
" ]) in
      std.io.stdio._print α0 in
    Pure tt in
  Pure tt.

Definition indirect_access `{H' : State.Trait} : M (H := H') unit :=
  let* _ :=
    let* _ :=
      let* α0 :=
        format_arguments::["new_const"]
          (addr_of [ "called `my_mod::indirect_access()`, that
> " ]) in
      std.io.stdio._print α0 in
    Pure tt in
  let* _ := visibility.my_mod.private_function in
  Pure tt.

Module nested.
  Definition function `{H' : State.Trait} : M (H := H') unit :=
    let* _ :=
      let* _ :=
        let* α0 :=
          format_arguments::["new_const"]
            (addr_of [ "called `my_mod::nested::function()`
" ]) in
        std.io.stdio._print α0 in
      Pure tt in
    Pure tt.
  
  (* #[allow(dead_code)] - function was ignored by the compiler *)
  Definition private_function `{H' : State.Trait} : M (H := H') unit :=
    let* _ :=
      let* _ :=
        let* α0 :=
          format_arguments::["new_const"]
            (addr_of [ "called `my_mod::nested::private_function()`
" ]) in
        std.io.stdio._print α0 in
      Pure tt in
    Pure tt.
  
  Definition public_function_in_my_mod `{H' : State.Trait} : M (H := H') unit :=
    let* _ :=
      let* _ :=
        let* α0 :=
          format_arguments::["new_const"]
            (addr_of
              [ "called `my_mod::nested::public_function_in_my_mod()`, that
> "
              ]) in
        std.io.stdio._print α0 in
      Pure tt in
    let* _ := visibility.my_mod.nested.public_function_in_nested in
    Pure tt.
  
  Definition public_function_in_nested `{H' : State.Trait} : M (H := H') unit :=
    let* _ :=
      let* _ :=
        let* α0 :=
          format_arguments::["new_const"]
            (addr_of
              [ "called `my_mod::nested::public_function_in_nested()`
" ]) in
        std.io.stdio._print α0 in
      Pure tt in
    Pure tt.
  
  Definition public_function_in_super_mod
      `{H' : State.Trait}
      : M (H := H') unit :=
    let* _ :=
      let* _ :=
        let* α0 :=
          format_arguments::["new_const"]
            (addr_of
              [ "called `my_mod::nested::public_function_in_super_mod()`
" ]) in
        std.io.stdio._print α0 in
      Pure tt in
    Pure tt.
End nested.

Definition function `{H' : State.Trait} : M (H := H') unit :=
  let* _ :=
    let* _ :=
      let* α0 :=
        format_arguments::["new_const"]
          (addr_of [ "called `my_mod::nested::function()`
" ]) in
      std.io.stdio._print α0 in
    Pure tt in
  Pure tt.

(* #[allow(dead_code)] - function was ignored by the compiler *)
Definition private_function `{H' : State.Trait} : M (H := H') unit :=
  let* _ :=
    let* _ :=
      let* α0 :=
        format_arguments::["new_const"]
          (addr_of [ "called `my_mod::nested::private_function()`
" ]) in
      std.io.stdio._print α0 in
    Pure tt in
  Pure tt.

Definition public_function_in_my_mod `{H' : State.Trait} : M (H := H') unit :=
  let* _ :=
    let* _ :=
      let* α0 :=
        format_arguments::["new_const"]
          (addr_of
            [ "called `my_mod::nested::public_function_in_my_mod()`, that
> "
            ]) in
      std.io.stdio._print α0 in
    Pure tt in
  let* _ := visibility.my_mod.nested.public_function_in_nested in
  Pure tt.

Definition public_function_in_nested `{H' : State.Trait} : M (H := H') unit :=
  let* _ :=
    let* _ :=
      let* α0 :=
        format_arguments::["new_const"]
          (addr_of
            [ "called `my_mod::nested::public_function_in_nested()`
" ]) in
      std.io.stdio._print α0 in
    Pure tt in
  Pure tt.

Definition public_function_in_super_mod
    `{H' : State.Trait}
    : M (H := H') unit :=
  let* _ :=
    let* _ :=
      let* α0 :=
        format_arguments::["new_const"]
          (addr_of
            [ "called `my_mod::nested::public_function_in_super_mod()`
" ]) in
      std.io.stdio._print α0 in
    Pure tt in
  Pure tt.

Definition call_public_function_in_my_mod
    `{H' : State.Trait}
    : M (H := H') unit :=
  let* _ :=
    let* _ :=
      let* α0 :=
        format_arguments::["new_const"]
          (addr_of
            [ "called `my_mod::call_public_function_in_my_mod()`, that
> " ]) in
      std.io.stdio._print α0 in
    Pure tt in
  let* _ := visibility.my_mod.nested.public_function_in_my_mod in
  let* _ :=
    let* _ :=
      let* α0 := format_arguments::["new_const"] (addr_of [ "> " ]) in
      std.io.stdio._print α0 in
    Pure tt in
  let* _ := visibility.my_mod.nested.public_function_in_super_mod in
  Pure tt.

Definition public_function_in_crate `{H' : State.Trait} : M (H := H') unit :=
  let* _ :=
    let* _ :=
      let* α0 :=
        format_arguments::["new_const"]
          (addr_of [ "called `my_mod::public_function_in_crate()`
" ]) in
      std.io.stdio._print α0 in
    Pure tt in
  Pure tt.

Module private_nested.
  (* #[allow(dead_code)] - function was ignored by the compiler *)
  Definition function `{H' : State.Trait} : M (H := H') unit :=
    let* _ :=
      let* _ :=
        let* α0 :=
          format_arguments::["new_const"]
            (addr_of [ "called `my_mod::private_nested::function()`
" ]) in
        std.io.stdio._print α0 in
      Pure tt in
    Pure tt.
  
  (* #[allow(dead_code)] - function was ignored by the compiler *)
  Definition restricted_function `{H' : State.Trait} : M (H := H') unit :=
    let* _ :=
      let* _ :=
        let* α0 :=
          format_arguments::["new_const"]
            (addr_of
              [ "called `my_mod::private_nested::restricted_function()`
" ]) in
        std.io.stdio._print α0 in
      Pure tt in
    Pure tt.
End private_nested.

(* #[allow(dead_code)] - function was ignored by the compiler *)
Definition function `{H' : State.Trait} : M (H := H') unit :=
  let* _ :=
    let* _ :=
      let* α0 :=
        format_arguments::["new_const"]
          (addr_of [ "called `my_mod::private_nested::function()`
" ]) in
      std.io.stdio._print α0 in
    Pure tt in
  Pure tt.

(* #[allow(dead_code)] - function was ignored by the compiler *)
Definition restricted_function `{H' : State.Trait} : M (H := H') unit :=
  let* _ :=
    let* _ :=
      let* α0 :=
        format_arguments::["new_const"]
          (addr_of
            [ "called `my_mod::private_nested::restricted_function()`
" ]) in
      std.io.stdio._print α0 in
    Pure tt in
  Pure tt.

Definition function `{H' : State.Trait} : M (H := H') unit :=
  let* _ :=
    let* _ :=
      let* α0 :=
        format_arguments::["new_const"] (addr_of [ "called `function()`
" ]) in
      std.io.stdio._print α0 in
    Pure tt in
  Pure tt.

(* #[allow(dead_code)] - function was ignored by the compiler *)
Definition main `{H' : State.Trait} : M (H := H') unit :=
  let* _ := visibility.function in
  let* _ := visibility.my_mod.function in
  let* _ := visibility.my_mod.indirect_access in
  let* _ := visibility.my_mod.nested.function in
  let* _ := visibility.my_mod.call_public_function_in_my_mod in
  let* _ := visibility.my_mod.public_function_in_crate in
  Pure tt.