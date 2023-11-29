(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Module  Borrowed.
Section Borrowed.
  Record t : Set := {
    x : ref i32.t;
  }.
  
  Global Instance Get_x : Notations.Dot "x" := {
    Notations.dot := Ref.map (fun x' => x'.(x)) (fun v x' => x' <| x := v |>);
  }.
  Global Instance Get_AF_x : Notations.DoubleColon t "x" := {
    Notations.double_colon (x' : M.Val t) := x'.["x"];
  }.
End Borrowed.
End Borrowed.

Module  Impl_core_fmt_Debug_for_scoping_rules_lifetimes_traits_Borrowed_t.
Section Impl_core_fmt_Debug_for_scoping_rules_lifetimes_traits_Borrowed_t.
  Ltac Self := exact scoping_rules_lifetimes_traits.Borrowed.t.
  
  (*
  Debug
  *)
  Parameter fmt :
      (ref ltac:(Self)) ->
        (mut_ref core.fmt.Formatter.t) ->
        M ltac:(core.fmt.Result).
  
  Global Instance AssociatedFunction_fmt :
    Notations.DoubleColon ltac:(Self) "fmt" := {
    Notations.double_colon := fmt;
  }.
  
  Global Instance ℐ : core.fmt.Debug.Trait ltac:(Self) := {
    core.fmt.Debug.fmt := fmt;
  }.
End Impl_core_fmt_Debug_for_scoping_rules_lifetimes_traits_Borrowed_t.
End Impl_core_fmt_Debug_for_scoping_rules_lifetimes_traits_Borrowed_t.

Module  Impl_core_default_Default_for_scoping_rules_lifetimes_traits_Borrowed_t.
Section Impl_core_default_Default_for_scoping_rules_lifetimes_traits_Borrowed_t.
  Ltac Self := exact scoping_rules_lifetimes_traits.Borrowed.t.
  
  (*
      fn default() -> Self {
          Self { x: &10 }
      }
  *)
  Parameter default : M ltac:(Self).
  
  Global Instance AssociatedFunction_default :
    Notations.DoubleColon ltac:(Self) "default" := {
    Notations.double_colon := default;
  }.
  
  Global Instance ℐ : core.default.Default.Trait ltac:(Self) := {
    core.default.Default.default := default;
  }.
End Impl_core_default_Default_for_scoping_rules_lifetimes_traits_Borrowed_t.
End Impl_core_default_Default_for_scoping_rules_lifetimes_traits_Borrowed_t.

(*
fn main() {
    let b: Borrowed = Default::default();
    println!("b is {:?}", b);
}
*)
(* #[allow(dead_code)] - function was ignored by the compiler *)
Parameter main : M unit.