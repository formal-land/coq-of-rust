(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Module  Incrementer.
Section Incrementer.
  Record t : Set := {
    value : i32.t;
  }.
  
  Global Instance Get_value : Notations.Dot "value" := {
    Notations.dot :=
      Ref.map (fun x => x.(value)) (fun v x => x <| value := v |>);
  }.
  Global Instance Get_AF_value : Notations.DoubleColon t "value" := {
    Notations.double_colon (x : M.Val t) := x.["value"];
  }.
End Incrementer.
End Incrementer.

Module  Impl_incrementer_Incrementer_t.
Section Impl_incrementer_Incrementer_t.
  Ltac Self := exact incrementer.Incrementer.t.
  
  (*
      pub fn new(init_value: i32) -> Self {
          Self { value: init_value }
      }
  *)
  Definition new (init_value : i32.t) : M ltac:(Self) :=
    let* init_value : M.Val i32.t := M.alloc init_value in
    let* α0 : i32.t := M.read init_value in
    M.pure {| incrementer.Incrementer.value := α0; |}.
  
  Global Instance AssociatedFunction_new :
    Notations.DoubleColon ltac:(Self) "new" := {
    Notations.double_colon := new;
  }.
  
  (*
      pub fn new_default() -> Self {
          Self::new(Default::default())
      }
  *)
  Definition new_default : M ltac:(Self) :=
    let* α0 : i32.t :=
      M.call
        (core.default.Default.default
          (Self := i32.t)
          (Trait := ltac:(refine _))) in
    M.call (incrementer.Incrementer.t::["new"] α0).
  
  Global Instance AssociatedFunction_new_default :
    Notations.DoubleColon ltac:(Self) "new_default" := {
    Notations.double_colon := new_default;
  }.
  
  (*
      pub fn inc(&mut self, by: i32) {
          self.value += by;
      }
  *)
  Definition inc (self : mut_ref ltac:(Self)) (by : i32.t) : M unit :=
    let* self : M.Val (mut_ref ltac:(Self)) := M.alloc self in
    let* by : M.Val i32.t := M.alloc by in
    let* _ : M.Val unit :=
      let* α0 : mut_ref incrementer.Incrementer.t := M.read self in
      assign_op BinOp.Panic.add (deref α0).["value"] by in
    let* α0 : M.Val unit := M.alloc tt in
    M.read α0.
  
  Global Instance AssociatedFunction_inc :
    Notations.DoubleColon ltac:(Self) "inc" := {
    Notations.double_colon := inc;
  }.
  
  (*
      pub fn get(&self) -> i32 {
          self.value
      }
  *)
  Definition get (self : ref ltac:(Self)) : M i32.t :=
    let* self : M.Val (ref ltac:(Self)) := M.alloc self in
    let* α0 : ref incrementer.Incrementer.t := M.read self in
    M.read (deref α0).["value"].
  
  Global Instance AssociatedFunction_get :
    Notations.DoubleColon ltac:(Self) "get" := {
    Notations.double_colon := get;
  }.
End Impl_incrementer_Incrementer_t.
End Impl_incrementer_Incrementer_t.