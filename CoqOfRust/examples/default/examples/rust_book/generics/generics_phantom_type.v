(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Module  PhantomTuple.
Section PhantomTuple.
  Context {A B : Set}.
  
  Record t : Set := {
    x0 : A;
    x1 : core.marker.PhantomData.t B;
  }.
  
  Definition Get_0 :=
    Ref.map (fun α => Some α.(x0)) (fun β α => Some (α <| x0 := β |>)).
  Definition Get_1 :=
    Ref.map (fun α => Some α.(x1)) (fun β α => Some (α <| x1 := β |>)).
End PhantomTuple.
End PhantomTuple.

Module  Impl_core_marker_StructuralPartialEq_for_generics_phantom_type_PhantomTuple_t_A_B.
Section Impl_core_marker_StructuralPartialEq_for_generics_phantom_type_PhantomTuple_t_A_B.
  Context {A B : Set}.
  
  Definition Self : Set := generics_phantom_type.PhantomTuple.t A B.
  
  Global Instance ℐ : core.marker.StructuralPartialEq.Trait Self := {
  }.
End Impl_core_marker_StructuralPartialEq_for_generics_phantom_type_PhantomTuple_t_A_B.
End Impl_core_marker_StructuralPartialEq_for_generics_phantom_type_PhantomTuple_t_A_B.

Module  Impl_core_cmp_PartialEq_for_generics_phantom_type_PhantomTuple_t_A_B.
Section Impl_core_cmp_PartialEq_for_generics_phantom_type_PhantomTuple_t_A_B.
  Context {A B : Set}.
  
  Context
    {ℋ_0 : core.cmp.PartialEq.Trait A (Rhs := core.cmp.PartialEq.Default.Rhs A)}
    {ℋ_1 :
      core.cmp.PartialEq.Trait B (Rhs := core.cmp.PartialEq.Default.Rhs B)}.
  
  Definition Self : Set := generics_phantom_type.PhantomTuple.t A B.
  
  (*
  PartialEq
  *)
  Definition eq
      (self : ref Self)
      (other : ref (generics_phantom_type.PhantomTuple.t A B))
      : M bool.t :=
    let* self := M.alloc self in
    let* other := M.alloc other in
    let* α0 : (ref A) -> (ref A) -> M bool.t :=
      ltac:(M.get_method (fun ℐ =>
        core.cmp.PartialEq.eq (Self := A) (Rhs := A) (Trait := ℐ))) in
    let* α1 : ref (generics_phantom_type.PhantomTuple.t A B) := M.read self in
    let* α2 : ref (generics_phantom_type.PhantomTuple.t A B) := M.read other in
    let* α3 : bool.t :=
      M.call
        (α0
          (borrow (generics_phantom_type.PhantomTuple.Get_0 (deref α1)))
          (borrow (generics_phantom_type.PhantomTuple.Get_0 (deref α2)))) in
    let* α4 :
        (ref (core.marker.PhantomData.t B)) ->
          (ref (core.marker.PhantomData.t B)) ->
          M bool.t :=
      ltac:(M.get_method (fun ℐ =>
        core.cmp.PartialEq.eq
          (Self := core.marker.PhantomData.t B)
          (Rhs := core.marker.PhantomData.t B)
          (Trait := ℐ))) in
    let* α5 : ref (generics_phantom_type.PhantomTuple.t A B) := M.read self in
    let* α6 : ref (generics_phantom_type.PhantomTuple.t A B) := M.read other in
    let* α7 : bool.t :=
      M.call
        (α4
          (borrow (generics_phantom_type.PhantomTuple.Get_1 (deref α5)))
          (borrow (generics_phantom_type.PhantomTuple.Get_1 (deref α6)))) in
    M.pure (BinOp.Pure.and α3 α7).
  
  Global Instance AssociatedFunction_eq : Notations.DoubleColon Self "eq" := {
    Notations.double_colon := eq;
  }.
  
  Global Instance ℐ :
    core.cmp.PartialEq.Required.Trait Self
      (Rhs := core.cmp.PartialEq.Default.Rhs Self) := {
    core.cmp.PartialEq.eq := eq;
    core.cmp.PartialEq.ne := Datatypes.None;
  }.
End Impl_core_cmp_PartialEq_for_generics_phantom_type_PhantomTuple_t_A_B.
End Impl_core_cmp_PartialEq_for_generics_phantom_type_PhantomTuple_t_A_B.

Module  PhantomStruct.
Section PhantomStruct.
  Context (A B : Set).
  
  Record t : Set := {
    first : A;
    phantom : core.marker.PhantomData.t B;
  }.
  
  Definition Get_first :=
    Ref.map (fun α => Some α.(first)) (fun β α => Some (α <| first := β |>)).
  Definition Get_phantom :=
    Ref.map
      (fun α => Some α.(phantom))
      (fun β α => Some (α <| phantom := β |>)).
End PhantomStruct.
End PhantomStruct.

Module  Impl_core_marker_StructuralPartialEq_for_generics_phantom_type_PhantomStruct_t_A_B.
Section Impl_core_marker_StructuralPartialEq_for_generics_phantom_type_PhantomStruct_t_A_B.
  Context {A B : Set}.
  
  Definition Self : Set := generics_phantom_type.PhantomStruct.t A B.
  
  Global Instance ℐ : core.marker.StructuralPartialEq.Trait Self := {
  }.
End Impl_core_marker_StructuralPartialEq_for_generics_phantom_type_PhantomStruct_t_A_B.
End Impl_core_marker_StructuralPartialEq_for_generics_phantom_type_PhantomStruct_t_A_B.

Module  Impl_core_cmp_PartialEq_for_generics_phantom_type_PhantomStruct_t_A_B.
Section Impl_core_cmp_PartialEq_for_generics_phantom_type_PhantomStruct_t_A_B.
  Context {A B : Set}.
  
  Context
    {ℋ_0 : core.cmp.PartialEq.Trait A (Rhs := core.cmp.PartialEq.Default.Rhs A)}
    {ℋ_1 :
      core.cmp.PartialEq.Trait B (Rhs := core.cmp.PartialEq.Default.Rhs B)}.
  
  Definition Self : Set := generics_phantom_type.PhantomStruct.t A B.
  
  (*
  PartialEq
  *)
  Definition eq
      (self : ref Self)
      (other : ref (generics_phantom_type.PhantomStruct.t A B))
      : M bool.t :=
    let* self := M.alloc self in
    let* other := M.alloc other in
    let* α0 : (ref A) -> (ref A) -> M bool.t :=
      ltac:(M.get_method (fun ℐ =>
        core.cmp.PartialEq.eq (Self := A) (Rhs := A) (Trait := ℐ))) in
    let* α1 : ref (generics_phantom_type.PhantomStruct.t A B) := M.read self in
    let* α2 : ref (generics_phantom_type.PhantomStruct.t A B) := M.read other in
    let* α3 : bool.t :=
      M.call
        (α0
          (borrow (generics_phantom_type.PhantomStruct.Get_first (deref α1)))
          (borrow
            (generics_phantom_type.PhantomStruct.Get_first (deref α2)))) in
    let* α4 :
        (ref (core.marker.PhantomData.t B)) ->
          (ref (core.marker.PhantomData.t B)) ->
          M bool.t :=
      ltac:(M.get_method (fun ℐ =>
        core.cmp.PartialEq.eq
          (Self := core.marker.PhantomData.t B)
          (Rhs := core.marker.PhantomData.t B)
          (Trait := ℐ))) in
    let* α5 : ref (generics_phantom_type.PhantomStruct.t A B) := M.read self in
    let* α6 : ref (generics_phantom_type.PhantomStruct.t A B) := M.read other in
    let* α7 : bool.t :=
      M.call
        (α4
          (borrow (generics_phantom_type.PhantomStruct.Get_phantom (deref α5)))
          (borrow
            (generics_phantom_type.PhantomStruct.Get_phantom (deref α6)))) in
    M.pure (BinOp.Pure.and α3 α7).
  
  Global Instance AssociatedFunction_eq : Notations.DoubleColon Self "eq" := {
    Notations.double_colon := eq;
  }.
  
  Global Instance ℐ :
    core.cmp.PartialEq.Required.Trait Self
      (Rhs := core.cmp.PartialEq.Default.Rhs Self) := {
    core.cmp.PartialEq.eq := eq;
    core.cmp.PartialEq.ne := Datatypes.None;
  }.
End Impl_core_cmp_PartialEq_for_generics_phantom_type_PhantomStruct_t_A_B.
End Impl_core_cmp_PartialEq_for_generics_phantom_type_PhantomStruct_t_A_B.

(*
fn main() {
    // Here, `f32` and `f64` are the hidden parameters.
    // PhantomTuple type specified as `<char, f32>`.
    let _tuple1: PhantomTuple<char, f32> = PhantomTuple('Q', PhantomData);
    // PhantomTuple type specified as `<char, f64>`.
    let _tuple2: PhantomTuple<char, f64> = PhantomTuple('Q', PhantomData);

    // Type specified as `<char, f32>`.
    let _struct1: PhantomStruct<char, f32> = PhantomStruct {
        first: 'Q',
        phantom: PhantomData,
    };
    // Type specified as `<char, f64>`.
    let _struct2: PhantomStruct<char, f64> = PhantomStruct {
        first: 'Q',
        phantom: PhantomData,
    };

    // Compile-time Error! Type mismatch so these cannot be compared:
    // println!("_tuple1 == _tuple2 yields: {}",
    //           _tuple1 == _tuple2);

    // Compile-time Error! Type mismatch so these cannot be compared:
    // println!("_struct1 == _struct2 yields: {}",
    //           _struct1 == _struct2);
}
*)
(* #[allow(dead_code)] - function was ignored by the compiler *)
Definition main : M unit :=
  let* _tuple1 : M.Val (generics_phantom_type.PhantomTuple.t char.t f32.t) :=
    M.alloc
      (generics_phantom_type.PhantomTuple.Build_t
        "Q"%char
        core.marker.PhantomData.Build) in
  let* _tuple2 : M.Val (generics_phantom_type.PhantomTuple.t char.t f64.t) :=
    M.alloc
      (generics_phantom_type.PhantomTuple.Build_t
        "Q"%char
        core.marker.PhantomData.Build) in
  let* _struct1 : M.Val (generics_phantom_type.PhantomStruct.t char.t f32.t) :=
    M.alloc
      {|
        generics_phantom_type.PhantomStruct.first := "Q"%char;
        generics_phantom_type.PhantomStruct.phantom :=
          core.marker.PhantomData.Build;
      |} in
  let* _struct2 : M.Val (generics_phantom_type.PhantomStruct.t char.t f64.t) :=
    M.alloc
      {|
        generics_phantom_type.PhantomStruct.first := "Q"%char;
        generics_phantom_type.PhantomStruct.phantom :=
          core.marker.PhantomData.Build;
      |} in
  let* α0 : M.Val unit := M.alloc tt in
  M.read α0.