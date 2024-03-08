Require Import CoqOfRust.CoqOfRust.

Module  Mapping.
Section Mapping.
  Parameter t : Set -> Set -> Set.

  Context {K V : Set}.

  Parameter empty : t K V.
  Parameter get : K -> t K V -> option.Option.t V.
  Parameter insert : K -> V -> t K V -> t K V.
  Parameter sum : (V -> Z) -> t K V -> Z.
  Parameter remove : K -> t K V -> t K V.
End Mapping.
End Mapping.

Module  Impl_core_default_Default_for_lib_Mapping_t_K_V.
Section Impl_core_default_Default_for_lib_Mapping_t_K_V.
  Context {K V : Set}.
  
  Context
    {ℋ_0 : core.default.Default.Trait K}
    {ℋ_1 : core.default.Default.Trait V}.
  
  Definition Self : Set := Mapping.t K V.
  
  Definition default : M (Mapping.t K V) :=
    M.pure Mapping.empty.
  
  Global Instance AssociatedFunction_default :
    Notations.DoubleColon Self "default" := {
    Notations.double_colon := default;
  }.
  
  Global Instance ℐ : core.default.Default.Trait Self := {
    core.default.Default.default := default;
  }.
End Impl_core_default_Default_for_lib_Mapping_t_K_V.
End Impl_core_default_Default_for_lib_Mapping_t_K_V.

Module  Impl_Mapping_t_K_V.
Section Impl_Mapping_t_K_V.
  Context {K V : Set}.
  
  Definition Self : Set := Mapping.t K V.
  
  Definition get
      (self : ref Self)
      (key : ref K)
      : M (core.option.Option.t V) :=
    let* self : Self := M.read self in
    let* key : K := M.read key in
    M.pure (Mapping.get key self).
  
  Global Instance AssociatedFunction_get :
    Notations.DoubleColon Self "get" := {
    Notations.double_colon := get;
  }.
  
  Definition contains
      (self : ref Self)
      (key : ref K)
      : M bool.t :=
    let* self : Self := M.read self in
    let* key : K := M.read key in
    M.pure (
      match Mapping.get key self with
      | option.Option.Some _ => true
      | option.Option.None => false
      end
    ).

  Global Instance AssociatedFunction_contains :
    Notations.DoubleColon Self "contains" := {
    Notations.double_colon := contains;
  }.

  Definition insert
      (self : mut_ref Self)
      (key : K)
      (value : V)
      : M unit :=
    let* self_content := M.read self in
    let new_self := Mapping.insert key value self_content in
    let* _ := assign self new_self in
    M.pure tt.
  
  Global Instance AssociatedFunction_insert :
    Notations.DoubleColon Self "insert" := {
    Notations.double_colon := insert;
  }.

  Definition remove
      (self : ref Self)
      (key : K)
      : M unit :=
    let* self_content : Self := M.read self in
    let new_self := Mapping.remove key self_content in
    let* _ := assign self new_self in
    M.pure tt.
  
  Global Instance AssociatedFunction_remove :
    Notations.DoubleColon Self "remove" := {
    Notations.double_colon := remove;
  }.
End Impl_Mapping_t_K_V.
End Impl_Mapping_t_K_V.
