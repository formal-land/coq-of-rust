(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Import Root.std.prelude.rust_2015.

Error StructUnit.

Error StructUnit.

Module DoubleDrop.
  Class Class (T Self : Set) : Set := {
    double_drop : Self -> (T -> _);
  }.
  
  Global Instance Method_double_drop `(Class) : Method "double_drop" _ := {|
    method := double_drop;
  |}.
  Class AssociatedFunction (name : string) (T : Set) : Set := {
    associated_function : T;
  }.
  Arguments associated_function name {T AssociatedFunction}.
End DoubleDrop.

Module Impl_DoubleDrop_for_U.
  Definition Self := U.
  
  Definition double_drop (self : Self) (Pattern : T) := tt.
  
  Global Instance M_double_drop : Method "double_drop" _ := {|
    method := double_drop;
  |}.
  Global Instance AF_double_drop : U.AssociatedFunction "double_drop" _ := {|
    U.associated_function := double_drop;
  |}.
  Global Instance
    AFT_double_drop
    :
    DoubleDrop.AssociatedFunction
    "double_drop"
    _
    :=
    {|
    DoubleDrop.associated_function := double_drop;
  |}.
  
  Global Instance I T U : DoubleDrop.Class T Self := {|
    DoubleDrop.double_drop := double_drop;
  |}.
End Impl_DoubleDrop_for_U.

Definition main (_ : unit) : unit :=
  let empty := Empty in
  let null := Null in
  method "double_drop" empty null ;;
  tt.
