(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

(*
Enum VeryVerboseEnumOfThingsToDoWithNumbers
{
  const_params := [];
  ty_params := [];
  variants :=
    [
      {
        name := "Add";
        item := StructTuple [];
      };
      {
        name := "Subtract";
        item := StructTuple [];
      }
    ];
}
*)

Axiom IsDiscriminant_VeryVerboseEnumOfThingsToDoWithNumbers_Add :
  M.IsDiscriminant "enums_type_aliases_v1::VeryVerboseEnumOfThingsToDoWithNumbers::Add" 0.
Axiom IsDiscriminant_VeryVerboseEnumOfThingsToDoWithNumbers_Subtract :
  M.IsDiscriminant "enums_type_aliases_v1::VeryVerboseEnumOfThingsToDoWithNumbers::Subtract" 1.

Axiom Operations :
  (Ty.path "enums_type_aliases_v1::Operations") =
    (Ty.path "enums_type_aliases_v1::VeryVerboseEnumOfThingsToDoWithNumbers").

(*
fn main() {
    // We can refer to each variant via its alias, not its long and inconvenient
    // name.
    let x = Operations::Add;
}
*)
Definition main (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
  match ε, τ, α with
  | [], [], [] =>
    ltac:(M.monadic
      (M.read (|
        let~ x : Ty.path "enums_type_aliases_v1::VeryVerboseEnumOfThingsToDoWithNumbers" :=
          Value.StructTuple
            "enums_type_aliases_v1::VeryVerboseEnumOfThingsToDoWithNumbers::Add"
            []
            []
            [] in
        M.alloc (| Ty.tuple [], Value.Tuple [] |)
      |)))
  | _, _, _ => M.impossible "wrong number of arguments"
  end.

Global Instance Instance_IsFunction_main : M.IsFunction.C "enums_type_aliases_v1::main" main.
Admitted.
Global Typeclasses Opaque main.
