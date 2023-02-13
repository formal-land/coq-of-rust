Error Enum.

(* Impl [VeryVerboseEnumOfThingsToDoWithNumbers] *)
  Definition run (self : ref Self) (x : i32) (y : i32) : i32 :=
    match self with
    | Add => add x y
    | Subtract => sub x y
    end.
(* End impl [VeryVerboseEnumOfThingsToDoWithNumbers] *)

Error TyAlias.

Definition main :=
  let x := Add in
  tt.