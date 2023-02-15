Error Enum.

(* Impl [VeryVerboseEnumOfThingsToDoWithNumbers] *)
Module VeryVerboseEnumOfThingsToDoWithNumbers.
  Definition run (self : ref Self) (x : i32) (y : i32) : i32 :=
    match self with
    | Self.Add => add x y
    | Self.Subtract => sub x y
    end.
End VeryVerboseEnumOfThingsToDoWithNumbers.
(* End impl [VeryVerboseEnumOfThingsToDoWithNumbers] *)

Error TyAlias.

Definition main (_ : unit) :=
  let x := Operations.Add in
  tt.