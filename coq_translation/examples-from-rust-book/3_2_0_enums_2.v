Error Enum.

Definition run :=
  match self with Add => add x y Subtract => sub x y end.

Error TyAlias.

Definition main :=
  let x := Add in
  tt.