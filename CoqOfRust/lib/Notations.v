Notation "'Sigma' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'Sigma' '/ ' x .. y , '/ ' p ']'")
  : type_scope.
