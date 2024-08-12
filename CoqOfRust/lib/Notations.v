Notation "'Sigma' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'Sigma' '/ ' x .. y , '/ ' p ']'")
  : type_scope.

(* NOTE: strange that this file is completely ignored. I decide to comment out 
this notation in case there are better places to place the notations *)
(* Notation "f $ x" := (f x) (at level 60, right associativity, only parsing). *)