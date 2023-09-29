Notation "'Sigma' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'Sigma' '/ ' x .. y , '/ ' p ']'")
  : type_scope.


Class supersuperclass (Self : Set) : Type := {}.
Class superclass (Self : Set) `{supersuperclass Self} : Type := {
  some_other_ty : Set;
  some_other_field : some_other_ty;
}.
Class class (Self : Set) `{superclass Self} : Type := {
  some_ty : Set;
  some_field : some_ty;
}.

Class assoc_ty_class (Self : Set) : Type := {
  ty : Set;
  __ty_bound : Sigma `(class ty), unit;
}.
Compute ty.

Definition Ty'' `(assoc_ty_class) : Type.
  unshelve eapply class; try exact (ty (assoc_ty_class := H)); compute; destruct H as [ty __ty_bound'];
repeat (destruct __ty_bound' as [? __ty_bound']; try assumption).
Defined.
Print Ty''.

Definition I'' `{H : assoc_ty_class} : Ty'' H.
compute in *.
  destruct H as [ty __ty_bound'].
  destruct __ty_bound' as [? __ty_bound'].
  destruct __ty_bound' as [? __ty_bound'].
  destruct __ty_bound' as [? __ty_bound'].
  exact x1.
Defined.
Parameter IC' : forall Self `(superclass Self), class Self.
Global Existing Instance IC'.

Section Sec.
  Parameter Self : Set.
  Parameter I''' : forall `{superclass Self}, class Self.
  Global Instance I'''' `(superclass Self) : class Self := I'''.
End Sec.

Parameter function : forall (T : Set) `{C : class T}, Set.

Global Instance I''''' Self `(H : class Self) : class Self := H.

Module Sec'.
Section Sec'.
Context (Self : Set).
Context `(H : class Self).
Global Instance I'''''' : class Self := H.
End Sec'.
End Sec'.

Ltac t n := exact n.
Check ltac:(t tt).

Print Instances class.
Global Hint Resolve I'' : typeclass_instances.

Ltac t' H :=   unshelve eapply class; try exact (ty (assoc_ty_class := H)); compute; destruct H as [ty __ty_bound'];
repeat (destruct __ty_bound' as [? __ty_bound']; try assumption).

Check fun `(H : assoc_ty_class) => ltac:(t' H).
Global Instance II `(H : assoc_ty_class) : ltac:(t' H) := I''.
Global Hint Resolve II : typeclass_instances.
Print II.
Check II ?[H] : class ty.
Print function.

Print Instances class.

Section s.
Context `(H : assoc_ty_class).

Definition T : Set := ty.
Global Instance GI : ltac:(unshelve eapply class; try exact (ty (assoc_ty_class := H)); compute; destruct H;
repeat (destruct __ty_bound0 as [? __ty_bound0]; try assumption)).
compute. destruct H.
repeat (destruct __ty_bound0 as [? __ty_bound0]). assumption.
Defined.
Print GI.

Parameter f : forall x `{class x}, Set.
(* Parameter x : f T. *)

Print Instances superclass.
End s.

(* Definition T : Set := ty. *)

(* I'm trying to make this work  v *)
(*           ____________________| *)
(*        vvv                      *)
Parameter obj : forall `{H : assoc_ty_class}, function (ty (assoc_ty_class := H)).

Section X.
Context `(H : assoc_ty_class).
Definition S : Type.
  destruct H as [ty __ty_bound].
  repeat
  (destruct __ty_bound as [? __ty_bound];
  try apply (class ty)).
Defined.
Compute S.

Definition S' : Sigma T : Type, T.
  destruct H as [ty __ty_bound'].
  destruct __ty_bound' as [? __ty_bound'].
  destruct __ty_bound' as [? __ty_bound'].
  destruct __ty_bound' as [? __ty_bound'].
  eapply existT.
  exact x1.
Defined.

(* Global Instance I : S.
 *)
Compute S'.
Compute projT2 S'.
Compute projT1 S'.
End X.
Compute fun `(H : assoc_ty_class) => (fun '({| ty := x; __ty_bound := y |}) => projT1 (S' {| ty := x; __ty_bound := y |})) H.
Compute fun '({| ty := x; __ty_bound := y |}) => projT1 (S' {| ty := x; __ty_bound := y |}).
Compute fun `(H : assoc_ty_class) => projT1 (S' H).

Check fun '({| ty := x; __ty_bound := y |}) => {| ty := x; __ty_bound := y |}.
Compute (fun `(H : assoc_ty_class) => let '{| ty := x; __ty_bound := y |} := H in
  (projT2 (S' {| ty := x; __ty_bound := y |}) : projT1 (S' {| ty := x; __ty_bound := y |})))
  : forall `(H : assoc_ty_class), let '{| ty := x; __ty_bound := y |} := H in projT1 (S' {| ty := x; __ty_bound := y |}).
Compute fun `(H : assoc_ty_class) => projT2 (S' H).

Definition Ty `(H : assoc_ty_class) : Type.
  unshelve eapply function.
  - exact ty.
  - destruct H. now compute.
  - destruct H. now compute.
  - destruct H. now compute.
Defined.
Compute Ty.

Definition Ty' `(H : assoc_ty_class) : Type.
  unshelve eapply (another_class ty).
  - exact Self.
  - easy.
  - easy.
  - easy.
  - easy.
Defined.
Print Ty'.

(*   apply (fun `(H : assoc_ty_class) (x : forall (T : Set) `(H : assoc_ty_class), Type) => forall (T : Set) `(H : assoc_ty_class), x T H) with Self.
Defined. *)

Parameter object' : forall (T : Set) `(H : assoc_ty_class), Ty H.
Compute object'.

Definition I' `(H : assoc_ty_class) : Ty' H.
  easy.
Defined.

Parameter object : forall (T : Set) `(H : assoc_ty_class),
  let '{| ty := x; __ty_bound := y |} := H in function ty (C := projT2 (S' {| ty := x; __ty_bound := y |})).

(* Goal forall `(H : assoc_ty_class), let '{| ty := x; __ty_bound := y |} := H in projT1 (S' H) = class x. *)
(* intros. compute. destruct H. destruct __ty_bound0. destruct s. destruct s. *)
Parameter object : forall '({| ty := x; __ty_bound := y |}), function x (C := projT2 (S' {| ty := x; __ty_bound := y |})).

Check fun '({| ty := x; __ty_bound := y |}) => {| ty := x; __ty_bound := y |}.
Compute fun '({| ty := x; __ty_bound := y |}) => (projT2 (S' {| ty := x; __ty_bound := y |}) : projT1 (S' {| ty := x; __ty_bound := y |})).
Compute fun `(H : assoc_ty_class) => projT2 (S' H).

Parameter object : forall (T : Set) '({| ty := x; __ty_bound := y |}), function ty (C := projT1 (projT2 (S' {| ty := x; __ty_bound := y |}))).
