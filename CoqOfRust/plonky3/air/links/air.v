Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.links.array.
Require Import core.convert.links.mod.
Require Import core.ops.links.arith.
Require Import core.links.option.
Require Import plonky3.air.air.
Require Import plonky3.field.links.field.
Require Import plonky3.matrix.links.dense.
Require Import plonky3.matrix.links.lib.

(* 
pub trait BaseAir<F>: Sync {
    /// The number of columns (a.k.a. registers) in this AIR.
    fn width(&self) -> usize;

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        None
    }
}
*)
Module BaseAir.
  Module AssociatedTypes.
    Record t : Type := {
      F : Set;
    }.

    Class AreLinks (types : t) : Set := {
      H_F : Link types.(F);
    }.

    Global Instance IsLinkF (types : t) (H : AreLinks types) : Link types.(F) :=
      H.(H_F _).
  End AssociatedTypes.

  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("p3_air::air::BaseAir", [], [], Φ Self).

  (* fn width(&self) -> usize; *)
  Definition Run_width
    (Self : Set) `{Link Self} 
    (types : AssociatedTypes.t) `{AssociatedTypes.AreLinks types} :
    Set :=
  TraitMethod.C (trait Self) "width" (fun method =>
    forall (self : Ref.t Pointer.Kind.Ref Self),
    Run.Trait method [] [] [ φ self ] Usize.t
  ).

  (* fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> *)
  Definition Run_preprocessed_trace
    (Self : Set) `{Link Self} 
    (types : AssociatedTypes.t) `{AssociatedTypes.AreLinks types} :
    Set :=
  TraitMethod.C (trait Self) "preprocessed_trace" (fun method =>
    forall (self : Ref.t Pointer.Kind.Ref Self),
    Run.Trait method [] [] [ φ self ] (option (RowMajorMatrix.t types.(AssociatedTypes.F)))
  ).

  Class Run (Self : Set) `{Link Self} 
  (types : AssociatedTypes.t) `{AssociatedTypes.AreLinks types} : Set := {
    (* Note: F : Sync is ignored *)
    F_IsAssociated :
      IsTraitAssociatedType
        "p3_air::air::AirBuilder" [] [] (Φ Self)
        "F" (Φ types.(AssociatedTypes.F));
    width : Run_width Self types;
    preprocessed_trace : Run_preprocessed_trace Self types;
  }.
End BaseAir.

(*
pub struct FilteredAirBuilder<'a, AB: AirBuilder> {
    pub inner: &'a mut AB,
    condition: AB::Expr,
}
*)
Module FilteredAirBuilder.
  (** As the [AirBuilder] is defined after, we require to explicitly provide the [Expr] type. *)
  Record t {AB Expr : Set} `{Link AB} : Set := {
    inner : Ref.t Pointer.Kind.MutRef AB;
    condition : Expr;
  }.
  Arguments t _ _ {_}.

  Global Instance IsLink (AB Expr : Set) `{Link AB} `{Link Expr} : Link (t AB Expr) := {
    Φ := Ty.apply (Ty.path "p3_air::air::FilteredAirBuilder") [] [Φ AB];
    φ x :=
      Value.StructRecord "p3_air::air::FilteredAirBuilder" [] [Φ AB] [
        ("inner", φ x.(inner));
        ("condition", φ x.(condition))
      ];
  }.
End FilteredAirBuilder.

(*
pub trait AirBuilder: Sized {
    type F: Field;
    type Expr: Algebra<Self::F> + Algebra<Self::Var>;
    type Var: Into<Self::Expr>
        + Copy
        + Send
        + Sync
        + Add<Self::F, Output = Self::Expr>
        + Add<Self::Var, Output = Self::Expr>
        + Add<Self::Expr, Output = Self::Expr>
        + Sub<Self::F, Output = Self::Expr>
        + Sub<Self::Var, Output = Self::Expr>
        + Sub<Self::Expr, Output = Self::Expr>
        + Mul<Self::F, Output = Self::Expr>
        + Mul<Self::Var, Output = Self::Expr>
        + Mul<Self::Expr, Output = Self::Expr>;
    type M: Matrix<Self::Var>;
}
*)
Module AirBuilder.
  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("p3_air::air::AirBuilder", [], [], Φ Self).

  Module AssociatedTypes.
    Record t : Type := {
      F : Set;
      Expr : Set;
      Var : Set;
      M : Set;
      M_types : Matrix.AssociatedTypes.t;
    }.

    Class AreLinks (types : t) : Set := {
      H_F : Link types.(F);
      H_Expr : Link types.(Expr);
      H_Var : Link types.(Var);
      H_M : Link types.(M);
      H_M_types : Matrix.AssociatedTypes.AreLinks types.(M_types);
    }.

    Global Instance IsLinkF (types : t) (H : AreLinks types) : Link types.(F) :=
      H.(H_F _).
    Global Instance IsLinkExpr (types : t) (H : AreLinks types) : Link types.(Expr) :=
      H.(H_Expr _).
    Global Instance IsLinkVar (types : t) (H : AreLinks types) : Link types.(Var) :=
      H.(H_Var _).
    Global Instance IsLinkM (types : t) (H : AreLinks types) : Link types.(M) :=
      H.(H_M _).
    Global Instance AreLinksM_types (types : t) (H : AreLinks types) :
      Matrix.AssociatedTypes.AreLinks types.(M_types) :=
      H.(H_M_types _).
  End AssociatedTypes.

  (* fn main(&self) -> Self::M; *)
  Definition Run_main
      (Self : Set) `{Link Self}
      (types : AssociatedTypes.t) `{AssociatedTypes.AreLinks types} :
      Set :=
    TraitMethod.C (trait Self) "main" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] types.(AssociatedTypes.M)
    ).

  (* fn is_first_row(&self) -> Self::Expr; *)
  Definition Run_is_first_row
      (Self : Set) `{Link Self}
      (types : AssociatedTypes.t) `{AssociatedTypes.AreLinks types} :
      Set :=
    TraitMethod.C (trait Self) "is_first_row" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] types.(AssociatedTypes.Expr)
    ).

  (* fn is_last_row(&self) -> Self::Expr; *)
  Definition Run_is_last_row
      (Self : Set) `{Link Self}
      (types : AssociatedTypes.t) `{AssociatedTypes.AreLinks types} :
      Set :=
    TraitMethod.C (trait Self) "is_last_row" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] types.(AssociatedTypes.Expr)
    ).

  (* fn is_transition(&self) -> Self::Expr; *)
  Definition Run_is_transition
      (Self : Set) `{Link Self}
      (types : AssociatedTypes.t) `{AssociatedTypes.AreLinks types} :
      Set :=
    TraitMethod.C (trait Self) "is_transition" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] types.(AssociatedTypes.Expr)
    ).

  (* fn is_transition_window(&self, size: usize) -> Self::Expr; *)
  Definition Run_is_transition_window
      (Self : Set) `{Link Self}
      (types : AssociatedTypes.t) `{AssociatedTypes.AreLinks types} :
      Set :=
    TraitMethod.C (trait Self) "is_transition_window" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self) (size : Usize.t),
      Run.Trait method [] [] [ φ self; φ size ] types.(AssociatedTypes.Expr)
    ).

  (* fn when<I: Into<Self::Expr>>(&mut self, condition: I) -> FilteredAirBuilder<'_, Self>; *)
  Definition Run_when
      (Self : Set) `{Link Self}
      (types : AssociatedTypes.t) `{AssociatedTypes.AreLinks types} :
      Set :=
    TraitMethod.C (trait Self) "when" (fun method =>
      forall
        (I : Set) `(Link I)
        (run_Into_for_I : Into.Run I types.(AssociatedTypes.Expr))
        (self : Ref.t Pointer.Kind.MutRef Self)
        (condition : I),
      Run.Trait method [] [Φ I] [ φ self; φ condition ]
        (FilteredAirBuilder.t Self types.(AssociatedTypes.Expr))
    ).

  (* 
  fn when_ne<I1: Into<Self::Expr>, I2: Into<Self::Expr>>(
      &mut self,
      x: I1,
      y: I2,
  ) -> FilteredAirBuilder<'_, Self>;
  *)
  Definition Run_when_ne
      (Self : Set) `{Link Self}
      (types : AssociatedTypes.t) `{AssociatedTypes.AreLinks types} :
      Set :=
    TraitMethod.C (trait Self) "when_ne" (fun method =>
      forall
        (I1 I2 : Set) `(Link I1) `(Link I2)
        (run_Into_for_I1 : Into.Run I1 types.(AssociatedTypes.Expr))
        (run_Into_for_I2 : Into.Run I2 types.(AssociatedTypes.Expr))
        (self : Ref.t Pointer.Kind.Ref Self)
        (x y : I1),
      Run.Trait method [] [Φ I1; Φ I2] [ φ self; φ x; φ y ]
        (FilteredAirBuilder.t Self types.(AssociatedTypes.Expr))
    ).

  (* fn when_first_row(&mut self) -> FilteredAirBuilder<'_, Self>; *)
  Definition Run_when_first_row
      (Self : Set) `{Link Self}
      (types : AssociatedTypes.t) `{AssociatedTypes.AreLinks types} :
      Set :=
    TraitMethod.C (trait Self) "when_first_row" (fun method =>
      forall (self : Ref.t Pointer.Kind.MutRef Self),
      Run.Trait method [] [] [ φ self ] (FilteredAirBuilder.t Self types.(AssociatedTypes.Expr))
    ).

  (* fn when_last_row(&mut self) -> FilteredAirBuilder<'_, Self>; *)
  Definition Run_when_last_row
      (Self : Set) `{Link Self}
      (types : AssociatedTypes.t) `{AssociatedTypes.AreLinks types} :
      Set :=
    TraitMethod.C (trait Self) "when_last_row" (fun method =>
      forall (self : Ref.t Pointer.Kind.MutRef Self),
      Run.Trait method [] [] [ φ self ] (FilteredAirBuilder.t Self types.(AssociatedTypes.Expr))
    ).

  (* fn when_transition(&mut self) -> FilteredAirBuilder<'_, Self>; *)
  Definition Run_when_transition
      (Self : Set) `{Link Self}
      (types : AssociatedTypes.t) `{AssociatedTypes.AreLinks types} :
      Set :=
    TraitMethod.C (trait Self) "when_transition" (fun method =>
      forall (self : Ref.t Pointer.Kind.MutRef Self),
      Run.Trait method [] [] [ φ self ] (FilteredAirBuilder.t Self types.(AssociatedTypes.Expr))
    ).

  (* fn when_transition_window(&mut self, size: usize) -> FilteredAirBuilder<'_, Self>;0 *)
  Definition Run_when_transition_window
      (Self : Set) `{Link Self}
      (types : AssociatedTypes.t) `{AssociatedTypes.AreLinks types} :
      Set :=
    TraitMethod.C (trait Self) "when_transition_window" (fun method =>
      forall (self : Ref.t Pointer.Kind.MutRef Self) (size : Usize.t),
      Run.Trait method [] [] [ φ self; φ size ]
        (FilteredAirBuilder.t Self types.(AssociatedTypes.Expr))
    ).

  (* fn assert_zero<I: Into<Self::Expr>>(&mut self, x: I); *)
  Definition Run_assert_zero
      (Self : Set) `{Link Self}
      (types : AssociatedTypes.t) `{AssociatedTypes.AreLinks types} :
      Set :=
    TraitMethod.C (trait Self) "assert_zero" (fun method =>
      forall
        (I : Set) `(Link I)
        (run_Into_for_I : Into.Run I types.(AssociatedTypes.Expr))
        (self : Ref.t Pointer.Kind.Ref Self)
        (x : I),
      Run.Trait method [] [Φ I] [ φ self; φ x ] unit
    ).

  (* fn assert_zeros<const N: usize, I: Into<Self::Expr>>(&mut self, array: [I; N]); *)
  Definition Run_assert_zeros
      (Self : Set) `{Link Self}
      (types : AssociatedTypes.t) `{AssociatedTypes.AreLinks types} :
      Set :=
    TraitMethod.C (trait Self) "assert_zeros" (fun method =>
      forall
        (N : Usize.t)
        (I : Set) `(Link I)
        (run_Into_for_I : Into.Run I types.(AssociatedTypes.Expr))
        (self : Ref.t Pointer.Kind.MutRef Self)
        (array : array.t I N),
      Run.Trait method [φ N] [Φ I] [ φ self; φ array ] unit
    ).

  (* fn assert_bools<const N: usize, I: Into<Self::Expr>>(&mut self, array: [I; N]); *)
  Definition Run_assert_bools
      (Self : Set) `{Link Self}
      (types : AssociatedTypes.t) `{AssociatedTypes.AreLinks types} :
      Set :=
    TraitMethod.C (trait Self) "assert_bools" (fun method =>
      forall
        (N : Usize.t)
        (I : Set) `(Link I)
        (run_Into_for_I : Into.Run I types.(AssociatedTypes.Expr))
        (self : Ref.t Pointer.Kind.MutRef Self)
        (array : array.t I N),
      Run.Trait method [φ N] [Φ I] [ φ self; φ array ] unit
    ).

  (* fn assert_one<I: Into<Self::Expr>>(&mut self, x: I); *)
  Definition Run_assert_one
      (Self : Set) `{Link Self}
      (types : AssociatedTypes.t) `{AssociatedTypes.AreLinks types} :
      Set :=
    TraitMethod.C (trait Self) "assert_one" (fun method =>
      forall
        (I : Set) `(Link I)
        (run_Into_for_I : Into.Run I types.(AssociatedTypes.Expr))
        (self : Ref.t Pointer.Kind.MutRef Self)
        (x : I),
      Run.Trait method [] [Φ I] [ φ self; φ x ] unit
    ).

  (* fn assert_eq<I1: Into<Self::Expr>, I2: Into<Self::Expr>>(&mut self, x: I1, y: I2); *)
  Definition Run_assert_eq
      (Self : Set) `{Link Self}
      (types : AssociatedTypes.t) `{AssociatedTypes.AreLinks types} :
      Set :=
    TraitMethod.C (trait Self) "assert_eq" (fun method =>
      forall
        (I1 I2 : Set) `(Link I1) `(Link I2)
        (run_Into_for_I1 : Into.Run I1 types.(AssociatedTypes.Expr))
        (run_Into_for_I2 : Into.Run I2 types.(AssociatedTypes.Expr))
        (self : Ref.t Pointer.Kind.MutRef Self)
        (x y : I1),
      Run.Trait method [] [Φ I1; Φ I2] [ φ self; φ x; φ y ] unit
    ).

  (* fn assert_bool<I: Into<Self::Expr>>(&mut self, x: I); *)
  Definition Run_assert_bool
      (Self : Set) `{Link Self}
      (types : AssociatedTypes.t) `{AssociatedTypes.AreLinks types} :
      Set :=
    TraitMethod.C (trait Self) "assert_bool" (fun method =>
      forall
        (I : Set) `(Link I)
        (run_Into_for_I : Into.Run I types.(AssociatedTypes.Expr))
        (self : Ref.t Pointer.Kind.MutRef Self)
        (x : I),
      Run.Trait method [] [Φ I] [ φ self; φ x ] unit
    ).

  Class Run
      (Self : Set) `{Link Self}
      (types : AssociatedTypes.t) `{AssociatedTypes.AreLinks types} :
      Set := {
    F_IsAssociated :
      IsTraitAssociatedType
        "p3_air::air::AirBuilder" [] [] (Φ Self)
        "F" (Φ types.(AssociatedTypes.F));
    run_Field_for_F : Field.Run types.(AssociatedTypes.F);
    Expr_IsAssociated :
      IsTraitAssociatedType
        "p3_air::air::AirBuilder" [] [] (Φ Self)
        "Expr" (Φ types.(AssociatedTypes.Expr));
    run_Algebra_for_Expr :
      Algebra.Run types.(AssociatedTypes.Expr) types.(AssociatedTypes.F);
    run_Algebra_for_Var :
      Algebra.Run types.(AssociatedTypes.Var) types.(AssociatedTypes.F);
    Var_IsAssociated :
      IsTraitAssociatedType
        "p3_air::air::AirBuilder" [] [] (Φ Self)
        "Var" (Φ types.(AssociatedTypes.Var));
    run_Into_for_Var :
      Into.Run types.(AssociatedTypes.Var) types.(AssociatedTypes.Expr);
    run_Add_F_for_Var :
      Add.Run types.(AssociatedTypes.Var) types.(AssociatedTypes.F) types.(AssociatedTypes.Expr);
    run_Add_Var_for_Expr :
      Add.Run types.(AssociatedTypes.Expr) types.(AssociatedTypes.Var) types.(AssociatedTypes.Expr);
    run_Add_Expr_for_Expr :
      Add.Run types.(AssociatedTypes.Expr) types.(AssociatedTypes.Expr) types.(AssociatedTypes.Expr);
    run_Sub_F_for_Var :
      Sub.Run types.(AssociatedTypes.Var) types.(AssociatedTypes.F) types.(AssociatedTypes.Expr);
    run_Sub_Var_for_Expr :
      Sub.Run types.(AssociatedTypes.Expr) types.(AssociatedTypes.Var) types.(AssociatedTypes.Expr);
    run_Sub_Expr_for_Expr :
      Sub.Run types.(AssociatedTypes.Expr) types.(AssociatedTypes.Expr) types.(AssociatedTypes.Expr);
    run_Mul_F_for_Var :
      Mul.Run types.(AssociatedTypes.Var) types.(AssociatedTypes.F) types.(AssociatedTypes.Expr);
    run_Mul_Var_for_Expr :
      Mul.Run types.(AssociatedTypes.Expr) types.(AssociatedTypes.Var) types.(AssociatedTypes.Expr);
    run_Mul_Expr_for_Expr :
      Mul.Run types.(AssociatedTypes.Expr) types.(AssociatedTypes.Expr) types.(AssociatedTypes.Expr);
    M_IsAssociated :
      IsTraitAssociatedType
        "p3_air::air::AirBuilder" [] [] (Φ Self)
        "M" (Φ types.(AssociatedTypes.M));
    run_Matrix_for_M :
      Matrix.Run types.(AssociatedTypes.M) types.(AssociatedTypes.Var) types.(AssociatedTypes.M_types);
    main : Run_main Self types;
    is_first_row : Run_is_first_row Self types;
    is_last_row : Run_is_last_row Self types;
    is_transition : Run_is_transition Self types;
    is_transition_window : Run_is_transition_window Self types;
    when : Run_when Self types;
    when_ne : Run_when_ne Self types;
    when_first_row : Run_when_first_row Self types;
    when_last_row : Run_when_last_row Self types;
    when_transition : Run_when_transition Self types;
    when_transition_window : Run_when_transition_window Self types;
    assert_zero : Run_assert_zero Self types;
    assert_zeros : Run_assert_zeros Self types;
    assert_bools : Run_assert_bools Self types;
    assert_one : Run_assert_one Self types;
    assert_eq : Run_assert_eq Self types;
    assert_bool : Run_assert_bool Self types;
  }.
End AirBuilder.

(** We make this definition here as we require the definition of the trait first to be able to
    uniquely infer the [Expr] type. *)
Definition FilteredAirBuilder_of_ty (AB' : Ty.t)
    types `{AirBuilder.AssociatedTypes.AreLinks types}
    (H_AB' : OfTy.t AB') :
  AirBuilder.Run (OfTy.get_Set H_AB') types ->
  OfTy.t (Ty.apply (Ty.path "p3_air::air::FilteredAirBuilder") [] [AB']).
Proof.
  intros.
  destruct H_AB' as [AB].
  eapply OfTy.Make with (A := FilteredAirBuilder.t AB types.(AirBuilder.AssociatedTypes.Expr)).
  cbn.
  now subst.
Defined.
Smpl Add unshelve eapply FilteredAirBuilder_of_ty : of_ty.

(* impl<AB: AirBuilder> AirBuilder for FilteredAirBuilder<'_, AB> *)
Module Impl_AirBuilder_for_FilteredAirBuilder.
  Definition Self (AB : Set) `{Link AB} (types : AirBuilder.AssociatedTypes.t) : Set :=
    FilteredAirBuilder.t AB types.(AirBuilder.AssociatedTypes.Expr).

  Definition types (types : AirBuilder.AssociatedTypes.t) : AirBuilder.AssociatedTypes.t :=
    types.

  Instance run
      (AB : Set) `{Link AB}
      (types : AirBuilder.AssociatedTypes.t) `{AirBuilder.AssociatedTypes.AreLinks types} :
      AirBuilder.Run (Self AB types) types.
  Admitted.
End Impl_AirBuilder_for_FilteredAirBuilder.
Export Impl_AirBuilder_for_FilteredAirBuilder.

(* 
pub trait Air<AB: AirBuilder> : BaseAir<AB::F> {
    fn eval(&self, builder: &mut AB);
}
*)
Module Air.
  Module AssociatedTypes.
    Record t : Type := {
      AB : Set;
    }.

    Class AreLinks (types : t) : Set := {
      H_AB : Link types.(AB);
    }.

    Global Instance IsLinkAB (types : t) (H : AreLinks types) : Link types.(AB) :=
      H.(H_AB _).
  End AssociatedTypes.

  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
  ("p3_air::air::Air", [], [], Φ Self).

  (* fn eval(&self, builder: &mut AB); *)
  Definition Run_eval
    (Self : Set) `{Link Self} 
    (types : AssociatedTypes.t) `{AssociatedTypes.AreLinks types} 
    (* TODO: check if this parameter is correct *)
    (builder : Ref.t Pointer.Kind.MutRef types.(AssociatedTypes.AB)) :
    Set :=
      TraitMethod.C (trait Self) "eval" (fun method =>
        forall (self : Ref.t Pointer.Kind.Ref Self) (builder : Ref.t Pointer.Kind.MutRef types.(AssociatedTypes.AB)),
        Run.Trait method [] [] [ φ self ] Usize.t
  ).

  Class Run (Self : Set) `{Link Self} 
    (types : AssociatedTypes.t) `{AssociatedTypes.AreLinks types} : Set := {
    AB_IsAssociated :
      IsTraitAssociatedType
        "p3_air::air::AirBuilder" [] [] (Φ Self)
        "AB" (Φ types.(AssociatedTypes.AB));
    run_AirBuilder_for_AB : AirBuilder.Run types.(AssociatedTypes.AB);
    (* 
    run_Mul_Var_for_Expr :
      Mul.Run types.(AssociatedTypes.Expr) types.(AssociatedTypes.Var) types.(AssociatedTypes.Expr);
    run_Mul_Expr_for_Expr :
      Mul.Run types.(AssociatedTypes.Expr) types.(AssociatedTypes.Expr) types.(AssociatedTypes.Expr);
    *)
    run_BaseAir_for_Air : BaseAir.Run (???);
    (* eval : Run_width Self types; *)
  }.
End Air.