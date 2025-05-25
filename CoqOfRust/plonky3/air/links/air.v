Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.links.array.
Require Import core.convert.links.mod.
Require Import core.ops.links.arith.
Require Import plonky3.air.air.
Require Import plonky3.field.links.field.

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

    fn main(&self) -> Self::M;
    fn is_first_row(&self) -> Self::Expr;
    fn is_last_row(&self) -> Self::Expr;
    fn is_transition(&self) -> Self::Expr;
    fn is_transition_window(&self, size: usize) -> Self::Expr;
    fn when<I: Into<Self::Expr>>(&mut self, condition: I) -> FilteredAirBuilder<'_, Self>;
    fn when_ne<I1: Into<Self::Expr>, I2: Into<Self::Expr>>(
        &mut self,
        x: I1,
        y: I2,
    ) -> FilteredAirBuilder<'_, Self>;
    fn when_first_row(&mut self) -> FilteredAirBuilder<'_, Self>;
    fn when_last_row(&mut self) -> FilteredAirBuilder<'_, Self>;
    fn when_transition(&mut self) -> FilteredAirBuilder<'_, Self>;
    fn when_transition_window(&mut self, size: usize) -> FilteredAirBuilder<'_, Self>;
    fn assert_zero<I: Into<Self::Expr>>(&mut self, x: I);
    fn assert_zeros<const N: usize, I: Into<Self::Expr>>(&mut self, array: [I; N]);
    fn assert_bools<const N: usize, I: Into<Self::Expr>>(&mut self, array: [I; N]);
    fn assert_one<I: Into<Self::Expr>>(&mut self, x: I);
    fn assert_eq<I1: Into<Self::Expr>, I2: Into<Self::Expr>>(&mut self, x: I1, y: I2);
    fn assert_bool<I: Into<Self::Expr>>(&mut self, x: I);
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
    }.

    Class AreLinks (types : t) : Set := {
      H_F : Link types.(F);
      H_Expr : Link types.(Expr);
      H_Var : Link types.(Var);
      H_M : Link types.(M);
    }.

    Global Instance IsLinkF (types : t) (H : AreLinks types) : Link types.(F) :=
      H.(H_F _).
    Global Instance IsLinkExpr (types : t) (H : AreLinks types) : Link types.(Expr) :=
      H.(H_Expr _).
    Global Instance IsLinkVar (types : t) (H : AreLinks types) : Link types.(Var) :=
      H.(H_Var _).
    Global Instance IsLinkM (types : t) (H : AreLinks types) : Link types.(M) :=
      H.(H_M _).
  End AssociatedTypes.

  Definition Run_main
      (Self : Set) `{Link Self}
      (types : AssociatedTypes.t) `{AssociatedTypes.AreLinks types} :
      Set :=
    TraitMethod.C (trait Self) "main" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] types.(AssociatedTypes.M)
    ).

  Definition Run_is_first_row
      (Self : Set) `{Link Self}
      (types : AssociatedTypes.t) `{AssociatedTypes.AreLinks types} :
      Set :=
    TraitMethod.C (trait Self) "is_first_row" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] types.(AssociatedTypes.Expr)
    ).

  Definition Run_is_last_row
      (Self : Set) `{Link Self}
      (types : AssociatedTypes.t) `{AssociatedTypes.AreLinks types} :
      Set :=
    TraitMethod.C (trait Self) "is_last_row" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] types.(AssociatedTypes.Expr)
    ).

  Definition Run_is_transition
      (Self : Set) `{Link Self}
      (types : AssociatedTypes.t) `{AssociatedTypes.AreLinks types} :
      Set :=
    TraitMethod.C (trait Self) "is_transition" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] types.(AssociatedTypes.Expr)
    ).

  Definition Run_is_transition_window
      (Self : Set) `{Link Self}
      (types : AssociatedTypes.t) `{AssociatedTypes.AreLinks types} :
      Set :=
    TraitMethod.C (trait Self) "is_transition_window" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self) (size : Usize.t),
      Run.Trait method [] [] [ φ self; φ size ] types.(AssociatedTypes.Expr)
    ).

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

  Definition Run_when_first_row
      (Self : Set) `{Link Self}
      (types : AssociatedTypes.t) `{AssociatedTypes.AreLinks types} :
      Set :=
    TraitMethod.C (trait Self) "when_first_row" (fun method =>
      forall (self : Ref.t Pointer.Kind.MutRef Self),
      Run.Trait method [] [] [ φ self ] (FilteredAirBuilder.t Self types.(AssociatedTypes.Expr))
    ).

  Definition Run_when_last_row
      (Self : Set) `{Link Self}
      (types : AssociatedTypes.t) `{AssociatedTypes.AreLinks types} :
      Set :=
    TraitMethod.C (trait Self) "when_last_row" (fun method =>
      forall (self : Ref.t Pointer.Kind.MutRef Self),
      Run.Trait method [] [] [ φ self ] (FilteredAirBuilder.t Self types.(AssociatedTypes.Expr))
    ).

  Definition Run_when_transition
      (Self : Set) `{Link Self}
      (types : AssociatedTypes.t) `{AssociatedTypes.AreLinks types} :
      Set :=
    TraitMethod.C (trait Self) "when_transition" (fun method =>
      forall (self : Ref.t Pointer.Kind.MutRef Self),
      Run.Trait method [] [] [ φ self ] (FilteredAirBuilder.t Self types.(AssociatedTypes.Expr))
    ).

  Definition Run_when_transition_window
      (Self : Set) `{Link Self}
      (types : AssociatedTypes.t) `{AssociatedTypes.AreLinks types} :
      Set :=
    TraitMethod.C (trait Self) "when_transition_window" (fun method =>
      forall (self : Ref.t Pointer.Kind.MutRef Self) (size : Usize.t),
      Run.Trait method [] [] [ φ self; φ size ]
        (FilteredAirBuilder.t Self types.(AssociatedTypes.Expr))
    ).

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
