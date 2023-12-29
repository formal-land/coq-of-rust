Require Import CoqOfRust.lib.lib.

Require CoqOfRust.alloc.vec.
Require CoqOfRust.core.convert.
Require CoqOfRust.core.result.

(* 
pub struct Range<Idx> {
    /// The lower bound of the range (inclusive).
    #[stable(feature = "rust1", since = "1.0.0")]
    pub start: Idx,
    /// The upper bound of the range (exclusive).
    #[stable(feature = "rust1", since = "1.0.0")]
    pub end: Idx,
}
*)
Module range.
  Module Range.
    Record t (Idx : Set) : Set := { 
      start: Idx;
      _end: Idx;
    }.
  End Range.
  Definition Range := Range.t.
End range.

Module arith.
  Module Add.
    Class Trait (Self : Set) {Rhs : Set} : Type := {
      Output : Set;
      Rhs := Rhs;
      add : Self -> Rhs -> M Output;
    }.

    Module Default.
      Definition Rhs (Self : Set) : Set := Self.
    End Default.

    Global Instance Method_add `(Trait) :
      Notations.Dot "add" := {
      Notations.dot := add;
    }.
  End Add.

  Module AddAssign.
    Class Trait (Self : Set) {Rhs : Set} : Set := {
      Rhs := Rhs;
      add_assign : mut_ref Self -> Rhs -> M unit;
    }.

    Module Default.
      Definition Rhs (Self : Set) : Set := Self.
    End Default.

    Global Instance Method_add_assign `(Trait) :
      Notations.Dot "add_assign" := {
      Notations.dot := add_assign;
    }.
  End AddAssign.

  Module Sub.
    Class Trait (Self : Set) {Rhs : Set} : Type := {
      Output : Set;
      Rhs := Rhs;
      sub : Self -> Rhs -> M Output;
    }.

    Module Default.
      Definition Rhs (Self : Set) : Set := Self.
    End Default.

    Global Instance Method_sub `(Trait) :
      Notations.Dot "sub" := {
      Notations.dot := sub;
    }.
  End Sub.

  Module SubAssign.
    Class Trait (Self : Set) {Rhs : Set} : Set := {
      Rhs := Rhs;
      sub_assign : mut_ref Self -> Rhs -> M unit;
    }.

    Module Default.
      Definition Rhs (Self : Set) : Set := Self.
    End Default.

    Global Instance Method_sub_assign `(Trait) :
      Notations.Dot "sub_assign" := {
      Notations.dot := sub_assign;
    }.
  End SubAssign.

  Module Mul.
    Class Trait (Self : Set) {Rhs : Set} : Type := {
      Output : Set;
      Rhs := Rhs;
      mul : Self -> Rhs -> M Output;
    }.

    Module Default.
      Definition Rhs (Self : Set) : Set := Self.
    End Default.

    Global Instance Method_mul `(Trait) :
      Notations.Dot "mul" := {
      Notations.dot := mul;
    }.
  End Mul.

  Module MulAssign.
    Class Trait (Self : Set) {Rhs : Set} : Set := {
      Rhs := Rhs;
      mul_assign : mut_ref Self -> Rhs -> M unit;
    }.

    Module Default.
      Definition Rhs (Self : Set) : Set := Self.
    End Default.

    Global Instance Method_mul_assign `(Trait) :
      Notations.Dot "mul_assign" := {
      Notations.dot := mul_assign;
    }.
  End MulAssign.

  Module Div.
    Class Trait (Self : Set) {Rhs : Set} : Type := {
      Output : Set;
      Rhs := Rhs;
      div : Self -> Rhs -> M Output;
    }.

    Module Default.
      Definition Rhs (Self : Set) : Set := Self.
    End Default.

    Global Instance Method_div `(Trait) :
      Notations.Dot "div" := {
      Notations.dot := div;
    }.
  End Div.

  Module DivAssign.
    Class Trait (Self : Set) {Rhs : Set} : Set := {
      Rhs := Rhs;
      div_assign : mut_ref Self -> Rhs -> M unit;
    }.

    Module Default.
      Definition Rhs (Self : Set) : Set := Self.
    End Default.

    Global Instance Method_div_assign `(Trait) :
      Notations.Dot "div_assign" := {
      Notations.dot := div_assign;
    }.
  End DivAssign.

  Module Rem.
    Class Trait (Self : Set) {Rhs : Set} : Type := {
      Output : Set;
      Rhs := Rhs;
      rem : Self -> Rhs -> M Output;
    }.

    Module Default.
      Definition Rhs (Self : Set) : Set := Self.
    End Default.

    Global Instance Method_rem `(Trait) :
      Notations.Dot "rem" := {
      Notations.dot := rem;
    }.
  End Rem.

  Module RemAssign.
    Class Trait (Self : Set) {Rhs : Set} : Set := {
      Rhs := Rhs;
      rem_assign : mut_ref Self -> Rhs -> M unit;
    }.

    Module Default.
      Definition Rhs (Self : Set) : Set := Self.
    End Default.

    Global Instance Method_rem_assign `(Trait) :
      Notations.Dot "rem_assign" := {
      Notations.dot := rem_assign;
    }.
  End RemAssign.

  Module BitXor.
    Class Trait (Self : Set) {Rhs : Set} : Type := {
      Output : Set;
      Rhs := Rhs;
      bitxor : Self -> Rhs -> M Output;
    }.

    Module Default.
      Definition Rhs (Self : Set) : Set := Self.
    End Default.

    Global Instance Method_bitxor `(Trait) :
      Notations.Dot "bitxor" := {
      Notations.dot := bitxor;
    }.
  End BitXor.

  Module BitXorAssign.
    Class Trait (Self : Set) {Rhs : Set} : Set := {
      Rhs := Rhs;
      bitxor_assign : mut_ref Self -> Rhs -> M unit;
    }.

    Module Default.
      Definition Rhs (Self : Set) : Set := Self.
    End Default.

    Global Instance Method_bitxor_assign `(Trait) :
      Notations.Dot "bitxor_assign" := {
      Notations.dot := bitxor_assign;
    }.
  End BitXorAssign.

  Module BitAnd.
    Class Trait (Self : Set) {Rhs : Set} : Type := {
      Output : Set;
      Rhs := Rhs;
      bitand : Self -> Rhs -> M Output;
    }.

    Module Default.
      Definition Rhs (Self : Set) : Set := Self.
    End Default.

    Global Instance Method_bitand `(Trait) :
      Notations.Dot "bitand" := {
      Notations.dot := bitand;
    }.
  End BitAnd.

  Module BitAndAssign.
    Class Trait (Self : Set) {Rhs : Set} : Set := {
      Rhs := Rhs;
      bitand_assign : mut_ref Self -> Rhs -> M unit;
    }.

    Module Default.
      Definition Rhs (Self : Set) : Set := Self.
    End Default.

    Global Instance Method_bitand_assign `(Trait) :
      Notations.Dot "bitand_assign" := {
      Notations.dot := bitand_assign;
    }.
  End BitAndAssign.

  Module BitOr.
    Class Trait (Self : Set) {Rhs : Set} : Type := {
      Output : Set;
      Rhs := Rhs;
      bitor : Self -> Rhs -> M Output;
    }.

    Module Default.
      Definition Rhs (Self : Set) : Set := Self.
    End Default.

    Global Instance Method_bitor `(Trait) :
      Notations.Dot "bitor" := {
      Notations.dot := bitor;
    }.
  End BitOr.

  Module BitOrAssign.
    Class Trait (Self : Set) {Rhs : Set} : Set := {
      Rhs := Rhs;
      bitor_assign : mut_ref Self -> Rhs -> M unit;
    }.

    Module Default.
      Definition Rhs (Self : Set) : Set := Self.
    End Default.

    Global Instance Method_bitor_assign `(Trait) :
      Notations.Dot "bitor_assign" := {
      Notations.dot := bitor_assign;
    }.
  End BitOrAssign.

  Module Shl.
    Class Trait (Self : Set) {Rhs : Set} : Type := {
      Output : Set;
      Rhs := Rhs;
      shl : Self -> Rhs -> M Output;
    }.

    Module Default.
      Definition Rhs (Self : Set) : Set := Self.
    End Default.

    Global Instance Method_shl `(Trait) :
      Notations.Dot "shl" := {
      Notations.dot := shl;
    }.
  End Shl.

  Module ShlAssign.
    Class Trait (Self : Set) {Rhs : Set} : Set := {
      Rhs := Rhs;
      shl_assign : mut_ref Self -> Rhs -> M unit;
    }.

    Module Default.
      Definition Rhs (Self : Set) : Set := Self.
    End Default.

    Global Instance Method_shl_assign `(Trait) :
      Notations.Dot "shl_assign" := {
      Notations.dot := shl_assign;
    }.
  End ShlAssign.

  Module Shr.
    Class Trait (Self : Set) {Rhs : Set} : Type := {
      Output : Set;
      Rhs := Rhs;
      shr : Self -> Rhs -> M Output;
    }.

    Module Default.
      Definition Rhs (Self : Set) : Set := Self.
    End Default.

    Global Instance Method_shr `(Trait) :
      Notations.Dot "shr" := {
      Notations.dot := shr;
    }.
  End Shr.

  Module ShrAssign.
    Class Trait (Self : Set) {Rhs : Set} : Set := {
      Rhs := Rhs;
      shr_assign : mut_ref Self -> Rhs -> M unit;
    }.

    Module Default.
      Definition Rhs (Self : Set) : Set := Self.
    End Default.

    Global Instance Method_shr_assign `(Trait) :
      Notations.Dot "shr_assign" := {
      Notations.dot := shr_assign;
    }.
  End ShrAssign.

  Module Neg.
    Class Trait (Self : Set) : Type := {
      Output : Set;
      neg : Self -> M Output;
    }.

    Global Instance Method_neg `(Trait) :
      Notations.Dot "neg" := {
      Notations.dot := neg;
    }.
  End Neg.

  Module Not.
    Class Trait (Self : Set) : Type := {
      Output : Set;
      not : M.Val Self -> M (M.Val Output);
    }.

    Global Instance Method_not `(Trait) :
      Notations.Dot "not" := {
      Notations.dot := not;
    }.
  End Not.
End arith.

Module deref.
  Module Deref.
    Class Trait (Self : Set) {Target : Set} : Set := {
      Target := Target;
      deref : ref Self -> M (ref Target);
    }.

    Global Instance Method_deref `(Trait) :
      Notations.Dot "deref" := {
      Notations.dot := deref;
    }.
  End Deref.
End deref.

Module function.
  Module FnOnce.
    Class Trait (Self : Set) {Args : Set} : Type := {
      Output : Set;
      call_once : Self -> Args -> M Output;
    }.
  End FnOnce.

  Module FnMut.
    Class Trait (Self : Set) {Args : Set} : Type := {
      L0 :: FnOnce.Trait Self (Args := Args);
      call_mut : mut_ref Self -> Args -> M FnOnce.Output;
    }.
  End FnMut.
End function.

(* Module Impl_Add_for_i32. Section Impl_Add_for_i32.
  Context `{State.Trait}.

  Definition add (z1 z2 : i32) : M Z := M.pure (Z.add z1 z2).

  Global Instance Method_add : Notations.Dot "add" := {
    Notations.dot := add;
  }.

  Global Instance Add_for_Z :
      arith.Add.Trait Z (Rhs := arith.Add.Default.Rhs Z) := {
    add := add;
  }.
End Impl_Add_for_i32. End Impl_Add_for_i32.

Module Impl_AddAssign_for_Z.
  Context `{State.Trait}.

  Parameter add_assign : forall `{State.Trait}, mut_ref Z -> Z -> M unit.

  Global Instance Method_add_assign `{State.Trait} :
    Notations.Dot "add_assign" := {
    Notations.dot := add_assign;
  }.

  Global Instance AddAssign_for_Z :
    arith.AddAssign.Trait Z (Rhs := Z) := {
    add_assign `{State.Trait} := add_assign;
  }.
End Impl_AddAssign_for_Z.

Module Impl_Sub_for_Z.
  Definition sub `{State.Trait} (z1 z2 : Z) : M Z := M.pure (Z.sub z1 z2).

  Global Instance Method_sub `{State.Trait} : Notations.Dot "sub" := {
    Notations.dot := sub;
  }.

  Global Instance Sub_for_Z : arith.Sub.Trait Z (Rhs := Z) := {
    sub `{State.Trait} := sub;
  }.
End Impl_Sub_for_Z.

Module Impl_SubAssign_for_Z.
  Parameter sub_assign : forall `{State.Trait}, mut_ref Z -> Z -> M unit.

  Global Instance Method_sub_assign `{State.Trait} :
    Notations.Dot "sub_assign" := {
    Notations.dot := sub_assign;
  }.

  Global Instance SubAssign_for_Z :
    arith.SubAssign.Trait Z (Rhs := Z) := {
    sub_assign `{State.Trait} := sub_assign;
  }.
End Impl_SubAssign_for_Z.

Module Impl_Mul_for_Z.
  Definition mul `{State.Trait} (z1 z2 : Z) : M Z := M.pure (Z.mul z1 z2).

  Global Instance Method_mul `{State.Trait} : Notations.Dot "mul" := {
    Notations.dot := mul;
  }.

  Global Instance Mul_for_Z : arith.Mul.Trait Z (Rhs := Z) := {
    mul `{State.Trait} := mul;
  }.
End Impl_Mul_for_Z.

Module Impl_MulAssign_for_Z.
  Parameter mul_assign : forall `{State.Trait}, mut_ref Z -> Z -> M unit.

  Global Instance Method_mul_assign `{State.Trait} :
    Notations.Dot "mul_assign" := {
    Notations.dot := mul_assign;
  }.

  Global Instance MulAssign_for_Z :
    arith.MulAssign.Trait Z (Rhs := Z) := {
    mul_assign `{State.Trait} := mul_assign;
  }.
End Impl_MulAssign_for_Z.

Module Impl_Div_for_Z.
  Definition div `{State.Trait} (z1 z2 : Z) : M Z := M.pure (Z.div z1 z2).

  Global Instance Method_div `{State.Trait} : Notations.Dot "div" := {
    Notations.dot := div;
  }.

  Global Instance Div_for_Z : arith.Div.Trait Z (Rhs := Z) := {
    div `{State.Trait} := div;
  }.
End Impl_Div_for_Z.

Module Impl_DivAssign_for_Z.
  Parameter div_assign : forall `{State.Trait}, mut_ref Z -> Z -> M unit.

  Global Instance Method_div_assign `{State.Trait} :
    Notations.Dot "div_assign" := {
    Notations.dot := div_assign;
  }.

  Global Instance DivAssign_for_Z :
    arith.DivAssign.Trait Z (Rhs := Z) := {
    div_assign `{State.Trait} := div_assign;
  }.
End Impl_DivAssign_for_Z.

Module Impl_Rem_for_Z.
  Definition rem `{State.Trait} (z1 z2 : Z) : M Z := M.pure (Z.rem z1 z2).

  Global Instance Method_rem `{State.Trait} : Notations.Dot "rem" := {
    Notations.dot := rem;
  }.

  Global Instance Rem_for_Z : arith.Rem.Trait Z (Rhs := Z) := {
    rem `{State.Trait} := rem;
  }.
End Impl_Rem_for_Z.

Module Impl_RemAssign_for_Z.
  Parameter rem_assign : forall `{State.Trait}, mut_ref Z -> Z -> M unit.

  Global Instance Method_rem_assign `{State.Trait} :
    Notations.Dot "rem_assign" := {
    Notations.dot := rem_assign;
  }.

  Global Instance RemAssign_for_Z :
    arith.RemAssign.Trait Z (Rhs := Z) := {
    rem_assign `{State.Trait} := rem_assign;
  }.
End Impl_RemAssign_for_Z.

Module Impl_Neg_for_Z.
  Definition neg `{State.Trait} (z : Z) : M Z := M.pure (Z.opp z).

  Global Instance Method_neg `{State.Trait} : Notations.Dot "neg" := {
    Notations.dot := neg;
  }.

  Global Instance Neg_for_Z : arith.Neg.Trait Z := {
    neg `{State.Trait} := neg;
  }.
End Impl_Neg_for_Z. *)

Module Impl_Not_for_bool.
  Definition not (b : M.Val bool) : M (M.Val bool) :=
    let* b := M.read b in
    M.alloc (negb b).

  Global Instance Method_not : Notations.Dot "not" := {
    Notations.dot := not;
  }.

  Global Instance Not_for_bool : arith.Not.Trait bool := {
    not := not;
  }.
End Impl_Not_for_bool.

Module drop.
  (*
  pub trait Drop {
      // Required method
      fn drop(&mut self);
  }
  *)
  Module Drop.
    Class Trait (Self : Set) : Set := {
      drop : mut_ref Self -> M unit;
    }.

    Global Instance Method_drop `(Trait) :
      Notations.Dot "drop" := {
      Notations.dot := drop;
    }.
  End Drop.
End drop.

Module control_flow.
  (*
  pub enum ControlFlow<B, C = ()> {
      Continue(C),
      Break(B),
  }
  *)
  Module ControlFlow.
    Inductive t (B C : Set) : Set :=
    | Continue : C -> t B C
    | Break : B -> t B C.
    Arguments Continue {_ _}.
    Arguments Break {_ _}.
  End ControlFlow.
End control_flow.

Module try_trait.
  (*
  pub trait Try: FromResidual<Self::Residual> {
      type Output;
      type Residual;

      // Required methods
      fn from_output(output: Self::Output) -> Self;
      fn branch(self) -> ControlFlow<Self::Residual, Self::Output>;
  }
  *)
  Module Try.
    Class Trait (Self : Set) : Type := {
      Output : Set;
      Residual : Set;
      from_output : Output -> M Self;
      branch :
        Self ->
        M (control_flow.ControlFlow.t Residual Output);
    }.

    Module Impl.
      Global Instance for_Result (T E : Set) :
          Trait (core.result.Result.t T E) := {
        Output := T;
        Residual := core.result.Result.t core.convert.Infallible.t E;
        from_output output :=
          M.pure (core.result.Result.Ok output);
        branch self :=
          match self with
          | core.result.Result.Ok v =>
            M.pure (control_flow.ControlFlow.Continue v)
          | core.result.Result.Err e =>
            let result := core.result.Result.Err e in
            M.pure (control_flow.ControlFlow.Break result)
          end;
      }.
    End Impl.
  End Try.

  (*
  pub trait FromResidual<R = <Self as Try>::Residual> {
      // Required method
      fn from_residual(residual: R) -> Self;
  }
  *)
  Module FromResidual.
    Class Trait (Self : Set) {R : Set} : Type := {
      from_residual : R -> M Self;
    }.

    Module Impl.
      Global Instance for_Result (T E F : Set)
          {H0 : core.convert.From.Trait F (T := E)} :
          Trait (core.result.Result.t T F)
            (R := core.result.Result.t core.convert.Infallible.t E) := {
        from_residual residual :=
          axiom "from_residual";
      }.

      (* Special case for when the From is the identity, to help the type-checker. *)
      Global Instance for_Result_id (T E : Set) :
          Trait (core.result.Result.t T E)
            (R := core.result.Result.t core.convert.Infallible.t E) := {
        from_residual residual :=
          match residual with
          | result.Result.Ok v => match v with end
          | result.Result.Err e =>
            M.pure (core.result.Result.Err e)
          end;
      }.
    End Impl.
  End FromResidual.
End try_trait.

Module index.
  (*
  pub trait Index<Idx: ?Sized> {
      type Output: ?Sized;

      // Required method
      fn index(&self, index: Idx) -> &Self::Output;
  }
  *)
  Module Index.
    Class Trait (Self : Set) {Idx : Set} : Type := {
      Output : Set;
      index : ref Self -> Idx -> M (ref Output);
    }.

    Module Impl.
      Global Instance for_vec (T : Set) :
          Trait (vec.Vec.t T vec.Vec.Default.A) (Idx := usize.t) := {
        Output := T;
        index self index :=
          axiom "index";
      }.
    End Impl.
  End Index.

  (*
  pub trait IndexMut<Idx: ?Sized>: Index<Idx> {
      // Required method
      fn index_mut(&mut self, index: Idx) -> &mut Self::Output;
  }
  *)
  Module IndexMut.
    Class Trait (Self : Set) {Idx : Set} : Type := {
      L0 :: Index.Trait Self (Idx := Idx);
      index_mut : mut_ref Self -> Idx -> M (mut_ref L0.(Index.Output));
    }.

    Module Impl.
      Global Instance for_vec (T : Set) :
          Trait (vec.Vec.t T vec.Vec.Default.A) (Idx := usize.t) := {
        index_mut self index :=
          axiom "index_mut";
      }.
    End Impl.
  End IndexMut.
End index.
